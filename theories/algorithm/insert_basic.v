(** The Yjs insert/integrate algorithm.

    Port of [LeanYjs/Algorithm/Insert/Basic.lean]. Faithful translation: the
    document is a [list], positions are [Z] indices (with [-1] for [First] and
    [length] for [Last] as in the Lean [Array] version), and partiality is
    expressed with [option] (Lean's single-constructor [Except IntegrateError]
    collapses to [None]/[Some]). The mutable [for]/[break] loop of
    [findIntegratedIndex] becomes the structural recursion [fii_loop]. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item.
From yjs.algorithm Require Import basic.

Section insert.
Context {A : Type} `{EqDecision A}.

Record IntegrateInput := MkIntegrateInput {
  in_originId : option YjsId;
  in_rightOriginId : option YjsId;
  in_content : A;
  in_id : YjsId;
}.

(** Find the item / its index by id (resp. by structure). *)
Definition find_by_id (id : YjsId) (arr : list (YjsItem A)) : option (YjsItem A) :=
  snd <$> list_find (fun item => item_id item = id) arr.

Definition find_item_idx (item : YjsItem A) (arr : list (YjsItem A)) : option nat :=
  fst <$> list_find (fun i => i = item) arr.

(** Build the new item from the input by resolving origin / right-origin. *)
Definition toItem (input : IntegrateInput) (arr : list (YjsItem A)) : option (YjsItem A) :=
  originPtr ← (match in_originId input with
               | Some id => itemPtr <$> find_by_id id arr
               | None => Some First
               end);
  rightOriginPtr ← (match in_rightOriginId input with
                    | Some id => itemPtr <$> find_by_id id arr
                    | None => Some Last
                    end);
  Some (Item originPtr rightOriginPtr (in_id input) (in_content input)).

(** Index of a pointer: [-1] for [First], [length] for [Last]. *)
Definition findPtrIdx (p : YjsPtr A) (arr : list (YjsItem A)) : option Z :=
  match p with
  | itemPtr item => (fun idx => Z.of_nat idx) <$> find_item_idx item arr
  | First => Some (-1)%Z
  | Last => Some (Z.of_nat (length arr))
  end.

Definition getElemExcept (arr : list (YjsItem A)) (idx : nat) : option (YjsItem A) :=
  arr !! idx.

(** The integration scan (Lean's mutable [for ... break] loop), as a recursion
    over a fuel [count] with the loop offset and the [scanning]/[destIdx]
    accumulators threaded through; [break] returns the current [destIdx]. *)
Fixpoint fii_loop (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (arr : list (YjsItem A)) (scanning : bool) (destIdx : Z) : option Z :=
  match count with
  | 0 => Some destIdx
  | S count' =>
    let i := Z.to_nat (leftIdx + Z.of_nat offset) in
    other ← getElemExcept arr i;
    oLeftIdx ← findPtrIdx (origin other) arr;
    oRightIdx ← findPtrIdx (rightOrigin other) arr;
    if decide (oLeftIdx < leftIdx)%Z then Some destIdx
    else if decide (oLeftIdx = leftIdx)%Z then
      if decide (clientId (item_id other) < cid)%nat then
        fii_loop count' (S offset) leftIdx rightIdx cid arr false (Z.of_nat (i + 1))
      else if decide (oRightIdx = rightIdx)%Z then Some destIdx
      else fii_loop count' (S offset) leftIdx rightIdx cid arr true destIdx
    else
      fii_loop count' (S offset) leftIdx rightIdx cid arr scanning
        (if scanning then destIdx else Z.of_nat (i + 1))
  end.

Definition findIntegratedIndex (leftIdx rightIdx : Z) (newItem : IntegrateInput)
    (arr : list (YjsItem A)) : option nat :=
  d ← fii_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
       (clientId (in_id newItem)) arr false (leftIdx + 1);
  Some (Z.to_nat d).

Definition findLeftIdx (originId : option YjsId) (arr : list (YjsItem A)) : option Z :=
  match originId with
  | Some id => (fun idx => Z.of_nat idx) <$> (fst <$> list_find (fun item => item_id item = id) arr)
  | None => Some (-1)%Z
  end.

Definition findRightIdx (rightOriginId : option YjsId) (arr : list (YjsItem A)) : option Z :=
  match rightOriginId with
  | Some id => (fun idx => Z.of_nat idx) <$> (fst <$> list_find (fun item => item_id item = id) arr)
  | None => Some (Z.of_nat (length arr))
  end.

Definition getPtrExcept (arr : list (YjsItem A)) (idx : Z) : option (YjsPtr A) :=
  if decide (idx = -1)%Z then Some First
  else if decide (idx = Z.of_nat (length arr))%Z then Some Last
  else itemPtr <$> (arr !! Z.to_nat idx).

Definition mkItemByIndex (leftIdx rightIdx : Z) (input : IntegrateInput)
    (arr : list (YjsItem A)) : option (YjsItem A) :=
  l ← getPtrExcept arr leftIdx;
  r ← getPtrExcept arr rightIdx;
  Some (Item l r (in_id input) (in_content input)).

(** Insert [x] at position [n], if in bounds (else leave [l] unchanged). *)
Definition insertIdxIfInBounds (n : nat) (x : YjsItem A) (l : list (YjsItem A)) : list (YjsItem A) :=
  if decide (n <= length l)%nat then take n l ++ x :: drop n l else l.

Definition integrate (newItem : IntegrateInput) (arr : list (YjsItem A)) :
    option (list (YjsItem A)) :=
  leftIdx ← findLeftIdx (in_originId newItem) arr;
  rightIdx ← findRightIdx (in_rightOriginId newItem) arr;
  destIdx ← findIntegratedIndex leftIdx rightIdx newItem arr;
  item ← mkItemByIndex leftIdx rightIdx newItem arr;
  Some (insertIdxIfInBounds destIdx item arr).

(** A new id is clock-safe when, for every existing item of the same client, the
    new clock is strictly larger. *)
Definition isClockSafe (id : YjsId) (arr : list (YjsItem A)) : bool :=
  forallb (fun item =>
    implb (bool_decide (clientId (item_id item) = clientId id))
          (bool_decide (clock (item_id item) < clock id)%nat)) arr.

Definition integrateSafe (newItem : IntegrateInput) (arr : list (YjsItem A)) :
    option (list (YjsItem A)) :=
  if isClockSafe (in_id newItem) arr then integrate newItem arr else None.

Definition YjsState_insert (s : YjsState A) (input : IntegrateInput) : option (YjsState A) :=
  newArr ← integrateSafe input (st_items s);
  Some (MkYjsState newArr (st_deleted s)).

End insert.

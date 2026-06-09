(** The indirect (by-id) integrate algorithm. Port of
    [LeanYjs/Indirect/Algorithm/Insert/Basic.lean]. Mirrors the direct
    [integrate] (insert_basic.v) verbatim, except origin / right-origin are
    resolved by id ([findRefIdx]) rather than by structure ([findPtrIdx]). The
    loop is the same fuel-recursion [ifii_loop]. *)
From stdpp Require Import base numbers list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item.
From yjs.algorithm Require Import basic insert_basic.
From yjs.indirect Require Import item basic.

Section indirect_insert.
Context {A : Type} `{EqDA : EqDecision A}.

(** Resolve a reference to an index ([-1] = First, [length] = Last). *)
Definition findRefIdx (p : YjsRef) (arr : list (IYjsItem A)) : option Z :=
  match p with
  | RefId id => (fun idx => Z.of_nat idx) <$> (fst <$> list_find (fun item => iid item = id) arr)
  | RefFirst => Some (-1)%Z
  | RefLast => Some (Z.of_nat (length arr))
  end.

Definition igetElemExcept (arr : list (IYjsItem A)) (idx : nat) : option (IYjsItem A) :=
  arr !! idx.

(** The scanning loop, identical in shape to the direct [fii_loop]. *)
Fixpoint ifii_loop (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (arr : list (IYjsItem A)) (scanning : bool) (destIdx : Z) : option Z :=
  match count with
  | 0 => Some destIdx
  | S count' =>
    let i := Z.to_nat (leftIdx + Z.of_nat offset) in
    other ← igetElemExcept arr i;
    oLeftIdx ← findRefIdx (iorigin other) arr;
    oRightIdx ← findRefIdx (irightOrigin other) arr;
    if decide (oLeftIdx < leftIdx)%Z then Some destIdx
    else if decide (oLeftIdx = leftIdx)%Z then
      if decide (clientId (iid other) < cid)%nat then
        ifii_loop count' (S offset) leftIdx rightIdx cid arr false (Z.of_nat (i + 1))
      else if decide (oRightIdx = rightIdx)%Z then Some destIdx
      else ifii_loop count' (S offset) leftIdx rightIdx cid arr true destIdx
    else
      ifii_loop count' (S offset) leftIdx rightIdx cid arr scanning
        (if scanning then destIdx else Z.of_nat (i + 1))
  end.

Definition ifindIntegratedIndex (leftIdx rightIdx : Z) (newItem : IntegrateInput (A := A))
    (arr : list (IYjsItem A)) : option nat :=
  d ← ifii_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
       (clientId (in_id newItem)) arr false (leftIdx + 1);
  Some (Z.to_nat d).

Definition ifindLeftIdx (originId : option YjsId) (arr : list (IYjsItem A)) : option Z :=
  match originId with
  | Some id => (fun idx => Z.of_nat idx) <$> (fst <$> list_find (fun item => iid item = id) arr)
  | None => Some (-1)%Z
  end.

Definition ifindRightIdx (rightOriginId : option YjsId) (arr : list (IYjsItem A)) : option Z :=
  match rightOriginId with
  | Some id => (fun idx => Z.of_nat idx) <$> (fst <$> list_find (fun item => iid item = id) arr)
  | None => Some (Z.of_nat (length arr))
  end.

Definition imkItem (input : IntegrateInput (A := A)) : IYjsItem A :=
  MkIYjsItem (ofOriginId (in_originId input)) (ofRightOriginId (in_rightOriginId input))
             (in_id input) (in_content input).

Definition iinsertIdxIfInBounds (n : nat) (x : IYjsItem A) (l : list (IYjsItem A)) : list (IYjsItem A) :=
  if decide (n <= length l)%nat then take n l ++ x :: drop n l else l.

Definition iintegrate (newItem : IntegrateInput (A := A)) (arr : list (IYjsItem A)) :
    option (list (IYjsItem A)) :=
  leftIdx ← ifindLeftIdx (in_originId newItem) arr;
  rightIdx ← ifindRightIdx (in_rightOriginId newItem) arr;
  destIdx ← ifindIntegratedIndex leftIdx rightIdx newItem arr;
  Some (iinsertIdxIfInBounds destIdx (imkItem newItem) arr).

Definition iisClockSafe (id : YjsId) (arr : list (IYjsItem A)) : bool :=
  forallb (fun item =>
    implb (bool_decide (clientId (iid item) = clientId id))
          (bool_decide (clock (iid item) < clock id)%nat)) arr.

Definition iintegrateSafe (newItem : IntegrateInput (A := A)) (arr : list (IYjsItem A)) :
    option (list (IYjsItem A)) :=
  if iisClockSafe (in_id newItem) arr then iintegrate newItem arr else None.

Definition IYjsState_insert (s : IYjsState A) (input : IntegrateInput (A := A)) : option (IYjsState A) :=
  newArr ← iintegrateSafe input (ist_items s);
  Some (MkIYjsState newArr (ist_deleted s)).

End indirect_insert.

(** [getPtrExcept] recovers the pointer at a [findLeftIdx]/[findRightIdx]
    position, and [findPtrIdx] shifts predictably under [insertIdxIfInBounds].
    Port of [findLeftIdx_getElemExcept], [findRightIdx_getElemExcept],
    [uniqueId_insertIdxIfInBounds_id_neq], [findPtrIdx_insert_some] from
    [LeanYjs/Algorithm/Invariant/YjsArray.lean]. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic insert_basic insert_lemmas
  invariant_yjsarray invariant_yjsarray_idx toitem_lemmas.

(** [list_find] skips a non-matching head. *)
Lemma list_find_cons_ne {X} (P : X -> Prop) `{!∀ x, Decision (P x)} (y : X) (l : list X) :
  ¬ P y -> list_find P (y :: l) = prod_map S id <$> list_find P l.
Proof. move=> Hy /=; rewrite decide_False //. Qed.

(** Inserting a non-matching element at position [i] shifts the first match
    index by one exactly when [i] is at or before it. *)
Lemma list_find_insert_shift {X} (P : X -> Prop) `{!∀ x, Decision (P x)}
    (l : list X) (i k : nat) (x y : X) :
  ¬ P y -> i <= length l ->
  list_find P l = Some (k, x) ->
  list_find P (take i l ++ y :: drop i l) =
    Some ((if decide (i <= k) then S k else k), x).
Proof.
  move=> Hy Hi Hl.
  have Htl : length (take i l) = i by rewrite length_take_le.
  have Hl' : list_find P (take i l ++ drop i l) = Some (k, x) by rewrite take_drop.
  apply list_find_app_Some in Hl'.
  destruct Hl' as [Hl1 | (Hge & Hnone & Hl2)].
  - have Hki : k < i.
    { apply list_find_Some in Hl1; destruct Hl1 as (Hlk & _ & _).
      have Hb := lookup_lt_Some _ _ _ Hlk; rewrite Htl in Hb; lia. }
    rewrite decide_False; [|lia].
    by apply list_find_app_l.
  - rewrite decide_True; [|lia].
    rewrite (list_find_app_r P (take i l) (y :: drop i l) Hnone)
            (list_find_cons_ne P y (drop i l) Hy) Hl2 /= !Htl.
    have -> : (k - i + i = k)%nat by lia.
    done.
Qed.

Section insert.
Context {A : Type} `{EqDA : EqDecision A}.

Lemma findLeftIdx_getElemExcept (arr : list (YjsItem A)) (input : IntegrateInput (A := A)) (leftIdx : Z) :
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  exists ptr, getPtrExcept arr leftIdx = Some ptr /\ isLeftIdPtr arr (in_originId input) ptr.
Proof using A EqDA.
  rewrite /findLeftIdx /isLeftIdPtr; destruct (in_originId input) as [id|].
  - move=> /fmap_Some [k [Hk ->]].
    move: Hk => /fmap_Some [[k' item] [Hfind Hkeq]]; simpl in Hkeq; subst k.
    have Hfacts := Hfind; apply list_find_Some in Hfacts; destruct Hfacts as (Hlk & _ & _).
    have Hlt : k' < length arr := lookup_lt_Some _ _ _ Hlk.
    exists (itemPtr item); split.
    + rewrite /getPtrExcept.
      destruct (decide (Z.of_nat k' = -1)%Z) as [?|_]; [lia|].
      destruct (decide (Z.of_nat k' = Z.of_nat (length arr))%Z) as [?|_]; [lia|].
      by rewrite Nat2Z.id Hlk /=.
    + exists item; split; [done|].
      rewrite /find_by_id; apply/fmap_Some; exists (k', item); split; [exact Hfind|done].
  - move=> [= <-]; exists First; split; [|done].
    rewrite /getPtrExcept.
    destruct (decide ((-1)%Z = -1)%Z) as [_|?]; [done|lia].
Qed.

Lemma findRightIdx_getElemExcept (arr : list (YjsItem A)) (input : IntegrateInput (A := A)) (rightIdx : Z) :
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  exists ptr, getPtrExcept arr rightIdx = Some ptr /\ isRightIdPtr arr (in_rightOriginId input) ptr.
Proof using A EqDA.
  rewrite /findRightIdx /isRightIdPtr; destruct (in_rightOriginId input) as [id|].
  - move=> /fmap_Some [k [Hk ->]].
    move: Hk => /fmap_Some [[k' item] [Hfind Hkeq]]; simpl in Hkeq; subst k.
    have Hfacts := Hfind; apply list_find_Some in Hfacts; destruct Hfacts as (Hlk & _ & _).
    have Hlt : k' < length arr := lookup_lt_Some _ _ _ Hlk.
    exists (itemPtr item); split.
    + rewrite /getPtrExcept.
      destruct (decide (Z.of_nat k' = -1)%Z) as [?|_]; [lia|].
      destruct (decide (Z.of_nat k' = Z.of_nat (length arr))%Z) as [?|_]; [lia|].
      by rewrite Nat2Z.id Hlk /=.
    + exists item; split; [done|].
      rewrite /find_by_id; apply/fmap_Some; exists (k', item); split; [exact Hfind|done].
  - move=> [= <-]; exists Last; split; [|done].
    rewrite /getPtrExcept.
    destruct (decide (Z.of_nat (length arr) = -1)%Z) as [?|_]; [lia|].
    destruct (decide (Z.of_nat (length arr) = Z.of_nat (length arr))%Z) as [_|?]; [done|lia].
Qed.

(** If inserting [newItem] keeps ids unique, its id differs from any existing
    element's id. *)
Lemma uniqueId_insertIdxIfInBounds_id_neq (arr : list (YjsItem A))
    (newItem a : YjsItem A) (i : nat) :
  uniqueId (insertIdxIfInBounds i newItem arr) -> i <= length arr -> a ∈ arr ->
  item_id newItem <> item_id a.
Proof using A EqDA.
  move=> Huniq Hi Ha.
  rewrite /insertIdxIfInBounds decide_True in Huniq; [|exact Hi].
  have Htl : length (take i arr) = i by rewrite length_take_le.
  set L := take i arr ++ newItem :: drop i arr in Huniq.
  have HLi : L !! i = Some newItem.
  { rewrite /L lookup_app_r; rewrite Htl; [|lia]. by rewrite Nat.sub_diag. }
  have [j Hj] := list_elem_of_lookup_1 _ _ Ha.
  destruct (decide (j < i)%nat) as [Hlt | Hge].
  - have HLj : L !! j = Some a.
    { rewrite /L lookup_app_l; [|rewrite Htl; lia].
      by rewrite lookup_take_lt; [|lia]. }
    have Hidneq := ss_lookup_lt L j i a newItem Huniq HLj HLi Hlt.
    by move=> Heq; apply Hidneq; rewrite Heq.
  - have HLj : L !! (S j) = Some a.
    { rewrite /L lookup_app_r; rewrite Htl; [|lia].
      have -> : S j - i = S (j - i) by lia.
      rewrite /= lookup_drop.
      by have -> : i + (j - i) = j by lia. }
    exact: (ss_lookup_lt L i (S j) newItem a Huniq HLi HLj ltac:(lia)).
Qed.

(** [findPtrIdx] shifts predictably when an element is inserted. *)
Lemma findPtrIdx_insert_some (arr : list (YjsItem A)) (other : YjsPtr A)
    (newItem : YjsItem A) (i : nat) (idx : Z) :
  uniqueId (insertIdxIfInBounds i newItem arr) ->
  findPtrIdx other arr = Some idx ->
  findPtrIdx other (insertIdxIfInBounds i newItem arr) =
    Some (if decide (Z.of_nat i <= idx)%Z then (idx + 1)%Z else idx).
Proof using A EqDA.
  move=> Huniq Hfind.
  destruct (decide (i <= length arr)%nat) as [Hin | Hout]; last first.
  { (* out of bounds: insertion is a no-op *)
    rewrite /insertIdxIfInBounds decide_False; [|exact Hout].
    have Hle := findPtrIdx_le_size arr other idx Hfind.
    rewrite Hfind decide_False; [done|lia]. }
  have Hins : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr.
  { by rewrite /insertIdxIfInBounds decide_True. }
  have Hlen' : length (insertIdxIfInBounds i newItem arr) = S (length arr).
  { rewrite Hins length_app /= length_take_le // length_drop; lia. }
  destruct other as [p| |].
  - (* itemPtr p *)
    move: Hfind; rewrite /findPtrIdx /find_item_idx => Hfind.
    move: Hfind => /fmap_Some [k [Hk Hidx]]; move: Hk => /fmap_Some [[k' p'] [Hfindp Hk2]].
    simpl in Hk2; subst k; subst idx.
    have Hfp := Hfindp; apply list_find_Some in Hfp; destruct Hfp as (Hlk & Hpp & _).
    subst p'.
    have Hpmem : p ∈ arr := list_elem_of_lookup_2 _ _ _ Hlk.
    have Hne : newItem <> p.
    { move=> Heq; apply: (uniqueId_insertIdxIfInBounds_id_neq arr newItem p i Huniq Hin Hpmem).
      by rewrite Heq. }
    rewrite /findPtrIdx /find_item_idx Hins.
    rewrite (list_find_insert_shift (fun i0 => i0 = p) arr i k' p newItem Hne Hin Hfindp) /=.
    destruct (decide (i <= k')%nat) as [Hik|Hik];
      destruct (decide (Z.of_nat i <= Z.of_nat k')%Z) as [Hz|Hz].
    + f_equal; lia.
    + exfalso; lia.
    + exfalso; lia.
    + done.
  - (* First *)
    rewrite /findPtrIdx in Hfind |- *; injection Hfind as <-.
    rewrite decide_False; [done|lia].
  - (* Last *)
    rewrite /findPtrIdx in Hfind |- *; injection Hfind as <-.
    rewrite Hlen' decide_True; [f_equal; lia | lia].
Qed.

End insert.

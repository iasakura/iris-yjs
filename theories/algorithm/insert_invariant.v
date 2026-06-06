(** Inserting an item at the position bounded by its left/right neighbours
    preserves [YjsArrInvariant]. Port of [YjsArrInvariant_insertIdxIfInBounds]
    (and the helper [findPtrIdx_lt_size_getElem]) from
    [LeanYjs/Algorithm/Insert/Spec.lean]. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant transitivity.
From yjs.algorithm Require Import basic insert_basic insert_lemmas invariant_basic
  invariant_yjsarray invariant_yjsarray_idx.

(** Insert [x] into a sorted list at index [i]: provided [x] dominates the
    prefix and is dominated by the suffix, the result stays sorted. *)
Lemma StronglySorted_insert {X} (R : X -> X -> Prop) (l : list X) (i : nat) (x : X) :
  i <= length l ->
  StronglySorted R l ->
  (forall j y, j < i -> l !! j = Some y -> R y x) ->
  (forall j y, i <= j -> l !! j = Some y -> R x y) ->
  StronglySorted R (take i l ++ x :: drop i l).
Proof.
  move=> Hi Hss Hpre Hsuf.
  have Happ : StronglySorted R (take i l ++ drop i l) by rewrite take_drop.
  apply StronglySorted_app in Happ; destruct Happ as (Hcross & Hssl & Hssr).
  apply StronglySorted_app_2; [|exact Hssl|].
  - move=> a b Ha; rewrite elem_of_cons => -[-> | Hb].
    + have [j Hj] := list_elem_of_lookup_1 _ _ Ha.
      have Hji : j < i.
      { have Hlt := lookup_lt_Some _ _ _ Hj.
        rewrite length_take_le in Hlt; [exact Hlt | exact Hi]. }
      apply: (Hpre j a Hji); rewrite -(lookup_take_lt l i j Hji); exact: Hj.
    + exact: (Hcross a b Ha Hb).
  - apply StronglySorted_cons; split; [|exact: Hssr].
    apply Forall_forall => b Hb.
    have [k Hk] := list_elem_of_lookup_1 _ _ Hb.
    apply: (Hsuf (i + k) b); [lia|].
    rewrite -(lookup_drop l i k); exact: Hk.
Qed.

Section invariant.
Context {A : Type} `{EqDA : EqDecision A}.

Lemma YjsArrInvariant_insertIdxIfInBounds (arr : list (YjsItem A)) (newItem : YjsItem A) (i : nat) :
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  YjsArrInvariant arr ->
  i <= length arr ->
  (forall y, 0 < i -> arr !! (i - 1) = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) ->
  (forall y, arr !! i = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
  (forall a, a ∈ arr -> item_id a <> item_id newItem) ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr).
Proof using A EqDA.
  move=> Hclosed Hinv Harr Hi Hlt1 Hlt2 Hneq.
  have Hsorted := yai_sorted _ Harr.
  have Huniq := yai_unique _ Harr.
  have Hins : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr
    by rewrite /insertIdxIfInBounds decide_True.
  have HsetIn : forall y, ArrSet (newItem :: arr) y <-> ArrSet (insertIdxIfInBounds i newItem arr) y.
  { move=> y; rewrite Hins; destruct y as [z| |]; rewrite /ArrSet.
    - rewrite elem_of_app !elem_of_cons.
      have Hsplit : z ∈ arr <-> z ∈ take i arr \/ z ∈ drop i arr.
      { rewrite -elem_of_app take_drop; tauto. }
      rewrite Hsplit; tauto.
    - tauto.
    - tauto. }
  have HPnew : ArrSet (newItem :: arr) (itemPtr newItem)
    by rewrite /ArrSet elem_of_cons; left.
  have HParr : forall z, z ∈ arr -> ArrSet (newItem :: arr) (itemPtr z)
    by move=> z Hz; rewrite /ArrSet elem_of_cons; right.
  have Hpre : forall j y, j < i -> arr !! j = Some y -> YjsLt' (itemPtr y) (itemPtr newItem).
  { move=> j y Hj Hjy.
    have Hi1 : (i - 1) < length arr by lia.
    have [w Hw] := lookup_lt_is_Some_2 arr (i - 1) Hi1.
    have Hwlt : YjsLt' (itemPtr w) (itemPtr newItem) := Hlt1 w ltac:(lia) Hw.
    destruct (decide (j = i - 1)) as [-> | Hne].
    - rewrite Hw in Hjy; injection Hjy as <-; exact Hwlt.
    - have Hjlt : j < i - 1 by lia.
      have Hjw : YjsLt' (itemPtr y) (itemPtr w)
        := ss_lookup_lt arr j (i - 1) y w Hsorted Hjy Hw Hjlt.
      apply: (yjs_leq'_p_trans1 Hinv (itemPtr y) (itemPtr w) (itemPtr newItem));
        [ exact: (HParr _ (list_elem_of_lookup_2 _ _ _ Hjy))
        | exact: (HParr _ (list_elem_of_lookup_2 _ _ _ Hw))
        | exact: HPnew | exact: Hclosed
        | exact: (YjsLeq'_leqLt _ _ Hjw) | exact: Hwlt ]. }
  have Hsuf : forall j y, i <= j -> arr !! j = Some y -> YjsLt' (itemPtr newItem) (itemPtr y).
  { move=> j y Hj Hjy.
    have Hisize : i < length arr.
    { have := lookup_lt_Some _ _ _ Hjy; lia. }
    have [w Hw] := lookup_lt_is_Some_2 arr i Hisize.
    have Hwlt : YjsLt' (itemPtr newItem) (itemPtr w) := Hlt2 w Hw.
    destruct (decide (j = i)) as [-> | Hne].
    - rewrite Hw in Hjy; injection Hjy as <-; exact Hwlt.
    - have Hilt : i < j by lia.
      have Hwj : YjsLt' (itemPtr w) (itemPtr y)
        := ss_lookup_lt arr i j w y Hsorted Hw Hjy Hilt.
      apply: (yjs_leq'_p_trans2 Hinv (itemPtr newItem) (itemPtr w) (itemPtr y));
        [ exact: HPnew
        | exact: (HParr _ (list_elem_of_lookup_2 _ _ _ Hw))
        | exact: (HParr _ (list_elem_of_lookup_2 _ _ _ Hjy))
        | exact: Hclosed | exact: Hwlt | exact: (YjsLeq'_leqLt _ _ Hwj) ]. }
  apply: Build_YjsArrInvariant.
  - apply: (IsClosedItemSet_eq_set _ _ Hclosed HsetIn).
  - apply: (ItemSetInvariant_eq_set _ _ Hclosed Hinv HsetIn).
  - rewrite Hins; apply: StronglySorted_insert => //.
  - rewrite /uniqueId Hins; apply: StronglySorted_insert => //.
    + move=> j y Hj Hjy; exact: (Hneq y (list_elem_of_lookup_2 _ _ _ Hjy)).
    + move=> j y Hj Hjy Heq.
      apply: (Hneq y (list_elem_of_lookup_2 _ _ _ Hjy)); by rewrite Heq.
Qed.

Lemma findPtrIdx_lt_size_getElem (arr : list (YjsItem A)) (p : YjsPtr A) (idx : Z) :
  findPtrIdx p arr = Some idx -> (0 <= idx)%Z -> (Z.to_nat idx < length arr)%nat ->
  itemPtr <$> (arr !! Z.to_nat idx) = Some p.
Proof using A EqDA.
  destruct p as [it| |] => Hfind Hge Hsize.
  - have [j [-> [_ Hj]]] := findPtrIdx_item_exists arr it idx Hfind.
    by rewrite Nat2Z.id Hj.
  - move: Hfind => /= [= ?]; lia.
  - move: Hfind => /= [= ?]; lia.
Qed.

End invariant.

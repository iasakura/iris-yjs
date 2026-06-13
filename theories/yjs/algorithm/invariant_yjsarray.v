(** The full Yjs array invariant [YjsArrInvariant] and document determinism.

    Port of [LeanYjs/Algorithm/Invariant/YjsArray.lean]. The document list is
    closed, satisfies the order invariant, is strictly sorted by [YjsLt'], and
    has unique ids. Lean's [List.Pairwise] is stdpp's [StronglySorted].

    This file holds the invariant definition; the heavy theorems
    ([same_yjs_set_unique] determinism, and the [findPtrIdx_*] family relating
    the algorithm's index functions to the order) are ported on top of it. *)
From stdpp Require Import base list sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant asymmetry.
From yjs.algorithm Require Import basic invariant_basic.

Section yjsarray.
Context {A : Type} `{EqDA : EqDecision A}.

(** Ids occurring in the list are pairwise distinct. *)
Definition uniqueId (items : list (YjsItem A)) : Prop :=
  StronglySorted (fun x y => item_id x <> item_id y) items.

(** The document is closed, order-invariant, [YjsLt']-sorted, and id-unique. *)
Record YjsArrInvariant (arr : list (YjsItem A)) : Prop := {
  yai_closed : IsClosedItemSet (ArrSet arr);
  yai_item_set_inv : ItemSetInvariant (ArrSet arr);
  yai_sorted : StronglySorted (fun x y : YjsItem A => YjsLt' (itemPtr x) (itemPtr y)) arr;
  yai_unique : uniqueId arr;
}.

Definition YjsStateInvariant (s : YjsState A) : Prop := YjsArrInvariant (st_items s).

(** In a sorted suffix [t ++ x :: xs], the head [x] is [R]-related to every
    element of [xs]. *)
Lemma ss_suffix_head {R : YjsItem A -> YjsItem A -> Prop}
    (t : list (YjsItem A)) (x : YjsItem A) (xs zs : list (YjsItem A)) :
  StronglySorted R zs -> t ++ x :: xs = zs -> forall a, a ∈ xs -> R x a.
Proof.
  move=> Hss Heq a Ha; rewrite -Heq in Hss.
  apply StronglySorted_app in Hss; destruct Hss as [_ [_ Hss]].
  apply StronglySorted_inv in Hss; destruct Hss as [_ Hfa].
  move: Hfa => /Forall_forall Hfa; exact: (Hfa a Ha).
Qed.

(** Determinism: two valid documents with the same item set, sharing a common
    suffix structure, coincide. *)
Lemma same_yjs_set_unique_aux (xs_all ys_all : list (YjsItem A)) :
  YjsArrInvariant xs_all -> YjsArrInvariant ys_all ->
  (forall a, ArrSet xs_all a <-> ArrSet ys_all a) ->
  forall xs ys,
  (exists t, t ++ xs = xs_all) -> (exists t, t ++ ys = ys_all) ->
  (forall x, ArrSet xs x <-> ArrSet ys x) ->
  xs = ys.
Proof using A EqDA.
  move=> Hinv1 Hinv2 Hseteq_all.
  have Hclosed2 := yai_closed _ Hinv2.
  have Hisinv2 := yai_item_set_inv _ Hinv2.
  have Hsort1 := yai_sorted _ Hinv1.
  have Hsort2 := yai_sorted _ Hinv2.
  have Huniq1 := yai_unique _ Hinv1.
  have Huniq2 := yai_unique _ Hinv2.
  elim => [|x xs IH] ys Hsub1 Hsub2 Hseteq.
  - case: ys Hsub2 Hseteq => [//|y ys] _ Hseteq; exfalso.
    move: (proj2 (Hseteq (itemPtr y))); rewrite /ArrSet elem_of_nil; apply.
    rewrite elem_of_cons; by left.
  - case: ys Hsub2 Hseteq => [|y ys] Hsub2 Hseteq.
    + exfalso; move: (proj1 (Hseteq (itemPtr x))); rewrite /ArrSet elem_of_nil; apply.
      rewrite elem_of_cons; by left.
    + have Hmin1 : forall a, a ∈ xs -> YjsLt' (itemPtr x) (itemPtr a).
      { move: Hsub1 => [t Ht]; exact: (ss_suffix_head t x xs xs_all Hsort1 Ht). }
      have Hmin2 : forall a, a ∈ ys -> YjsLt' (itemPtr y) (itemPtr a).
      { move: Hsub2 => [t Ht]; exact: (ss_suffix_head t y ys ys_all Hsort2 Ht). }
      have Hxin_all : ArrSet ys_all (itemPtr x).
      { apply (proj1 (Hseteq_all (itemPtr x))); move: Hsub1 => [t Ht].
        rewrite /ArrSet -Ht elem_of_app elem_of_cons; right; by left. }
      have Hyin_all : ArrSet ys_all (itemPtr y).
      { move: Hsub2 => [t Ht]; rewrite /ArrSet -Ht elem_of_app elem_of_cons; right; by left. }
      have Heq : x = y.
      { have Hlt1 : x = y \/ YjsLt' (itemPtr y) (itemPtr x).
        { destruct (decide (x = y)) as [->|Hne]; [by left|right].
          have Hxin : x ∈ y :: ys.
          { apply (proj1 (Hseteq (itemPtr x))); rewrite /ArrSet elem_of_cons; by left. }
          move: Hxin; rewrite elem_of_cons => -[Hxy|Hxin]; [done|exact: (Hmin2 _ Hxin)]. }
        have Hlt2 : x = y \/ YjsLt' (itemPtr x) (itemPtr y).
        { destruct (decide (x = y)) as [->|Hne]; [by left|right].
          have Hyin : y ∈ x :: xs.
          { apply (proj2 (Hseteq (itemPtr y))); rewrite /ArrSet elem_of_cons; by left. }
          move: Hyin; rewrite elem_of_cons => -[Hyx|Hyin]; [by subst|exact: (Hmin1 _ Hyin)]. }
        case: Hlt1 => [//|Hlt1]; case: Hlt2 => [//|Hlt2].
        exfalso; exact: (yjs_lt_asymm Hclosed2 Hisinv2 _ _ Hxin_all Hyin_all Hlt2 Hlt1). }
      subst y; f_equal.
      have Hxxs : x ∉ xs.
      { move: Hsub1 => [t Ht] Hin.
        exact: (ss_suffix_head t x xs xs_all Huniq1 Ht x Hin eq_refl). }
      have Hxys : x ∉ ys.
      { move: Hsub2 => [t Ht] Hin.
        exact: (ss_suffix_head t x ys ys_all Huniq2 Ht x Hin eq_refl). }
      apply: IH.
      * move: Hsub1 => [t Ht]; exists (t ++ [x]); by rewrite -app_assoc.
      * move: Hsub2 => [t Ht]; exists (t ++ [x]); by rewrite -app_assoc.
      * move=> [a'| |] /=; [|tauto|tauto]; split=> Ha'.
        -- have Hin : a' ∈ x :: ys
             by apply (proj1 (Hseteq (itemPtr a'))); rewrite /ArrSet elem_of_cons; by right.
           move: Hin; rewrite elem_of_cons => -[Heq2|//]; subst a'; exfalso; exact: (Hxxs Ha').
        -- have Hin : a' ∈ x :: xs
             by apply (proj2 (Hseteq (itemPtr a'))); rewrite /ArrSet elem_of_cons; by right.
           move: Hin; rewrite elem_of_cons => -[Heq2|//]; subst a'; exfalso; exact: (Hxys Ha').
Qed.

Lemma same_yjs_set_unique (xs ys : list (YjsItem A)) :
  YjsArrInvariant xs -> YjsArrInvariant ys ->
  (forall a, ArrSet xs a <-> ArrSet ys a) ->
  xs = ys.
Proof using A EqDA.
  move=> Hinv1 Hinv2 Hseteq.
  apply: (same_yjs_set_unique_aux xs ys Hinv1 Hinv2 Hseteq xs ys);
    [by exists [] | by exists [] | exact: Hseteq].
Qed.

End yjsarray.

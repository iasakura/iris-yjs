(** Converse direction: the document order [YjsLt'] reflects the [findPtrIdx]
    index order. Port of [getElem_YjsLt'_index_lt], [YjsLt'_findPtrIdx_lt],
    [YjsLeq'_findPtrIdx_leq] from [LeanYjs/Algorithm/Invariant/YjsArray.lean]. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant asymmetry.
From yjs.algorithm Require Import basic insert_basic insert_lemmas
  invariant_basic invariant_yjsarray invariant_yjsarray_idx.

Section conv.
Context {A : Type} `{EqDA : EqDecision A}.

(** A [YjsLt']-smaller element sits at a strictly smaller index. *)
Lemma getElem_YjsLt'_index_lt (arr : list (YjsItem A)) (i j : nat) (x y : YjsItem A) :
  YjsArrInvariant arr -> arr !! i = Some x -> arr !! j = Some y ->
  YjsLt' (itemPtr x) (itemPtr y) -> i < j.
Proof using A EqDA.
  move=> Hinv Hi Hj Hlt; destruct (decide (i < j)) as [|Hge]; first done.
  exfalso.
  have Hpx : ArrSet arr (itemPtr x) := list_elem_of_lookup_2 arr i x Hi.
  have Hpy : ArrSet arr (itemPtr y) := list_elem_of_lookup_2 arr j y Hj.
  have Hleq : YjsLeq' (itemPtr y) (itemPtr x)
    := getElem_leq_YjsLeq' arr j i y x Hinv Hj Hi ltac:(lia).
  case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq) => [Heq | Hyx].
  - rewrite Heq in Hlt.
    exact: (yjs_lt_asymm (yai_closed _ Hinv) (yai_item_set_inv _ Hinv) _ _ Hpx Hpx Hlt Hlt).
  - exact: (yjs_lt_asymm (yai_closed _ Hinv) (yai_item_set_inv _ Hinv) _ _ Hpx Hpy Hlt Hyx).
Qed.

Lemma YjsLt'_findPtrIdx_lt (arr : list (YjsItem A)) (x y : YjsPtr A) (i j : Z) :
  YjsArrInvariant arr -> ArrSet arr x -> ArrSet arr y ->
  YjsLt' x y -> findPtrIdx x arr = Some i -> findPtrIdx y arr = Some j -> (i < j)%Z.
Proof using A EqDA.
  move=> Hinv Hax Hay Hlt Hx Hy.
  have Hc := yai_closed _ Hinv. have Hisi := yai_item_set_inv _ Hinv.
  destruct x as [xx| |]; destruct y as [yy| |].
  - have [ix [Hix [_ Hax']]] := findPtrIdx_item_exists arr xx i Hx.
    have [jy [Hjy [_ Hay']]] := findPtrIdx_item_exists arr yy j Hy.
    have Hlt' : ix < jy := getElem_YjsLt'_index_lt arr ix jy xx yy Hinv Hax' Hay' Hlt. lia.
  - exfalso; case: Hlt => [h Hlt]; exact: (not_ptr_lt_first Hc Hisi h _ Hax Hlt).
  - have [ix [Hix [Hlti _]]] := findPtrIdx_item_exists arr xx i Hx.
    move: Hy => /= [= ?]; lia.
  - have [jy [Hjy [_ _]]] := findPtrIdx_item_exists arr yy j Hy.
    move: Hx => /= [= ?]; lia.
  - exfalso; case: Hlt => [h Hlt]; exact: (not_ptr_lt_first Hc Hisi h _ Hax Hlt).
  - move: Hx Hy => /= [= ?] [= ?]; lia.
  - exfalso; case: Hlt => [h Hlt]; exact: (not_last_lt_ptr Hc Hisi h _ Hay Hlt).
  - exfalso; case: Hlt => [h Hlt]; exact: (not_last_lt_ptr Hc Hisi h _ Hay Hlt).
  - exfalso; case: Hlt => [h Hlt]; exact: (not_last_lt_ptr Hc Hisi h _ Hay Hlt).
Qed.

Lemma YjsLeq'_findPtrIdx_leq (arr : list (YjsItem A)) (x y : YjsPtr A) (i j : Z) :
  YjsArrInvariant arr -> ArrSet arr x -> ArrSet arr y ->
  YjsLeq' x y -> findPtrIdx x arr = Some i -> findPtrIdx y arr = Some j -> (i <= j)%Z.
Proof using A EqDA.
  move=> Hinv Hax Hay Hleq Hx Hy.
  case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq) => [Heq | Hlt].
  - subst y; rewrite Hx in Hy; injection Hy as ->; lia.
  - have Hlt' : (i < j)%Z := YjsLt'_findPtrIdx_lt arr x y i j Hinv Hax Hay Hlt Hx Hy. lia.
Qed.

End conv.

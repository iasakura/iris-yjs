(** Correctness of the integration scan [fii_loop] / [findIntegratedIndex].
    Port of the loop-invariant reasoning in [LeanYjs/Algorithm/Insert/Spec.lean].
    Lean uses a monadic [for]/[ForInStep] loop with [for_in_list_loop_invariant];
    here [fii_loop] is structural recursion over a fuel, so the invariant is
    carried explicitly and maintained by induction on the fuel. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set util.
From yjs.order Require Import item_order item_set_invariant transitivity.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray invariant_yjsarray_idx findptridx_order findptridx_order2
  findptridx_getelem insert_invariant.

Section loop.
Context {A : Type} `{EqDA : EqDecision A}.

(** The scan keeps the destination index within [leftIdx+1 .. current], where
    [current = leftIdx + offset] advances by one each step up to [rightIdx].
    Hence the returned index lies in [leftIdx+1 .. rightIdx]. *)
Lemma fii_loop_bounds (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (arr : list (YjsItem A)) (scanning : bool) (destIdx d : Z) :
  (-1 <= leftIdx)%Z ->
  (leftIdx + 1 <= destIdx)%Z ->
  (destIdx <= leftIdx + Z.of_nat offset)%Z ->
  (leftIdx + Z.of_nat offset + Z.of_nat count = rightIdx)%Z ->
  fii_loop count offset leftIdx rightIdx cid arr scanning destIdx = Some d ->
  (leftIdx + 1 <= d)%Z /\ (d <= rightIdx)%Z.
Proof using A EqDA.
  move: offset scanning destIdx.
  induction count as [|count' IH] => offset scanning destIdx H0 Ha Hb Hc Hloop.
  - move: Hloop => /= [= <-]; lia.
  - move: Hloop => /=.
    move=> /bind_Some [other [_ Hloop]].
    move: Hloop => /bind_Some [oLeftIdx [_ Hloop]].
    move: Hloop => /bind_Some [oRightIdx [_ Hloop]].
    have Hcur0 : (0 <= leftIdx + Z.of_nat offset)%Z by lia.
    move: Hloop.
    destruct (decide (oLeftIdx < leftIdx)%Z) as [_|_]; [move=> [= <-]; lia|].
    destruct (decide (oLeftIdx = leftIdx)%Z) as [_|_].
    + destruct (decide (clientId (item_id other) < cid)%nat) as [_|_].
      * move=> Hrec; apply: (IH (S offset) false _ H0 _ _ _ Hrec); lia.
      * destruct (decide (oRightIdx = rightIdx)%Z) as [_|_]; [move=> [= <-]; lia|].
        move=> Hrec; apply: (IH (S offset) true _ H0 _ _ _ Hrec); lia.
    + move=> Hrec; apply: (IH (S offset) scanning _ H0 _ _ _ Hrec); destruct scanning; lia.
Qed.

(** [findIntegratedIndex] returns a destination in [0 .. rightIdx]. *)
Lemma findIntegratedIndex_bounds (leftIdx rightIdx : Z) (input : IntegrateInput)
    (arr : list (YjsItem A)) (d : nat) :
  (-1 <= leftIdx)%Z -> (leftIdx < rightIdx)%Z ->
  findIntegratedIndex leftIdx rightIdx input arr = Some d ->
  (Z.of_nat d <= rightIdx)%Z.
Proof using A EqDA.
  rewrite /findIntegratedIndex => H0 Hlr.
  move=> /bind_Some [z [Hloop [= <-]]].
  have [Hlo Hhi] := fii_loop_bounds (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
    (clientId (in_id input)) arr false (leftIdx + 1) z H0 ltac:(lia) ltac:(lia) ltac:(lia) Hloop.
  lia.
Qed.

(** The candidate-range push: once [newItem < arr[cur]] is known, every element
    in [[dest, cur]] is also [> newItem], using the candidate property [Htbd].
    Port of [loopInv_YjsLt'] (Spec.lean 143-375), by strong induction on the
    structural size of the item (recursing through origin / right origin). *)
Lemma loopInv_YjsLt' (arr : list (YjsItem A)) (newItem : YjsItem A)
    (rightIdx : Z) (dest : Z) (cur : nat) :
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  YjsArrInvariant arr ->
  findPtrIdx (rightOrigin newItem) arr = Some rightIdx ->
  (0 <= dest)%Z ->
  (Z.of_nat cur <= rightIdx)%Z ->
  (forall (k : nat) y, (dest <= Z.of_nat k)%Z -> (k < cur)%nat -> arr !! k = Some y ->
     (origin y = origin newItem /\ YjsId_lt (item_id newItem) (item_id y)) \/
     (exists dy, arr !! Z.to_nat dest = Some dy /\ YjsLeq' (itemPtr dy) (origin y))) ->
  ((cur < length arr)%nat -> forall y, arr !! cur = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
  forall (j : nat) y, (dest <= Z.of_nat j)%Z -> (j <= cur)%nat -> arr !! j = Some y ->
    YjsLt' (itemPtr newItem) (itemPtr y).
Proof using A EqDA.
  move=> Hclosed Hinv Harr HfindR Hdest0 Hcurle Htbd Hanchor.
  have Hc := yai_closed _ Harr.
  have Hisi := yai_item_set_inv _ Harr.
  have HPnew : ArrSet (newItem :: arr) (itemPtr newItem) by rewrite /ArrSet elem_of_cons; left.
  have HPmem : forall z, z ∈ arr -> ArrSet (newItem :: arr) (itemPtr z)
    by move=> z Hz; rewrite /ArrSet elem_of_cons; right.
  enough (H : forall (n : nat) (j : nat) (y : YjsItem A), (dest <= Z.of_nat j)%Z -> (j <= cur)%nat ->
             arr !! j = Some y -> YjsItem_size y = n -> YjsLt' (itemPtr newItem) (itemPtr y)).
  { move=> j y Hdj Hjc Hjy; apply (H (YjsItem_size y) j y Hdj Hjc Hjy); reflexivity. }
  apply: (nat_strong_ind (fun n => forall (j : nat) (y : YjsItem A), (dest <= Z.of_nat j)%Z ->
            (j <= cur)%nat -> arr !! j = Some y -> YjsItem_size y = n -> YjsLt' (itemPtr newItem) (itemPtr y))).
  move=> n IH j y Hdj Hjc Hjy Hn.
  destruct (decide (j < cur)%nat) as [Hjlt | Hjge]; last first.
  { have Hjeq : j = cur by lia. subst j.
    exact: (Hanchor (lookup_lt_Some _ _ _ Hjy) y Hjy). }
  have Hymem : y ∈ arr := list_elem_of_lookup_2 _ _ _ Hjy.
  have Hjsize : (j < length arr)%nat := lookup_lt_Some _ _ _ Hjy.
  case: (Htbd j y Hdj Hjlt Hjy) => [[Horigin Hidlt] | [dy [Hdy Hleqdy]]].
  - (* same origin, larger id: ltOriginSame *)
    have hlt_ro : YjsLt' (itemPtr newItem) (rightOrigin y).
    { have Hror : rightOrigin y <> First := not_rightOrigin_first (P := ArrSet arr) y Hc Hisi Hymem.
      case: (arr_set_closed_exists_index_for_right_origin arr y Hc Hymem)
        => [Hf | [Hl | [roIdx [ro [Hro Hroeq]]]]].
      - by rewrite Hf in Hror.
      - rewrite Hl; apply: YjsLt'_ltOriginOrder; apply: lt_last.
      - have Hyro : YjsLt' (itemPtr y) (itemPtr ro).
        { rewrite -Hroeq; destruct y as [yo yr yid yc]; rewrite /rightOrigin /=.
          exists 1; apply: ltRightOrigin; apply: leqSame. }
        have HjroIdx : (j < roIdx)%nat := @getElem_YjsLt'_index_lt _ EqDA arr j roIdx y ro Harr Hjy Hro Hyro.
        have HdestroIdx : (dest <= Z.of_nat roIdx)%Z by lia.
        have HrosizeLt : (YjsItem_size ro < n)%nat.
        { subst n; destruct y as [yo yr yid yc]; rewrite /rightOrigin /= in Hroeq; subst yr; simpl; lia. }
        destruct (decide (roIdx < cur)%nat) as [Hroc | Hroc].
        + have HH := IH (YjsItem_size ro) HrosizeLt roIdx ro HdestroIdx ltac:(lia) Hro eq_refl.
          by rewrite Hroeq.
        + have HroIdxsize : (roIdx < length arr)%nat := lookup_lt_Some _ _ _ Hro.
          have Hcurlt : (cur < length arr)%nat by lia.
          have [ycur Hycur] := lookup_lt_is_Some_2 arr cur Hcurlt.
          rewrite Hroeq.
          apply: (yjs_leq'_p_trans2 Hinv (itemPtr newItem) (itemPtr ycur) (itemPtr ro)
            HPnew (HPmem _ (list_elem_of_lookup_2 _ _ _ Hycur))
            (HPmem _ (list_elem_of_lookup_2 _ _ _ Hro)) Hclosed
            (Hanchor Hcurlt ycur Hycur)).
          exact: (getElem_leq_YjsLeq' arr cur roIdx ycur ro Harr Hycur Hro ltac:(lia)). }
    have hlt_ro' : YjsLt' (itemPtr y) (rightOrigin newItem).
    { apply: (findPtrIdx_lt_YjsLt' arr (itemPtr y) (rightOrigin newItem) (Z.of_nat j) rightIdx Harr
        (findPtrIdx_getElem arr j y Harr Hjy) HfindR); lia. }
    destruct newItem as [no nr nid nc]; destruct y as [yo yr yid yc].
    rewrite /origin /= in Horigin; subst yo.
    apply: YjsLt'_ltConflict.
    apply: (ConflictLt'_ltOriginSame no nr yr nid yid nc yc).
    + exact: hlt_ro.
    + exact: hlt_ro'.
    + exact: Hidlt.
  - (* arr[dest] <= origin y: ltOrigin *)
    have hlt_o : YjsLt' (itemPtr newItem) (origin y).
    { have Hdymem : dy ∈ arr := list_elem_of_lookup_2 _ _ _ Hdy.
      case: (arr_set_closed_exists_index_for_origin arr y Hc Hymem)
        => [Hf | [Hl | [oIdx [o [Ho Hoeq]]]]].
      - exfalso; rewrite Hf in Hleqdy.
        case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleqdy) => [Heq | Hlt]; [done|].
        exact: (not_ptr_lt'_first Hc Hisi (itemPtr dy) Hdymem Hlt).
      - rewrite Hl; apply: YjsLt'_ltOriginOrder; apply: lt_last.
      - have Hoyset : o ∈ arr := list_elem_of_lookup_2 _ _ _ Ho.
        have HfindDy : findPtrIdx (itemPtr dy) arr = Some dest.
        { have := findPtrIdx_getElem arr (Z.to_nat dest) dy Harr Hdy.
          by rewrite Z2Nat.id. }
        have HleqO : YjsLeq' (itemPtr dy) (itemPtr o) by rewrite -Hoeq.
        have HdestoIdx : (dest <= Z.of_nat oIdx)%Z :=
          YjsLeq'_findPtrIdx_leq arr (itemPtr dy) (itemPtr o) dest (Z.of_nat oIdx) Harr
            Hdymem Hoyset HleqO HfindDy (findPtrIdx_getElem arr oIdx o Harr Ho).
        have Hoy : YjsLt' (itemPtr o) (itemPtr y).
        { rewrite -Hoeq; destruct y as [yo yr yid yc]; rewrite /origin /=.
          exists 1; apply: ltOrigin; apply: leqSame. }
        have HoIdxj : (oIdx < j)%nat := @getElem_YjsLt'_index_lt _ EqDA arr oIdx j o y Harr Ho Hjy Hoy.
        have HosizeLt : (YjsItem_size o < n)%nat.
        { subst n; destruct y as [yo yr yid yc]; rewrite /origin /= in Hoeq; subst yo; simpl; lia. }
        have HH := IH (YjsItem_size o) HosizeLt oIdx o HdestoIdx ltac:(lia) Ho eq_refl.
        by rewrite Hoeq. }
    destruct y as [yo yr yid yc]; rewrite /origin /= in hlt_o.
    apply: YjsLt'_ltOrigin; apply: YjsLeq'_leqLt; exact: hlt_o.
Qed.

End loop.

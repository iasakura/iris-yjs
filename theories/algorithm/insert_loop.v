(** Correctness of the integration scan [fii_loop] / [findIntegratedIndex].
    Port of the loop-invariant reasoning in [LeanYjs/Algorithm/Insert/Spec.lean].
    Lean uses a monadic [for]/[ForInStep] loop with [for_in_list_loop_invariant];
    here [fii_loop] is structural recursion over a fuel, so the invariant is
    carried explicitly and maintained by induction on the fuel. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set util.
From yjs.order Require Import item_order item_set_invariant transitivity totality no_cross_origin.
From yjs.algorithm Require Import basic insert_basic insert_lemmas invariant_basic
  invariant_yjsarray invariant_yjsarray_idx findptridx_order findptridx_order2
  findptridx_getelem findptridx_origin insert_invariant.

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

(** [newItem] is below the (structural) right origin. *)
Lemma item_lt_rightOrigin (it : YjsItem A) : YjsLt' (itemPtr it) (rightOrigin it).
Proof. destruct it as [o r id c]; exists 1; apply: ltRightOrigin; apply: leqSame. Qed.

(** Loop-invariant maintenance for [fii_loop]. The standing hypotheses fix the
    new item and its resolved origin/right-origin indices. *)
Section spec.
Context (arr : list (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : Z).
Context
  (Hclosed : IsClosedItemSet (ArrSet (newItem :: arr)))
  (Hinv : ItemSetInvariant (ArrSet (newItem :: arr)))
  (Harr : YjsArrInvariant arr)
  (Hmax : forall x, ArrSet arr (itemPtr x) ->
     clientId (item_id x) = clientId (item_id newItem) ->
     (clock (item_id x) < clock (item_id newItem))%nat)
  (HfindL : findPtrIdx (origin newItem) arr = Some leftIdx)
  (HfindR : findPtrIdx (rightOrigin newItem) arr = Some rightIdx)
  (HleftIdx : (-1 <= leftIdx)%Z)
  (HleftR : (leftIdx < rightIdx)%Z)
  (HRsize : (rightIdx <= Z.of_nat (length arr))%Z).

(** The carried invariant at loop state [(offset, scanning, destIdx)];
    [cur = leftIdx + offset] is the next index to scan. *)
Definition LInv (offset : nat) (scanning : bool) (destIdx : Z) : Prop :=
  (leftIdx + 1 <= destIdx <= leftIdx + Z.of_nat offset)%Z /\
  (forall k y, (Z.of_nat k < destIdx)%Z -> arr !! k = Some y ->
     YjsLt' (itemPtr y) (itemPtr newItem)) /\
  (forall k y, (destIdx <= Z.of_nat k)%Z -> (Z.of_nat k < leftIdx + Z.of_nat offset)%Z ->
     arr !! k = Some y ->
     (origin y = origin newItem /\ YjsId_lt (item_id newItem) (item_id y)) \/
     (exists dy, arr !! Z.to_nat destIdx = Some dy /\ YjsLeq' (itemPtr dy) (origin y))) /\
  (scanning = true -> exists dy, arr !! Z.to_nat destIdx = Some dy /\ origin dy = origin newItem) /\
  (scanning = false -> destIdx = (leftIdx + Z.of_nat offset)%Z).

(** At any exit point the destination is below [arr[destIdx]], by pushing the
    [cur]-anchor back through the candidate range. *)
Lemma exit_C2 (offset : nat) (scanning : bool) (destIdx : Z) :
  (leftIdx + Z.of_nat offset <= rightIdx)%Z ->
  LInv offset scanning destIdx ->
  ((Z.to_nat (leftIdx + Z.of_nat offset) < length arr)%nat -> forall y,
     arr !! Z.to_nat (leftIdx + Z.of_nat offset) = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
  forall y, arr !! Z.to_nat destIdx = Some y -> YjsLt' (itemPtr newItem) (itemPtr y).
Proof using All.
  move=> Hcurle [Hbounds [HP1 [HPmid [_ _]]]] Hanchor y Hy.
  have Hcur0 : (0 <= leftIdx + Z.of_nat offset)%Z by lia.
  apply: (loopInv_YjsLt' arr newItem rightIdx destIdx (Z.to_nat (leftIdx + Z.of_nat offset))
            Hclosed Hinv Harr HfindR ltac:(lia) _ _ Hanchor (Z.to_nat destIdx) y _ _ Hy).
  - rewrite Z2Nat.id; lia.
  - move=> k yk Hdk Hkcur Hyk.
    apply: (HPmid k yk Hdk _ Hyk); lia.
  - lia.
  - lia.
Qed.

(** In an advancing step, the scanned [other] is below [newItem]. *)
Lemma other_lt_newItem (i : nat) (other : YjsItem A) (oLeftIdx oRightIdx : Z) :
  arr !! i = Some other ->
  (leftIdx < Z.of_nat i)%Z -> (Z.of_nat i < rightIdx)%Z ->
  findPtrIdx (origin other) arr = Some oLeftIdx ->
  findPtrIdx (rightOrigin other) arr = Some oRightIdx ->
  (leftIdx <= oLeftIdx)%Z ->
  (leftIdx = oLeftIdx -> YjsId_lt (item_id other) (item_id newItem)) ->
  YjsLt' (origin other) (itemPtr newItem) ->
  YjsLt' (itemPtr other) (itemPtr newItem).
Proof using All.
  move=> Hi Hli Hir HoL HoR Hle Hidcond Hoo.
  have HfindOther : findPtrIdx (itemPtr other) arr = Some (Z.of_nat i) := @findPtrIdx_getElem _ EqDA arr i other Harr Hi.
  apply: (findPtrIdx_origin_leq_newItem_YjsLt' (newItem :: arr) arr other newItem
            leftIdx rightIdx oLeftIdx oRightIdx).
  - move=> z Hz; rewrite elem_of_cons; by right.
  - rewrite elem_of_cons; by left.
  - rewrite elem_of_cons; right; exact: (list_elem_of_lookup_2 _ _ _ Hi).
  - exact Hclosed.
  - exact Hinv.
  - exact Harr.
  - exact HfindL.
  - exact HfindR.
  - exact HoL.
  - exact HoR.
  - apply: (findPtrIdx_lt_YjsLt' arr (origin newItem) (itemPtr other) leftIdx (Z.of_nat i));
      [exact Harr | exact HfindL | exact HfindOther | exact Hli].
  - apply: (findPtrIdx_lt_YjsLt' arr (itemPtr other) (rightOrigin newItem) (Z.of_nat i) rightIdx);
      [exact Harr | exact HfindOther | exact HfindR | exact Hir].
  - exact Hle.
  - exact Hidcond.
  - exact Hoo.
Qed.

(** Common to both break cases: useful memberships. *)
Lemma arrset_new : ArrSet (newItem :: arr) (itemPtr newItem).
Proof using A. by rewrite /ArrSet elem_of_cons; left. Qed.
Lemma arrset_mem (z : YjsItem A) : z ∈ arr -> ArrSet (newItem :: arr) (itemPtr z).
Proof using A. by move=> Hz; rewrite /ArrSet elem_of_cons; right. Qed.

(** [other] is distinct from [newItem] (else the clock would be self-smaller). *)
Lemma other_ne_newItem (other : YjsItem A) : other ∈ arr -> other <> newItem.
Proof using A Hmax. move=> Hmem Heq; have := Hmax other Hmem; rewrite Heq => H; lia. Qed.

(** break case 1: the scanned item's origin is strictly before [newItem]'s, so
    [newItem] precedes it (uses no-cross-origin). *)
Lemma break1_newItem_lt (i : nat) (other : YjsItem A) (oLeftIdx : Z) :
  arr !! i = Some other ->
  (leftIdx < Z.of_nat i)%Z ->
  findPtrIdx (origin other) arr = Some oLeftIdx ->
  (oLeftIdx < leftIdx)%Z ->
  YjsLt' (itemPtr newItem) (itemPtr other).
Proof using All.
  move=> Hi Hli HoL Hc1.
  have Hmem : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hi.
  have Hother_set := arrset_mem other Hmem.
  have Hnew_set := arrset_new.
  case: (YjsLeq'_or_YjsLt' Hinv Hclosed Hother_set Hnew_set) => [Hleq | Hlt]; last exact Hlt.
  exfalso.
  have Hotherlt : YjsLt' (itemPtr other) (itemPtr newItem).
  { case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq) => [Heq | Hlt]; [|exact Hlt].
    exfalso; have := other_ne_newItem other Hmem; congruence. }
  have HfindOther : findPtrIdx (itemPtr other) arr = Some (Z.of_nat i)
    := @findPtrIdx_getElem _ EqDA arr i other Harr Hi.
  have Horig_new : ArrSet arr (origin newItem) := @findPtrIdx_ArrSet _ EqDA arr (origin newItem) leftIdx HfindL.
  have Horig_oth : ArrSet arr (origin other) := @findPtrIdx_ArrSet _ EqDA arr (origin other) oLeftIdx HoL.
  case: (no_cross_origin Hclosed Hinv other newItem Hother_set Hnew_set Hotherlt) => [Hle1 | Hle1].
  - have Hle : (leftIdx <= oLeftIdx)%Z :=
      @YjsLeq'_findPtrIdx_leq _ EqDA arr (origin newItem) (origin other) leftIdx oLeftIdx
        Harr Horig_new Horig_oth Hle1 HfindL HoL.
    lia.
  - have Hle : (Z.of_nat i <= leftIdx)%Z :=
      @YjsLeq'_findPtrIdx_leq _ EqDA arr (itemPtr other) (origin newItem) (Z.of_nat i) leftIdx
        Harr Hmem Horig_new Hle1 HfindOther HfindL.
    lia.
Qed.

(** break case 2: same origin and right origin as [newItem], and [other]'s
    client id does not beat [newItem]'s, so [newItem] precedes [other]. *)
Lemma break2_newItem_lt (i : nat) (other : YjsItem A) (oLeftIdx oRightIdx : Z) :
  arr !! i = Some other ->
  findPtrIdx (origin other) arr = Some oLeftIdx ->
  findPtrIdx (rightOrigin other) arr = Some oRightIdx ->
  oLeftIdx = leftIdx -> oRightIdx = rightIdx ->
  ~ (clientId (item_id other) < clientId (item_id newItem))%nat ->
  YjsLt' (itemPtr newItem) (itemPtr other).
Proof using All.
  move=> Hi HoL HoR Hoeq Hreq Hcid.
  have Hmem : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hi.
  have HoL' : findPtrIdx (origin other) arr = Some leftIdx by rewrite -Hoeq.
  have HoR' : findPtrIdx (rightOrigin other) arr = Some rightIdx by rewrite -Hreq.
  have Horig_eq : origin newItem = origin other :=
    @findPtrIdx_eq_ok_inj _ EqDA arr (origin newItem) (origin other) leftIdx HfindL HoL'.
  have Hror_eq : rightOrigin newItem = rightOrigin other :=
    @findPtrIdx_eq_ok_inj _ EqDA arr (rightOrigin newItem) (rightOrigin other) rightIdx HfindR HoR'.
  have Hidlt : YjsId_lt (item_id newItem) (item_id other).
  { rewrite /YjsId_lt; case_bool_decide as Hc.
    - apply: (Hmax other Hmem); by rewrite Hc.
    - lia. }
  destruct newItem as [no nr nid nc]; destruct other as [oo orr oid oc].
  move: Horig_eq Hror_eq Hidlt; rewrite /origin /rightOrigin /item_id /= => Horig_eq Hror_eq Hidlt.
  subst oo; subst orr.
  apply: YjsLt'_ltConflict.
  apply: (ConflictLt'_ltOriginSame no nr nr nid oid nc oc).
  - exact: (item_lt_rightOrigin (Item no nr nid nc)).
  - exact: (item_lt_rightOrigin (Item no nr oid oc)).
  - exact: Hidlt.
Qed.

End spec.

End loop.

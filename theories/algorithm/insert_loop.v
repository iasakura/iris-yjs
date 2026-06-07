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
  findptridx_getelem findptridx_origin insert_invariant toitem_lemmas findptridx_insert.

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

(** Same-origin and bigger-id from an advancing/scanning [other] with
    [oLeftIdx = leftIdx]. *)
Lemma same_origin_bigger_id (other : YjsItem A) (oLeftIdx : Z) :
  other ∈ arr ->
  findPtrIdx (origin other) arr = Some oLeftIdx -> oLeftIdx = leftIdx ->
  ~ (clientId (item_id other) < clientId (item_id newItem))%nat ->
  origin other = origin newItem /\ YjsId_lt (item_id newItem) (item_id other).
Proof using All.
  move=> Hmem HoL Hoeq Hcid.
  have HoL' : findPtrIdx (origin other) arr = Some leftIdx by rewrite -Hoeq.
  split.
  - exact: (@findPtrIdx_eq_ok_inj _ EqDA arr (origin other) (origin newItem) leftIdx HoL' HfindL).
  - rewrite /YjsId_lt; case_bool_decide as Hc; [apply: (Hmax other Hmem); by rewrite Hc | lia].
Qed.

(** The main loop-invariant spec: from [LInv] at entry, the returned destination
    has everything before it [< newItem] and [arr] at it [> newItem]. *)
Lemma fii_loop_spec : forall (count offset : nat) (scanning : bool) (destIdx d : Z),
  (leftIdx + Z.of_nat offset + Z.of_nat count = rightIdx)%Z ->
  LInv offset scanning destIdx ->
  fii_loop count offset leftIdx rightIdx (clientId (item_id newItem)) arr scanning destIdx = Some d ->
  (forall k y, (Z.of_nat k < d)%Z -> arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) /\
  (forall y, arr !! Z.to_nat d = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)).
Proof using All.
  induction count as [|count' IH] => offset scanning destIdx d Hcount Hlinv Hloop.
  - (* count = 0: cur = rightIdx; arr[rightIdx] = rightOrigin *)
    move: Hloop => /= [= <-].
    move: (Hlinv) => [Hbounds [HP1 _]].
    split; first exact HP1.
    apply: (exit_C2 offset scanning destIdx ltac:(lia) Hlinv).
    move=> Hsz y Hy.
    have Hcureq : (leftIdx + Z.of_nat offset = rightIdx)%Z by lia.
    rewrite Hcureq in Hsz Hy.
    have HH := @findPtrIdx_lt_size_getElem _ EqDA arr (rightOrigin newItem) rightIdx HfindR ltac:(lia) Hsz.
    rewrite Hy /= in HH; injection HH as Hroeq.
    rewrite Hroeq; exact: (item_lt_rightOrigin newItem).
  - (* S count' *)
    move: Hloop => /=; rewrite /getElemExcept.
    move=> /bind_Some [other [Hother Hloop]].
    move: Hloop => /bind_Some [oLeftIdx [HoL Hloop]].
    move: Hloop => /bind_Some [oRightIdx [HoR Hloop]].
    move: (Hlinv) => [Hbounds [HP1 [HPmid [Hscan Hnotscan]]]].
    have Hcur0 : (0 <= leftIdx + Z.of_nat offset)%Z by lia.
    have Hieq : Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset)) = (leftIdx + Z.of_nat offset)%Z
      by rewrite Z2Nat.id.
    have Hli : (leftIdx < leftIdx + Z.of_nat offset)%Z by lia.
    have Hir : (leftIdx + Z.of_nat offset < rightIdx)%Z by lia.
    have Hmem : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hother.
    have Hother_set := arrset_mem other Hmem.
    (* the candidate at the current index, used by advancing P1 / scanning Pmid *)
    have Hadvance : (leftIdx <= oLeftIdx)%Z -> (leftIdx = oLeftIdx -> YjsId_lt (item_id other) (item_id newItem)) ->
        YjsLt' (origin other) (itemPtr newItem) -> YjsLt' (itemPtr other) (itemPtr newItem).
    { move=> Hle Hidc Hoo.
      apply: (other_lt_newItem (Z.to_nat (leftIdx + Z.of_nat offset)) other oLeftIdx oRightIdx
                Hother _ _ HoL HoR Hle Hidc Hoo); lia. }
    (* prefix-< update when destIdx advances to i+1, given other < newItem *)
    have HP1adv : YjsLt' (itemPtr other) (itemPtr newItem) ->
        forall k y, (Z.of_nat k < Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset) + 1))%Z ->
          arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem).
    { move=> Hother_lt k yk Hk Hyk.
      destruct (decide (Z.of_nat k < destIdx)%Z) as [Hkd|Hkd]; first exact: (HP1 k yk Hkd Hyk).
      have Hki : (k <= Z.to_nat (leftIdx + Z.of_nat offset))%nat by lia.
      have Hyko : YjsLeq' (itemPtr yk) (itemPtr other) :=
        getElem_leq_YjsLeq' arr k (Z.to_nat (leftIdx + Z.of_nat offset)) yk other Harr Hyk Hother Hki.
      apply: (yjs_leq'_p_trans1 Hinv (itemPtr yk) (itemPtr other) (itemPtr newItem)
                (arrset_mem yk (list_elem_of_lookup_2 _ _ _ Hyk)) Hother_set arrset_new Hclosed Hyko Hother_lt). }
    move: Hloop.
    destruct (decide (oLeftIdx < leftIdx)%Z) as [Hc1|Hc1].
    + (* break1 *)
      move=> [= <-]; split; first exact HP1.
      apply: (exit_C2 offset scanning destIdx ltac:(lia) Hlinv).
      move=> Hsz z Hz; rewrite Hother in Hz; injection Hz as <-.
      exact: (break1_newItem_lt (Z.to_nat (leftIdx + Z.of_nat offset)) other oLeftIdx Hother ltac:(lia) HoL Hc1).
    + destruct (decide (oLeftIdx = leftIdx)%Z) as [Hc2|Hc2].
      * (* oLeftIdx = leftIdx *)
        destruct (decide (clientId (item_id other) < clientId (item_id newItem))%nat) as [Hc3|Hc3].
        -- (* cid-advance: scanning:=false, destIdx:=i+1 *)
           move=> Hrec.
           have Hoo : YjsLt' (origin other) (itemPtr newItem).
           { have Horeq : origin other = origin newItem :=
               @findPtrIdx_eq_ok_inj _ EqDA arr (origin other) (origin newItem) leftIdx
                 ltac:(rewrite -Hc2; exact HoL) HfindL.
             rewrite Horeq; destruct newItem as [no nr nid nc]; rewrite /origin /=.
             exists 1; apply: ltOrigin; apply: leqSame. }
           have Hother_lt : YjsLt' (itemPtr other) (itemPtr newItem).
           { apply: Hadvance; [lia | move=> _; rewrite /YjsId_lt; case_bool_decide as Hc; lia | exact Hoo]. }
           apply: (IH (S offset) false (Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset) + 1)) d _ _ Hrec).
           ++ lia.
           ++ rewrite /LInv; split_and!.
              ** lia.
              ** lia.
              ** exact: (HP1adv Hother_lt).
              ** move=> k yk Hk1 Hk2 Hyk; exfalso; lia.
              ** done.
              ** move=> _; lia.
        -- destruct (decide (oRightIdx = rightIdx)%Z) as [Hc4|Hc4].
           ++ (* break2 *)
              move=> [= <-]; split; first exact HP1.
              apply: (exit_C2 offset scanning destIdx ltac:(lia) Hlinv).
              move=> Hsz z Hz; rewrite Hother in Hz; injection Hz as <-.
              exact: (break2_newItem_lt (Z.to_nat (leftIdx + Z.of_nat offset)) other oLeftIdx oRightIdx
                        Hother HoL HoR Hc2 Hc4 Hc3).
           ++ (* scan-true: scanning:=true, destIdx unchanged *)
              move=> Hrec.
              have Hcand := same_origin_bigger_id other oLeftIdx Hmem HoL Hc2 Hc3.
              have Hpscan' : exists dy, arr !! Z.to_nat destIdx = Some dy /\ origin dy = origin newItem.
              { destruct scanning; first exact: (Hscan eq_refl).
                rewrite (Hnotscan eq_refl); exists other; split; [exact Hother | exact: (proj1 Hcand)]. }
              apply: (IH (S offset) true destIdx d _ _ Hrec).
              ** lia.
              ** rewrite /LInv; split_and!.
                 --- lia.
                 --- lia.
                 --- exact HP1.
                 --- move=> k yk Hk1 Hk2 Hyk.
                     destruct (decide (Z.of_nat k < leftIdx + Z.of_nat offset)%Z) as [Hkc|Hkc];
                       first exact: (HPmid k yk Hk1 Hkc Hyk).
                     left; have Hkeq : k = Z.to_nat (leftIdx + Z.of_nat offset) by lia.
                     subst k; rewrite Hother in Hyk; injection Hyk as <-; exact Hcand.
                 --- move=> _; exact Hpscan'.
                 --- done.
      * (* oLeftIdx > leftIdx *)
        destruct scanning.
        -- (* scan-stay: scanning=true, destIdx unchanged *)
           move=> Hrec.
           have [dy [Hdy Hdyo]] := Hscan eq_refl.
           have Hdmem : dy ∈ arr := list_elem_of_lookup_2 _ _ _ Hdy.
           have Hpmid_new : exists dy0, arr !! Z.to_nat destIdx = Some dy0 /\ YjsLeq' (itemPtr dy0) (origin other).
           { have Hdid : (Z.to_nat destIdx <= Z.to_nat (leftIdx + Z.of_nat offset))%nat by lia.
             have Hdle : YjsLeq' (itemPtr dy) (itemPtr other) :=
               getElem_leq_YjsLeq' arr (Z.to_nat destIdx) (Z.to_nat (leftIdx + Z.of_nat offset)) dy other Harr Hdy Hother Hdid.
             have Hdlt : YjsLt' (itemPtr dy) (itemPtr other).
             { case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hdle) => [Heq | Hlt]; [|exact Hlt].
               exfalso; have Hdoeq : origin other = origin newItem by (move: Heq => [= <-]; exact Hdyo).
               have : (leftIdx = oLeftIdx)%Z.
               { have HoL2 : findPtrIdx (origin newItem) arr = Some oLeftIdx by rewrite -Hdoeq.
                 by move: HoL2; rewrite HfindL => -[= ->]. }
               lia. }
             case: (no_cross_origin Hclosed Hinv dy other (arrset_mem dy Hdmem) Hother_set Hdlt) => [Hle1 | Hle1].
             - exfalso.
               have Hle : (oLeftIdx <= leftIdx)%Z.
               { apply: (@YjsLeq'_findPtrIdx_leq _ EqDA arr (origin other) (origin dy) oLeftIdx leftIdx
                   Harr (@findPtrIdx_ArrSet _ EqDA arr (origin other) oLeftIdx HoL)
                   (@findPtrIdx_ArrSet _ EqDA arr (origin dy) leftIdx ltac:(rewrite Hdyo; exact HfindL))
                   Hle1 HoL ltac:(rewrite Hdyo; exact HfindL)). }
               lia.
             - exists dy; split; [exact Hdy | exact Hle1]. }
           apply: (IH (S offset) true destIdx d _ _ Hrec).
           ** lia.
           ** rewrite /LInv; split_and!.
              --- lia.
              --- lia.
              --- exact HP1.
              --- move=> k yk Hk1 Hk2 Hyk.
                  destruct (decide (Z.of_nat k < leftIdx + Z.of_nat offset)%Z) as [Hkc|Hkc];
                    first exact: (HPmid k yk Hk1 Hkc Hyk).
                  right; have Hkeq : k = Z.to_nat (leftIdx + Z.of_nat offset) by lia.
                  subst k; rewrite Hother in Hyk; injection Hyk as <-; exact Hpmid_new.
              --- move=> _; exact: (Hscan eq_refl).
              --- done.
        -- (* else-advance: scanning=false, destIdx:=i+1 *)
           move=> Hrec.
           have Hdest_i : destIdx = (leftIdx + Z.of_nat offset)%Z := Hnotscan eq_refl.
           have Hoo : YjsLt' (origin other) (itemPtr newItem).
           { have Horig_set : ArrSet arr (origin other) := @findPtrIdx_ArrSet _ EqDA arr (origin other) oLeftIdx HoL.
             destruct (origin other) as [oo| |] eqn:Hooe.
             - (* itemPtr oo at index oLeftIdx < destIdx *)
               have Hoolt : YjsLt' (itemPtr oo) (itemPtr other).
               { rewrite -Hooe; destruct other as [a b c e]; rewrite /origin /=; exists 1; apply: ltOrigin; apply: leqSame. }
               have [k Hk] := arr_set_item_exists_index arr oo Horig_set.
               have HkLt : (k < Z.to_nat (leftIdx + Z.of_nat offset))%nat :=
                 @getElem_YjsLt'_index_lt _ EqDA arr k (Z.to_nat (leftIdx + Z.of_nat offset)) oo other Harr Hk Hother Hoolt.
               apply: (HP1 k oo _ Hk); lia.
             - apply: YjsLt'_ltOriginOrder; apply: lt_first.
             - exfalso. have Hol : YjsLt' (origin other) (itemPtr other).
               { destruct other as [a b c e]; rewrite /origin /=; exists 1; apply: ltOrigin; apply: leqSame. }
               move: Hol; rewrite Hooe => -[h Hol].
               exact: (not_last_lt_ptr (yai_closed _ Harr) (yai_item_set_inv _ Harr) h (itemPtr other) Hmem Hol). }
           have Hother_lt : YjsLt' (itemPtr other) (itemPtr newItem) by apply: Hadvance; [lia | lia | exact Hoo].
           apply: (IH (S offset) false (Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset) + 1)) d _ _ Hrec).
           ** lia.
           ** rewrite /LInv; split_and!.
              --- lia.
              --- lia.
              --- exact: (HP1adv Hother_lt).
              --- move=> k yk Hk1 Hk2 Hyk; exfalso; lia.
              --- done.
              --- move=> _; lia.
Qed.

End spec.

End loop.

(** Validity of the new item and clock-maximality, and the top-level integrate
    correctness. Port of [IsItemValid], [maximalId], [YjsArrInvariant_integrate]
    from [LeanYjs/Algorithm/Insert/Spec.lean]. *)
Section integrate.
Context {A : Type} `{EqDA : EqDecision A}.

Record IsItemValid (item : YjsItem A) : Prop := {
  iiv_origin_lt : YjsLt' (origin item) (rightOrigin item);
  iiv_reachable : forall x, OriginReachable (itemPtr item) x ->
    YjsLeq' x (origin item) \/ YjsLeq' (rightOrigin item) x;
}.

Definition maximalId (newItem : YjsItem A) (arr : list (YjsItem A)) : Prop :=
  forall x, ArrSet arr (itemPtr x) ->
    clientId (item_id x) = clientId (item_id newItem) ->
    (clock (item_id x) < clock (item_id newItem))%nat.

Lemma item_origin_lt (it : YjsItem A) : YjsLt' (origin it) (itemPtr it).
Proof. destruct it as [o r id c]; exists 1; apply: ltOrigin; apply: leqSame. Qed.

Theorem YjsArrInvariant_integrate (input : IntegrateInput) (arr newArr : list (YjsItem A))
    (newItem : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  integrate input arr = Some newArr ->
  exists i, (i <= length arr)%nat /\ newArr = insertIdxIfInBounds i newItem arr /\ YjsArrInvariant newArr.
Proof using A EqDA.
  move=> Harr Htoitem Hvalid Hmax.
  rewrite /integrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  move: Hr2 => /bind_Some [destIdx [HfindIdx Hr3]].
  move: Hr3 => /bind_Some [item [Hmk [= <-]]].
  have Huniq := yai_unique _ Harr.
  (* origin / right-origin indices *)
  have HfindL : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem); exact HfindLeft. }
  have HfindR : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem); exact HfindRight. }
  have Horig_set : ArrSet arr (origin newItem) := @findPtrIdx_ArrSet _ EqDA arr (origin newItem) leftIdx HfindL.
  have Hror_set : ArrSet arr (rightOrigin newItem) := @findPtrIdx_ArrSet _ EqDA arr (rightOrigin newItem) rightIdx HfindR.
  have Hclosed : IsClosedItemSet (ArrSet (newItem :: arr)) :=
    arr_set_closed_push arr newItem (yai_closed _ Harr) Horig_set Hror_set.
  (* item set invariant after push *)
  have Hsameid : forall x, ArrSet arr (itemPtr x) -> item_id x = item_id newItem -> x = newItem.
  { move=> x Hx Hxid; exfalso.
    have Hcc : clientId (item_id x) = clientId (item_id newItem) by rewrite Hxid.
    have Hcl := Hmax x Hx Hcc; rewrite Hxid in Hcl; lia. }
  have Hinv : ItemSetInvariant (ArrSet (newItem :: arr)) :=
    item_set_invariant_push arr newItem (yai_item_set_inv _ Harr) (yai_closed _ Harr)
      (iiv_origin_lt _ Hvalid) (iiv_reachable _ Hvalid) Hsameid.
  have HleftIdx : (-1 <= leftIdx)%Z := findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfindL.
  have HRsize : (rightIdx <= Z.of_nat (length arr))%Z := findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfindR.
  have HleftR : (leftIdx < rightIdx)%Z :=
    @YjsLt'_findPtrIdx_lt _ EqDA arr (origin newItem) (rightOrigin newItem) leftIdx rightIdx
      Harr Horig_set Hror_set (iiv_origin_lt _ Hvalid) HfindL HfindR.
  (* the constructed item equals newItem *)
  have [o [r [id [c [Hnewdef [HoLp [HoRp [Hid Hc]]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
  have Hitem : item = newItem.
  { move: Hmk; rewrite /mkItemByIndex.
    have [lptr [Hgl HLl]] := findLeftIdx_getElemExcept arr input leftIdx HfindLeft.
    have [rptr [Hgr HRr]] := findRightIdx_getElemExcept arr input rightIdx HfindRight.
    rewrite Hgl Hgr /=.
    have Hlo : lptr = o := isLeftIdPtr_unique arr (in_originId input) lptr o HLl HoLp.
    have Hro : rptr = r := isRightIdPtr_unique arr (in_rightOriginId input) rptr r HRr HoRp.
    move=> [= <-]; by rewrite Hlo Hro Hnewdef Hid Hc. }
  (* loop spec on the initial invariant *)
  have Hidnew : item_id newItem = in_id input by rewrite Hnewdef /=.
  move: HfindIdx; rewrite /findIntegratedIndex => /bind_Some [dval [Hfii [= Hdestdef]]].
  have Hcideq : clientId (in_id input) = clientId (item_id newItem) by rewrite Hidnew.
  rewrite Hcideq in Hfii.
  (* P1 base: everything at/before leftIdx is < newItem *)
  have HP1base : forall k y, (Z.of_nat k < leftIdx + 1)%Z -> arr !! k = Some y ->
      YjsLt' (itemPtr y) (itemPtr newItem).
  { move=> k y Hk Hy.
    have Hkleft : (Z.of_nat k <= leftIdx)%Z by lia.
    have Hl0 : (0 <= leftIdx)%Z by lia.
    have Hlsz : (Z.to_nat leftIdx < length arr)%nat by lia.
    have HH := @findPtrIdx_lt_size_getElem _ EqDA arr (origin newItem) leftIdx HfindL Hl0 Hlsz.
    destruct (arr !! Z.to_nat leftIdx) as [oitm|] eqn:Hoitm; last by [].
    move: HH; rewrite /= => -[Hooe].
    have Hkle : (k <= Z.to_nat leftIdx)%nat by lia.
    have Hyle : YjsLeq' (itemPtr y) (itemPtr oitm) :=
      getElem_leq_YjsLeq' arr k (Z.to_nat leftIdx) y oitm Harr Hy Hoitm Hkle.
    apply: (yjs_leq'_p_trans1 Hinv (itemPtr y) (itemPtr oitm) (itemPtr newItem)
      (arrset_mem arr newItem y (list_elem_of_lookup_2 _ _ _ Hy))
      (arrset_mem arr newItem oitm (list_elem_of_lookup_2 _ _ _ Hoitm))
      (arrset_new arr newItem) Hclosed Hyle).
    rewrite Hooe; exact: (item_origin_lt newItem). }
  have Hlinv : LInv arr newItem leftIdx 1 false (leftIdx + 1)%Z.
  { rewrite /LInv; split_and!.
    - lia.
    - simpl; lia.
    - exact HP1base.
    - move=> k yk Hk1 Hk2 Hyk; simpl in Hk2; exfalso; lia.
    - done.
    - move=> _; simpl; lia. }
  have Hcount : (leftIdx + Z.of_nat 1 + Z.of_nat (Z.to_nat (rightIdx - leftIdx) - 1) = rightIdx)%Z by lia.
  have [HC1 HC2] := fii_loop_spec arr newItem leftIdx rightIdx Hclosed Hinv Harr Hmax
    HfindL HfindR HleftIdx HleftR HRsize (Z.to_nat (rightIdx - leftIdx) - 1) 1 false (leftIdx + 1)%Z dval
    Hcount Hlinv Hfii.
  (* assemble *)
  have Hdvalpos : (0 <= dval)%Z by (have := fii_loop_bounds (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
      (clientId (item_id newItem)) arr false (leftIdx + 1)%Z dval HleftIdx ltac:(lia) ltac:(lia) Hcount Hfii; lia).
  have Hdvalsz : (dval <= rightIdx)%Z by (have := fii_loop_bounds (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
      (clientId (item_id newItem)) arr false (leftIdx + 1)%Z dval HleftIdx ltac:(lia) ltac:(lia) Hcount Hfii; lia).
  exists destIdx; split_and!.
  - subst destIdx; lia.
  - by rewrite Hitem.
  - rewrite Hitem; subst destIdx.
    apply: (YjsArrInvariant_insertIdxIfInBounds arr newItem (Z.to_nat dval) Hclosed Hinv Harr).
    + lia.
    + move=> y Hipos Hy; apply: (HC1 (Z.to_nat dval - 1) y _ Hy); lia.
    + move=> y Hy; exact: (HC2 y Hy).
    + move=> a Ha Haid.
      have Hcc : clientId (item_id a) = clientId (item_id newItem) by rewrite Haid.
      have := Hmax a Ha Hcc; rewrite Haid; lia.
Qed.

(** Clock-safety of the input is exactly clock-maximality of the resolved item. *)
Lemma isClockSafe_maximalId (input : IntegrateInput) (arr : list (YjsItem A)) (newItem : YjsItem A) :
  toItem input arr = Some newItem ->
  isClockSafe (in_id input) arr = true ->
  maximalId newItem arr.
Proof using A EqDA.
  move=> Htoitem Hcs x Hx Hcc.
  have [o [r [id [c [Hnewdef [_ [_ [Hid _]]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
  have Hidnew : item_id newItem = in_id input by rewrite Hnewdef /=.
  move: Hcs; rewrite /isClockSafe => Hcs.
  have Hforall : Forall (fun item => Is_true (implb (bool_decide (clientId (item_id item) = clientId (in_id input)))
      (bool_decide (clock (item_id item) < clock (in_id input))))) arr by (apply/forallb_True; by rewrite Hcs).
  move: Hforall => /Forall_forall Hforall.
  have Hgx := Hforall x Hx.
  have HP1 : bool_decide (clientId (item_id x) = clientId (in_id input)) = true
    by (apply bool_decide_eq_true; rewrite -Hidnew; exact Hcc).
  rewrite HP1 /= in Hgx.
  move: Hgx => /Is_true_eq_true /bool_decide_eq_true Hclk.
  rewrite Hidnew; exact Hclk.
Qed.

Theorem YjsArrInvariant_integrateSafe (input : IntegrateInput) (arr newArr : list (YjsItem A))
    (newItem : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  integrateSafe input arr = Some newArr ->
  exists i, (i <= length arr)%nat /\ newArr = insertIdxIfInBounds i newItem arr /\ YjsArrInvariant newArr.
Proof using A EqDA.
  move=> Harr Htoitem Hvalid Hint.
  move: Hint; rewrite /integrateSafe.
  destruct (isClockSafe (in_id input) arr) eqn:Hcs; last by (move=> H; discriminate H).
  move=> Hint.
  apply: (YjsArrInvariant_integrate input arr newArr newItem Harr Htoitem Hvalid _ Hint).
  exact: (isClockSafe_maximalId input arr newItem Htoitem Hcs).
Qed.

Theorem YjsStateInvariant_insert (s newS : YjsState A) (input : IntegrateInput) (newItem : YjsItem A) :
  YjsStateInvariant s ->
  toItem input (st_items s) = Some newItem ->
  IsItemValid newItem ->
  YjsState_insert s input = Some newS ->
  YjsStateInvariant newS.
Proof using A EqDA.
  rewrite /YjsStateInvariant /YjsState_insert.
  move=> Hsinv Htoitem Hvalid /bind_Some [newArr [Hint [= <-]]].
  have [i [_ [_ Hinv]]] := YjsArrInvariant_integrateSafe input (st_items s) newArr newItem Hsinv Htoitem Hvalid Hint.
  exact Hinv.
Qed.

End integrate.

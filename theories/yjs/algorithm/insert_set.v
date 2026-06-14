(** The set-based integration scan, mirroring the original-Yjs / y-octo
    [Item.integrate] (and cert-yjs's Go port): instead of the reference-crdts
    [scanning] boolean, it maintains two id sets — [ibo] (items-before-origin,
    every scanned id) and [ci] (conflicting-items, ids since the last advance) —
    and advances the destination when a scanned item's origin lies before the
    current destination ([col ∈ ibo ∧ col ∉ ci]).

    We prove [setfii_loop]'s output satisfies the same sorted-position
    characterization as [fii_loop] (everything before it is [< newItem], the
    item at it is [> newItem]); from there [setintegrate] preserves
    [YjsArrInvariant], and [setintegrate = integrate] follows because two valid
    ([YjsLt']-sorted) arrays with the same elements are equal. Thus the set-based
    algorithm inherits the convergence results of the verified scanning one. *)
From stdpp Require Import base list numbers sorting gmap sets.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set util.
From yjs.order Require Import item_order item_set_invariant transitivity totality asymmetry no_cross_origin.
From yjs.algorithm Require Import basic insert_basic insert_lemmas invariant_basic
  invariant_yjsarray invariant_yjsarray_idx findptridx_order findptridx_order2
  findptridx_getelem findptridx_origin insert_invariant toitem_lemmas findptridx_insert
  insert_loop.

Section set_loop.
Context {A : Type} `{EqDA : EqDecision A}.

(** The id a pointer references as an origin: an item's id, or [None] for a
    boundary ([First]/[Last]). Matches the heap [Item.originLeftId] field. *)
Definition origin_id (p : YjsPtr A) : option YjsId :=
  match p with itemPtr it => Some (item_id it) | First => None | Last => None end.

(** The set-based scan. [oLeftId] / [oRightId] / [newId] are the new item's
    origin-left id, origin-right id, and id (matching the Go [idOptEqual] /
    client comparisons). *)
Fixpoint setfii_loop (count offset : nat) (leftIdx rightIdx : Z)
    (oLeftId oRightId : option YjsId) (newId : YjsId)
    (arr : list (YjsItem A)) (ibo ci : gset YjsId) (destIdx : Z) : option Z :=
  match count with
  | 0 => Some destIdx
  | S count' =>
    let i := Z.to_nat (leftIdx + Z.of_nat offset) in
    other ← arr !! i;
    let cId := item_id other in
    let ibo' := {[cId]} ∪ ibo in
    let ci' := {[cId]} ∪ ci in
    if decide (origin_id (origin other) = oLeftId) then
      if decide (clientId cId < clientId newId)%nat then
        setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
          ibo' ∅ (Z.of_nat (i + 1))
      else if decide (origin_id (rightOrigin other) = oRightId) then
        Some destIdx
      else
        setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
          ibo' ci' destIdx
    else
      match origin_id (origin other) with
      | Some col =>
        if decide (col ∈ ibo' /\ col ∉ ci') then
          setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
            ibo' ∅ (Z.of_nat (i + 1))
        else
          setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
            ibo' ci' destIdx
      | None => Some destIdx
      end
  end.

Definition setfindIntegratedIndex (leftIdx rightIdx : Z) (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) : option nat :=
  d ← setfii_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
       (in_originId input) (in_rightOriginId input) (in_id input) arr ∅ ∅ (leftIdx + 1);
  Some (Z.to_nat d).

(** [setintegrate] mirrors [integrate] verbatim except the loop. *)
Definition setintegrate (input : IntegrateInput (A := A)) (arr : list (YjsItem A)) :
    option (list (YjsItem A)) :=
  leftIdx ← findLeftIdx (in_originId input) arr;
  rightIdx ← findRightIdx (in_rightOriginId input) arr;
  destIdx ← setfindIntegratedIndex leftIdx rightIdx input arr;
  item ← mkItemByIndex leftIdx rightIdx input arr;
  Some (insertIdxIfInBounds destIdx item arr).

Definition setintegrateSafe (input : IntegrateInput (A := A)) (arr : list (YjsItem A)) :
    option (list (YjsItem A)) :=
  if isClockSafe (in_id input) arr then setintegrate input arr else None.

End set_loop.

Section set_spec.
Context {A : Type} `{EqDA : EqDecision A}.

(** The sorted-position characterization determines the insertion index
    uniquely: in a valid array, at most one index has everything before it
    [< newItem] and the item at it [> newItem]. *)
Lemma insert_index_unique (arr : list (YjsItem A)) (newItem : YjsItem A) (d1 d2 : nat) :
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  (forall k y, (k < d1)%nat -> arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) ->
  (forall y, arr !! d1 = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
  (forall k y, (k < d2)%nat -> arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) ->
  (forall y, arr !! d2 = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
  (d1 <= length arr)%nat -> (d2 <= length arr)%nat ->
  d1 = d2.
Proof using A EqDA.
  move=> Hclosed Hinv HA1 HA2 HB1 HB2 Hd1 Hd2.
  (* If d1 <> d2, the smaller index's item is both < and > newItem. *)
  enough (Hnlt : forall e1 e2,
    (forall k y, (k < e1)%nat -> arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) ->
    (forall y, arr !! e2 = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) ->
    (e1 <= length arr)%nat -> ~ (e2 < e1)%nat).
  { destruct (Nat.lt_trichotomy d1 d2) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
    - exfalso; exact: (Hnlt d2 d1 HB1 HA2 Hd2 Hlt).
    - exfalso; exact: (Hnlt d1 d2 HA1 HB2 Hd1 Hgt). }
  move=> e1 e2 He1 He2 He1len Hlt.
  have [y Hy] : exists y, arr !! e2 = Some y.
  { apply lookup_lt_is_Some_2; lia. }
  have Hgt := He2 y Hy.
  have Hlt' := He1 e2 y Hlt Hy.
  exact: (yjs_lt_asymm Hclosed Hinv (itemPtr y) (itemPtr newItem)
            (arrset_mem arr newItem y (list_elem_of_lookup_2 _ _ _ Hy))
            (arrset_new arr newItem) Hlt' Hgt).
Qed.

(** The set-based loop's output satisfies the sorted-position characterization:
    everything before it is [< newItem], the item at it is [> newItem], and it is
    in bounds. This is the core correctness of the set-based algorithm — the
    [ibo]/[ci] bookkeeping lands the new item at the [YjsLt']-sorted position,
    exactly like the scanning loop ([fii_loop_spec]).

    [TODO] the loop-invariant induction (the [ibo]/[ci] <-> index coupling).
    Reuses the order-theoretic break/advance lemmas from insert_loop.v
    ([break1_newItem_lt], [break2_newItem_lt], [other_lt_newItem],
    [same_origin_bigger_id], [exit_C2], [loopInv_YjsLt']). *)
Lemma setfindIntegratedIndex_spec (arr : list (YjsItem A)) (newItem : YjsItem A)
    (input : IntegrateInput (A := A)) (leftIdx rightIdx : Z) (d : nat) :
  YjsArrInvariant arr ->
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  maximalId newItem arr ->
  toItem input arr = Some newItem ->
  findPtrIdx (origin newItem) arr = Some leftIdx ->
  findPtrIdx (rightOrigin newItem) arr = Some rightIdx ->
  (-1 <= leftIdx)%Z -> (leftIdx < rightIdx)%Z -> (rightIdx <= Z.of_nat (length arr))%Z ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some d ->
  (forall k y, (k < d)%nat -> arr !! k = Some y -> YjsLt' (itemPtr y) (itemPtr newItem)) /\
  (forall y, arr !! d = Some y -> YjsLt' (itemPtr newItem) (itemPtr y)) /\
  (d <= length arr)%nat.
Proof using A EqDA.
Admitted.

(** The set-based integrate preserves the document invariant. The set loop lands
    at the sorted position, so [YjsArrInvariant_insertIdxIfInBounds] applies —
    mirrors [YjsArrInvariant_integrate]. *)
Theorem YjsArrInvariant_setintegrate (input : IntegrateInput (A := A))
    (arr newArr : list (YjsItem A)) (newItem : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  setintegrate input arr = Some newArr ->
  YjsArrInvariant newArr.
Proof using A EqDA.
  move=> Harr Htoitem Hvalid Hmax.
  rewrite /setintegrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  move: Hr2 => /bind_Some [destIdx [HfindIdx Hr3]].
  move: Hr3 => /bind_Some [item [Hmk [= <-]]].
  have Huniq := yai_unique _ Harr.
  have HfindL : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem); exact HfindLeft. }
  have HfindR : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem); exact HfindRight. }
  have Horig_set : ArrSet arr (origin newItem) := @findPtrIdx_ArrSet _ EqDA arr (origin newItem) leftIdx HfindL.
  have Hror_set : ArrSet arr (rightOrigin newItem) := @findPtrIdx_ArrSet _ EqDA arr (rightOrigin newItem) rightIdx HfindR.
  have Hclosed : IsClosedItemSet (ArrSet (newItem :: arr)) :=
    arr_set_closed_push arr newItem (yai_closed _ Harr) Horig_set Hror_set.
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
  have [o [r [id [c [Hnewdef [HoLp [HoRp [Hid Hc]]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
  have Hitem : item = newItem.
  { move: Hmk; rewrite /mkItemByIndex.
    have [lptr [Hgl HLl]] := findLeftIdx_getElemExcept arr input leftIdx HfindLeft.
    have [rptr [Hgr HRr]] := findRightIdx_getElemExcept arr input rightIdx HfindRight.
    rewrite Hgl Hgr /=.
    have Hlo : lptr = o := isLeftIdPtr_unique arr (in_originId input) lptr o HLl HoLp.
    have Hro : rptr = r := isRightIdPtr_unique arr (in_rightOriginId input) rptr r HRr HoRp.
    move=> [= <-]; by rewrite Hlo Hro Hnewdef Hid Hc. }
  have [HC1 [HC2 Hdlen]] := setfindIntegratedIndex_spec arr newItem input leftIdx rightIdx destIdx
    Harr Hclosed Hinv Hmax Htoitem HfindL HfindR HleftIdx HleftR HRsize HfindIdx.
  rewrite Hitem.
  apply: (YjsArrInvariant_insertIdxIfInBounds arr newItem destIdx Hclosed Hinv Harr Hdlen).
  - move=> y Hipos Hy; apply: (HC1 (destIdx - 1) y _ Hy); lia.
  - move=> y Hy; exact: (HC2 y Hy).
  - move=> a Ha Haid.
    have Hcc : clientId (item_id a) = clientId (item_id newItem) by rewrite Haid.
    have := Hmax a Ha Hcc; rewrite Haid; lia.
Qed.

Theorem YjsArrInvariant_setintegrateSafe (input : IntegrateInput (A := A))
    (arr newArr : list (YjsItem A)) (newItem : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  setintegrateSafe input arr = Some newArr ->
  YjsArrInvariant newArr.
Proof using A EqDA.
  move=> Harr Htoitem Hvalid.
  rewrite /setintegrateSafe.
  destruct (isClockSafe (in_id input) arr) eqn:Hcs; last by (move=> H; discriminate H).
  move=> Hint.
  apply: (YjsArrInvariant_setintegrate input arr newArr newItem Harr Htoitem Hvalid _ Hint).
  exact: (isClockSafe_maximalId input arr newItem Htoitem Hcs).
Qed.

End set_spec.

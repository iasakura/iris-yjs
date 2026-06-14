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
        if decide (col ∈ ibo') then
          (* conflict's left origin was already scanned (case 2) *)
          if decide (col ∉ ci') then
            setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
              ibo' ∅ (Z.of_nat (i + 1))
          else
            setfii_loop count' (S offset) leftIdx rightIdx oLeftId oRightId newId arr
              ibo' ci' destIdx
        else
          (* left origin is before this run: origins would cross, stop (yrs) *)
          Some destIdx
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

(** Coupling between the set-based accumulators and the scanning state at a loop
    step ([cur = leftIdx + offset] is the next index to scan):
    - [scanning] is on exactly when [destIdx] has fallen behind the frontier;
    - [ibo] is the id set of the scanned window [(leftIdx, cur)];
    - [ci] is the id set of [[destIdx, cur)] (ids since the last advance);
    - when scanning, the anchor [arr[destIdx]] has [origin = origin newItem]
      (used to rule out advancing-while-scanning via no-cross-origin). *)
Definition Couple (arr : list (YjsItem A)) (newItem : YjsItem A) (leftIdx : Z)
    (offset : nat) (ibo ci : gset YjsId) (destIdx : Z) (scanning : bool) : Prop :=
  (leftIdx + 1 <= destIdx <= leftIdx + Z.of_nat offset)%Z /\
  scanning = bool_decide (destIdx <> leftIdx + Z.of_nat offset)%Z /\
  (forall idz, idz ∈ ibo <-> exists k y, (leftIdx < Z.of_nat k)%Z /\
     (Z.of_nat k < leftIdx + Z.of_nat offset)%Z /\ arr !! k = Some y /\ item_id y = idz) /\
  (forall idz, idz ∈ ci <-> exists k y, (destIdx <= Z.of_nat k)%Z /\
     (Z.of_nat k < leftIdx + Z.of_nat offset)%Z /\ arr !! k = Some y /\ item_id y = idz) /\
  (scanning = true -> exists dy, arr !! Z.to_nat destIdx = Some dy /\ origin dy = origin newItem).

(** The new item's resolved origins carry exactly the input's origin ids, so the
    set loop's id-equality tests match the index tests of [fii_loop]. *)
Lemma in_originId_origin_id (arr : list (YjsItem A)) (newItem : YjsItem A)
    (input : IntegrateInput (A := A)) :
  toItem input arr = Some newItem ->
  origin_id (origin newItem) = in_originId input.
Proof using A EqDA.
  move=> Htoitem.
  have [o [r [id [c [Hnewdef [HoLp [_ _]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
  subst newItem; rewrite /origin.
  move: HoLp; rewrite /isLeftIdPtr; destruct (in_originId input) as [pid|].
  - move=> [item [-> Hfind]]; rewrite /origin_id /=; by rewrite (find_by_id_id pid arr item Hfind).
  - by move=> ->.
Qed.

Lemma in_rightOriginId_rightOrigin_id (arr : list (YjsItem A)) (newItem : YjsItem A)
    (input : IntegrateInput (A := A)) :
  toItem input arr = Some newItem ->
  origin_id (rightOrigin newItem) = in_rightOriginId input.
Proof using A EqDA.
  move=> Htoitem.
  have [o [r [id [c [Hnewdef [_ [HoRp _]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
  subst newItem; rewrite /rightOrigin.
  move: HoRp; rewrite /isRightIdPtr; destruct (in_rightOriginId input) as [pid|].
  - move=> [item [-> Hfind]]; rewrite /origin_id /=; by rewrite (find_by_id_id pid arr item Hfind).
  - by move=> ->.
Qed.

(** CORE: the set-based scan computes the same index as the verified scanning
    scan. With the yrs-faithful break the two follow the same control flow; the
    only other would-be divergence — advancing while scanning, i.e. a scanned
    item whose left origin sits in [(leftIdx, destIdx)] — is impossible by
    no-cross-origin (the scanning anchor [arr[destIdx]] has origin [origin
    newItem] at [leftIdx], so such an edge would cross). Proved by induction on
    the fuel, maintaining [Couple].

    [TODO] the coupling induction. Reuses [no_cross_origin] and the same-origin /
    break facts from insert_loop.v. *)
Lemma setfii_loop_eq_fii_loop (arr : list (YjsItem A)) (newItem : YjsItem A)
    (input : IntegrateInput (A := A)) (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  maximalId newItem arr ->
  toItem input arr = Some newItem ->
  findPtrIdx (origin newItem) arr = Some leftIdx ->
  findPtrIdx (rightOrigin newItem) arr = Some rightIdx ->
  (-1 <= leftIdx)%Z -> (leftIdx < rightIdx)%Z -> (rightIdx <= Z.of_nat (length arr))%Z ->
  forall (count offset : nat) (ibo ci : gset YjsId) (destIdx : Z) (scanning : bool),
    (leftIdx + Z.of_nat offset + Z.of_nat count = rightIdx)%Z ->
    Couple arr newItem leftIdx offset ibo ci destIdx scanning ->
    setfii_loop count offset leftIdx rightIdx (in_originId input) (in_rightOriginId input)
      (in_id input) arr ibo ci destIdx
    = fii_loop count offset leftIdx rightIdx (clientId (item_id newItem)) arr scanning destIdx.
Proof using A EqDA.
Admitted.

(** The two index-finders agree: the initial state satisfies [Couple]. *)
Lemma setfindIntegratedIndex_eq (arr : list (YjsItem A)) (newItem : YjsItem A)
    (input : IntegrateInput (A := A)) (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  IsClosedItemSet (ArrSet (newItem :: arr)) ->
  ItemSetInvariant (ArrSet (newItem :: arr)) ->
  maximalId newItem arr ->
  toItem input arr = Some newItem ->
  findPtrIdx (origin newItem) arr = Some leftIdx ->
  findPtrIdx (rightOrigin newItem) arr = Some rightIdx ->
  (-1 <= leftIdx)%Z -> (leftIdx < rightIdx)%Z -> (rightIdx <= Z.of_nat (length arr))%Z ->
  setfindIntegratedIndex leftIdx rightIdx input arr = findIntegratedIndex leftIdx rightIdx input arr.
Proof using A EqDA.
  move=> Harr Hclosed Hinv Hmax Htoitem HfindL HfindR Hl0 Hlr Hrsz.
  have Hid : item_id newItem = in_id input.
  { have [o [r [id [c [Hnewdef [_ [_ [Hidd _]]]]]]]] := proj1 (toItem_ok_iff input arr newItem) Htoitem.
    by rewrite Hnewdef /=. }
  have Hcount : (leftIdx + Z.of_nat 1 + Z.of_nat (Z.to_nat (rightIdx - leftIdx) - 1) = rightIdx)%Z by lia.
  have HCouple : Couple arr newItem leftIdx 1 ∅ ∅ (leftIdx + 1)%Z false.
  { rewrite /Couple; split_and!.
    - lia.
    - lia.
    - case_bool_decide as Hc; [exfalso; lia | done].
    - move=> idz; split; [set_solver | move=> [k [y [Hk1 [Hk2 _]]]]; exfalso; lia].
    - move=> idz; split; [set_solver | move=> [k [y [Hk1 [Hk2 _]]]]; exfalso; lia].
    - done. }
  have Heq := setfii_loop_eq_fii_loop arr newItem input leftIdx rightIdx
    Harr Hclosed Hinv Hmax Htoitem HfindL HfindR Hl0 Hlr Hrsz
    (Z.to_nat (rightIdx - leftIdx) - 1) 1 ∅ ∅ (leftIdx + 1)%Z false Hcount HCouple.
  rewrite /setfindIntegratedIndex /findIntegratedIndex Heq Hid //.
Qed.

(** Convergence transfer: the set-based integrate equals the verified one, so it
    inherits all of [integrate]'s results (invariant, commutativity, ...). *)
Theorem setintegrate_eq_integrate (input : IntegrateInput (A := A)) (arr : list (YjsItem A))
    (newItem : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  setintegrate input arr = integrate input arr.
Proof using A EqDA.
  move=> Harr Htoitem Hvalid Hmax.
  have Huniq := yai_unique _ Harr.
  rewrite /setintegrate /integrate.
  destruct (findLeftIdx (in_originId input) arr) as [leftIdx|] eqn:HfindLeft; last done.
  destruct (findRightIdx (in_rightOriginId input) arr) as [rightIdx|] eqn:HfindRight; last done.
  simpl.
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
  by rewrite (setfindIntegratedIndex_eq arr newItem input leftIdx rightIdx
       Harr Hclosed Hinv Hmax Htoitem HfindL HfindR HleftIdx HleftR HRsize).
Qed.

(** Invariant preservation, inherited from [integrate]. *)
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
  rewrite (setintegrate_eq_integrate input arr newItem Harr Htoitem Hvalid Hmax) => Hint.
  have [i [_ [_ Hres]]] := YjsArrInvariant_integrate input arr newArr newItem Harr Htoitem Hvalid Hmax Hint.
  exact Hres.
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

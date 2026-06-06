(** The key conflict-resolution step: if [newItem]'s origin sits no later than
    [other]'s origin (with id tie-break) and the reachability bounds hold, then
    [other] precedes [newItem] in the document order. Port of
    [findPtrIdx_origin_leq_newItem_YjsLt'] from
    [LeanYjs/Algorithm/Invariant/YjsArray.lean]. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant totality.
From yjs.algorithm Require Import basic insert_basic insert_lemmas
  invariant_basic invariant_yjsarray findptridx_order.

Section origin.
Context {A : Type} `{EqDA : EqDecision A}.

Lemma findPtrIdx_origin_leq_newItem_YjsLt'
    (ls arr : list (YjsItem A)) (other newItem : YjsItem A)
    (leftIdx rightIdx oLeftIdx oRightIdx : Z) :
  (forall i, i ∈ arr -> i ∈ ls) ->
  newItem ∈ ls ->
  other ∈ ls ->
  IsClosedItemSet (ArrSet ls) ->
  ItemSetInvariant (ArrSet ls) ->
  YjsArrInvariant arr ->
  findPtrIdx (origin newItem) arr = Some leftIdx ->
  findPtrIdx (rightOrigin newItem) arr = Some rightIdx ->
  findPtrIdx (origin other) arr = Some oLeftIdx ->
  findPtrIdx (rightOrigin other) arr = Some oRightIdx ->
  YjsLt' (origin newItem) (itemPtr other) ->
  YjsLt' (itemPtr other) (rightOrigin newItem) ->
  (leftIdx <= oLeftIdx)%Z ->
  (leftIdx = oLeftIdx -> YjsId_lt (item_id other) (item_id newItem)) ->
  YjsLt' (origin other) (itemPtr newItem) ->
  YjsLt' (itemPtr other) (itemPtr newItem).
Proof using A EqDA.
  move=> hsub hnew_in hoth_in hclosed hsetinv hinv
         hfindL hfindR hfindOL hfindOR
         hno_lt_other hother_lt_nr hleL hleL_eq hoo_lt_new.
  (* Compare [other]'s right origin against [newItem] in the closed set. *)
  have hRO : ArrSet ls (rightOrigin other) := right_origin_p_valid hclosed other hoth_in.
  have hor : YjsLeq' (rightOrigin other) (itemPtr newItem)
             \/ YjsLt' (itemPtr newItem) (rightOrigin other)
    := yjs_lt_total hsetinv hclosed (rightOrigin other) (itemPtr newItem) hRO hnew_in.
  case: hor => [hle | hlt].
  - (* [other] reaches up to [newItem] via its right origin. *)
    destruct other as [oo orr oid oc].
    apply: (YjsLt'_ltRightOrigin oo orr oid oc (itemPtr newItem)); exact: hle.
  - destruct (decide (leftIdx = oLeftIdx)) as [Heq | Hne].
    + (* Origins coincide: resolve by id (ltOriginSame). *)
      have hid : YjsId_lt (item_id other) (item_id newItem) := hleL_eq Heq.
      have heq_origin : origin newItem = origin other.
      { apply: (findPtrIdx_eq_ok_inj arr (origin newItem) (origin other) leftIdx hfindL).
        rewrite Heq; exact: hfindOL. }
      destruct other as [oo orr oid oc]; destruct newItem as [no nr nid nc].
      simpl in heq_origin; subst no.
      apply: YjsLt'_ltConflict.
      apply: (ConflictLt'_ltOriginSame oo orr nr oid nid oc nc);
        [exact: hother_lt_nr | exact: hlt | exact: hid].
    + (* [newItem]'s origin strictly precedes [other]'s (ltOriginDiff). *)
      have Hlt' : (leftIdx < oLeftIdx)%Z by lia.
      have heq_origin : YjsLt' (origin newItem) (origin other) :=
        findPtrIdx_lt_YjsLt' arr (origin newItem) (origin other) leftIdx oLeftIdx
          hinv hfindL hfindOL Hlt'.
      destruct other as [oo orr oid oc]; destruct newItem as [no nr nid nc].
      apply: YjsLt'_ltConflict.
      apply: (ConflictLt'_ltOriginDiff oo no orr nr oid nid oc nc);
        [exact: heq_origin | exact: hother_lt_nr | exact: hoo_lt_new | exact: hlt].
Qed.

End origin.

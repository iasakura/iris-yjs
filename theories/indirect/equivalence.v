(** Equivalence of the indirect (by-id) algorithm with the verified direct
    (structural) one. Port of [LeanYjs/Indirect/Algorithm/Equivalence.lean].
    The key bridge [findRefIdx_ofDirectPtr_exact] says a by-id lookup of an
    erased pointer equals the structural lookup (using id-uniqueness); the loop
    [ifii_loop] then runs identically to the direct [fii_loop], so [iintegrate]
    on an erased array equals the erasure of [integrate]. *)
From stdpp Require Import base numbers list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set.
From yjs.order Require Import item_order item_set_invariant.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray toitem_lemmas findptridx_insert delete.
From yjs.indirect Require Import item basic insert_basic delete.

Section equivalence.
Context {A : Type} `{EqDA : EqDecision A}.

(** [fst] commutes through the [prod_map id _] that [list_find_fmap] produces. *)
Lemma fst_fmap_prod_map (Y : option (nat * YjsItem A)) :
  fst <$> (prod_map id ofDirectItem <$> Y) = fst <$> Y.
Proof. by case: Y => [[i x]|]. Qed.

(** A by-id lookup of an erased pointer equals the structural lookup. *)
Lemma findRefIdx_ofDirectPtr_exact (arr : list (YjsItem A)) (ptr : YjsPtr A) :
  uniqueId arr -> ArrSet arr ptr ->
  findRefIdx (ofDirectPtr ptr) (ofDirectItem <$> arr) = findPtrIdx ptr arr.
Proof using A EqDA.
  move=> Huniq Hptr.
  destruct ptr as [item | |].
  - have Hitem : item ∈ arr by move: Hptr; rewrite /ArrSet.
    rewrite /ofDirectPtr /findRefIdx /findPtrIdx /find_item_idx.
    f_equal.
    rewrite list_find_fmap fst_fmap_prod_map.
    have Hagree : forall a, a ∈ arr ->
        (((fun i => iid i = item_id item) ∘ ofDirectItem) a <-> (fun i => i = item) a).
    { move=> a Ha; rewrite /compose /=; split.
      - move=> Hid; exact: (uniqueId_id_eq_implies_eq arr Huniq a item Ha Hitem Hid).
      - by move=> ->. }
    by rewrite (list_find_ext_in _ _ arr Hagree).
  - by [].
  - by rewrite /ofDirectPtr /findRefIdx /findPtrIdx length_fmap.
Qed.

(** The find-left / find-right index lookups agree (no uniqueness needed — the
    erased predicate reduces to the direct one). *)
Lemma ifindLeftIdx_ofDirect (oid : option YjsId) (arr : list (YjsItem A)) :
  ifindLeftIdx oid (ofDirectItem <$> arr) = findLeftIdx oid arr.
Proof using A EqDA.
  rewrite /ifindLeftIdx /findLeftIdx; destruct oid as [id|]; last done.
  by f_equal; rewrite list_find_fmap fst_fmap_prod_map.
Qed.

Lemma ifindRightIdx_ofDirect (rid : option YjsId) (arr : list (YjsItem A)) :
  ifindRightIdx rid (ofDirectItem <$> arr) = findRightIdx rid arr.
Proof using A EqDA.
  rewrite /ifindRightIdx /findRightIdx; destruct rid as [id|].
  - by f_equal; rewrite list_find_fmap fst_fmap_prod_map.
  - by rewrite length_fmap.
Qed.

(** Clock-safety agrees. *)
Lemma iisClockSafe_ofDirect (id : YjsId) (arr : list (YjsItem A)) :
  iisClockSafe id (ofDirectItem <$> arr) = isClockSafe id arr.
Proof using A EqDA.
  rewrite /iisClockSafe /isClockSafe; elim: arr => [|x arr IH] //=; by rewrite IH.
Qed.

(** Delete commutes with erasure. *)
Lemma ideleteById_ofDirect (s : YjsState A) (id : YjsId) :
  ideleteById (ofDirectState s) id = ofDirectState (deleteById s id).
Proof using A. by []. Qed.

(** The scanning loop runs identically on an erased array (each step's by-id
    origin / right-origin resolution matches the structural one, using the
    invariant's closure + uniqueness). *)
Lemma ifii_loop_ofDirect (arr : list (YjsItem A)) (Harr : YjsArrInvariant arr) :
  forall (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (scanning : bool) (destIdx : Z),
  ifii_loop count offset leftIdx rightIdx cid (ofDirectItem <$> arr) scanning destIdx
    = fii_loop count offset leftIdx rightIdx cid arr scanning destIdx.
Proof using A EqDA.
  have Huniq := yai_unique _ Harr.
  have Hclosed := yai_closed _ Harr.
  elim => [|count' IH] offset leftIdx rightIdx cid scanning destIdx //=.
  rewrite /igetElemExcept /getElemExcept list_lookup_fmap.
  case Hother: (arr !! Z.to_nat (leftIdx + Z.of_nat offset)) => [other|] //=.
  have Hmem : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hother.
  have HoL : ArrSet arr (origin other) := origin_p_valid Hclosed other Hmem.
  have HoR : ArrSet arr (rightOrigin other) := right_origin_p_valid Hclosed other Hmem.
  rewrite (findRefIdx_ofDirectPtr_exact arr (origin other) Huniq HoL).
  case: (findPtrIdx (origin other) arr) => [oLeftIdx|] //=.
  rewrite (findRefIdx_ofDirectPtr_exact arr (rightOrigin other) Huniq HoR).
  case: (findPtrIdx (rightOrigin other) arr) => [oRightIdx|] //=.
  case: (decide (oLeftIdx < leftIdx)%Z) => // _.
  case: (decide (oLeftIdx = leftIdx)%Z) => _.
  - case: (decide (clientId (item_id other) < cid)%nat) => _; first exact: IH.
    case: (decide (oRightIdx = rightIdx)%Z) => _; [done | exact: IH].
  - exact: IH.
Qed.

(** The integrated index agrees. *)
Lemma ifindIntegratedIndex_ofDirect (leftIdx rightIdx : Z) (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (Harr : YjsArrInvariant arr) :
  ifindIntegratedIndex leftIdx rightIdx input (ofDirectItem <$> arr)
    = findIntegratedIndex leftIdx rightIdx input arr.
Proof using A EqDA.
  rewrite /ifindIntegratedIndex /findIntegratedIndex.
  by rewrite (ifii_loop_ofDirect arr Harr).
Qed.

(** An erased resolved pointer matches the input's origin / right-origin ref. *)
Lemma ofDirectPtr_isLeftIdPtr (arr : list (YjsItem A)) (oid : option YjsId) (p : YjsPtr A) :
  isLeftIdPtr arr oid p -> ofDirectPtr p = ofOriginId oid.
Proof using A EqDA.
  rewrite /isLeftIdPtr; destruct oid as [id|].
  - move=> [oit [-> Hfind]]; rewrite /ofDirectPtr /ofOriginId.
    by rewrite (@find_by_id_id _ EqDA id arr oit Hfind).
  - by move=> ->.
Qed.

Lemma ofDirectPtr_isRightIdPtr (arr : list (YjsItem A)) (rid : option YjsId) (p : YjsPtr A) :
  isRightIdPtr arr rid p -> ofDirectPtr p = ofRightOriginId rid.
Proof using A EqDA.
  rewrite /isRightIdPtr; destruct rid as [id|].
  - move=> [rit [-> Hfind]]; rewrite /ofDirectPtr /ofRightOriginId.
    by rewrite (@find_by_id_id _ EqDA id arr rit Hfind).
  - by move=> ->.
Qed.

(** The item the direct algorithm builds erases to the indirect [imkItem]. *)
Lemma ofDirectItem_mkItemByIndex (arr : list (YjsItem A)) (input : IntegrateInput (A := A))
    (leftIdx rightIdx : Z) :
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  exists item, mkItemByIndex leftIdx rightIdx input arr = Some item /\
    ofDirectItem item = imkItem input.
Proof using A EqDA.
  move=> Hleft Hright.
  have [lptr [Hgl HLl]] := findLeftIdx_getElemExcept arr input leftIdx Hleft.
  have [rptr [Hgr HRr]] := findRightIdx_getElemExcept arr input rightIdx Hright.
  exists (Item lptr rptr (in_id input) (in_content input)); split.
  - by rewrite /mkItemByIndex Hgl Hgr /=.
  - rewrite /ofDirectItem /imkItem /=.
    by rewrite (ofDirectPtr_isLeftIdPtr arr _ _ HLl) (ofDirectPtr_isRightIdPtr arr _ _ HRr).
Qed.

(** Erasure commutes with the in-bounds splice. *)
Lemma map_ofDirectItem_insertIdxIfInBounds (arr : list (YjsItem A)) (i : nat) (item : YjsItem A) :
  ofDirectItem <$> insertIdxIfInBounds i item arr
    = iinsertIdxIfInBounds i (ofDirectItem item) (ofDirectItem <$> arr).
Proof using A.
  rewrite /insertIdxIfInBounds /iinsertIdxIfInBounds length_fmap.
  case: (decide (i <= length arr)%nat) => Hi; last done.
  by rewrite fmap_app fmap_cons fmap_take fmap_drop.
Qed.

(** The integrate algorithms agree (up to erasure). *)
Lemma iintegrate_ofDirect (arr : list (YjsItem A)) (input : IntegrateInput (A := A))
    (Harr : YjsArrInvariant arr) :
  iintegrate input (ofDirectItem <$> arr)
    = (fun a : list (YjsItem A) => ofDirectItem <$> a) <$> integrate input arr.
Proof using A EqDA.
  rewrite /iintegrate /integrate ifindLeftIdx_ofDirect ifindRightIdx_ofDirect.
  case Hleft: (findLeftIdx (in_originId input) arr) => [leftIdx|] //=.
  case Hright: (findRightIdx (in_rightOriginId input) arr) => [rightIdx|] //=.
  rewrite (ifindIntegratedIndex_ofDirect leftIdx rightIdx input arr Harr).
  case Hdest: (findIntegratedIndex leftIdx rightIdx input arr) => [destIdx|] //=.
  have [item [Hmk Hof]] := ofDirectItem_mkItemByIndex arr input leftIdx rightIdx Hleft Hright.
  rewrite Hmk /= -Hof.
  by rewrite map_ofDirectItem_insertIdxIfInBounds.
Qed.

Lemma iintegrateSafe_ofDirect (arr : list (YjsItem A)) (input : IntegrateInput (A := A))
    (Harr : YjsArrInvariant arr) :
  iintegrateSafe input (ofDirectItem <$> arr)
    = (fun a : list (YjsItem A) => ofDirectItem <$> a) <$> integrateSafe input arr.
Proof using A EqDA.
  rewrite /iintegrateSafe /integrateSafe iisClockSafe_ofDirect.
  case: (isClockSafe (in_id input) arr); [exact: iintegrate_ofDirect | done].
Qed.

(** Insert commutes with erasure (the realistic by-id insert computes the
    erasure of the verified direct insert). *)
Theorem IYjsState_insert_ofDirect (s : YjsState A) (input : IntegrateInput (A := A))
    (hinv : YjsStateInvariant s) :
  IYjsState_insert (ofDirectState s) input = ofDirectState <$> YjsState_insert s input.
Proof using A EqDA.
  rewrite /IYjsState_insert /YjsState_insert /ofDirectState /=.
  rewrite (iintegrateSafe_ofDirect (st_items s) input hinv).
  by case: (integrateSafe input (st_items s)) => [newArr|].
Qed.

End equivalence.

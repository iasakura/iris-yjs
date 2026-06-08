(** Insert/insert commutativity (port of
    [LeanYjs/Algorithm/Commutativity/InsertInsert.lean]). This file begins with
    the foundational monotonicity lemmas for clock-maximality under array
    extension / insertion; the equational core ([integrate_integrate_eq_*],
    [insert_commutative]) builds on top. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray toitem_lemmas findptridx_insert insert_loop.

(** Inserting a non-matching element keeps a failed search failed. *)
Lemma list_find_insert_None {X} (P : X -> Prop) `{!∀ x, Decision (P x)}
    (l : list X) (i : nat) (y : X) :
  ¬ P y -> list_find P l = None -> list_find P (take i l ++ y :: drop i l) = None.
Proof.
  move=> Hy /list_find_None Hl.
  apply/list_find_None; apply/Forall_app; split; [exact: Forall_take|].
  apply/Forall_cons; split; [exact Hy | exact: Forall_drop].
Qed.

Section commutativity.
Context {A : Type} `{EqDA : EqDecision A}.

(** Clock-maximality transfers to a superset whose extra elements have a
    different client id. *)
Lemma maximalId_mono (arr1 arr2 : list (YjsItem A)) (x : YjsItem A) :
  (forall a, a ∈ arr1 -> a ∈ arr2) ->
  (forall a, a ∈ arr2 -> a ∉ arr1 -> clientId (item_id a) <> clientId (item_id x)) ->
  maximalId x arr1 ->
  maximalId x arr2.
Proof using A EqDA.
  move=> Hsub Hidneq Hmax y Hy2 Hideq.
  have Hy1 : y ∈ arr1.
  { destruct (decide (y ∈ arr1)) as [Hin|Hnin]; first exact Hin.
    exfalso; exact: (Hidneq y Hy2 Hnin Hideq). }
  exact: (Hmax y Hy1 Hideq).
Qed.

(** Inserting an item with a fresh client id preserves clock-maximality. *)
Lemma maximalId_insertIdxIfInBounds (arr : list (YjsItem A)) (a x : YjsItem A) (idx : nat) :
  maximalId x arr ->
  clientId (item_id a) <> clientId (item_id x) ->
  maximalId x (insertIdxIfInBounds idx a arr).
Proof using A EqDA.
  move=> Hmax Hane.
  rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [Hidx|Hidx]; last exact Hmax.
  apply: (maximalId_mono arr (take idx arr ++ a :: drop idx arr) x); [| |exact Hmax].
  - move=> b Hb; rewrite elem_of_app elem_of_cons.
    have Hbd : b ∈ take idx arr \/ b ∈ drop idx arr by (rewrite -elem_of_app take_drop; exact Hb).
    tauto.
  - move=> b Hb2 Hbnin.
    move: Hb2; rewrite elem_of_app elem_of_cons => -[Hbt | [Hba | Hbd]].
    + exfalso; apply Hbnin; rewrite -(take_drop idx arr) elem_of_app; by left.
    + subst b; exact Hane.
    + exfalso; apply Hbnin; rewrite -(take_drop idx arr) elem_of_app; by right.
Qed.

(** A failed pointer search stays failed after inserting a different item. *)
Lemma findPtrIdx_none_insert (arr : list (YjsItem A)) (a p : YjsItem A) (idx : nat) :
  findPtrIdx (itemPtr a) arr = None -> a <> p ->
  findPtrIdx (itemPtr a) (insertIdxIfInBounds idx p arr) = None.
Proof using A EqDA.
  rewrite /findPtrIdx /find_item_idx => Hnone Hne.
  have Hln : list_find (fun i => i = a) arr = None
    by (apply fmap_None in Hnone; apply fmap_None in Hnone; exact Hnone).
  have Hpa : ¬ ((fun i => i = a) p) by (move=> /= Hpa; apply Hne; by rewrite Hpa).
  rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [_|_].
  - by rewrite (list_find_insert_None (fun i => i = a) arr idx p Hpa Hln).
  - by rewrite Hln.
Qed.

Lemma findLeftIdx_none_insert (arr : list (YjsItem A)) (a : YjsItem A) (originId : option YjsId) (idx : nat) :
  findLeftIdx originId arr = None -> originId <> Some (item_id a) ->
  findLeftIdx originId (insertIdxIfInBounds idx a arr) = None.
Proof using A EqDA.
  rewrite /findLeftIdx; destruct originId as [id|]; last (move=> H; discriminate H).
  move=> Hnone Hne.
  have Hln : list_find (fun item => item_id item = id) arr = None
    by (apply fmap_None in Hnone; apply fmap_None in Hnone; exact Hnone).
  have Hpa : ¬ ((fun item => item_id item = id) a) by (move=> /= Hpa; apply Hne; by rewrite Hpa).
  rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [_|_].
  - by rewrite (list_find_insert_None _ arr idx a Hpa Hln).
  - by rewrite Hln.
Qed.

Lemma findRightIdx_none_insert (arr : list (YjsItem A)) (a : YjsItem A) (originId : option YjsId) (idx : nat) :
  findRightIdx originId arr = None -> originId <> Some (item_id a) ->
  findRightIdx originId (insertIdxIfInBounds idx a arr) = None.
Proof using A EqDA.
  rewrite /findRightIdx; destruct originId as [id|]; last (move=> H; discriminate H).
  move=> Hnone Hne.
  have Hln : list_find (fun item => item_id item = id) arr = None
    by (apply fmap_None in Hnone; apply fmap_None in Hnone; exact Hnone).
  have Hpa : ¬ ((fun item => item_id item = id) a) by (move=> /= Hpa; apply Hne; by rewrite Hpa).
  rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [_|_].
  - by rewrite (list_find_insert_None _ arr idx a Hpa Hln).
  - by rewrite Hln.
Qed.

(** A successful left/right search yields the pointer it located. *)
Lemma findLeftIdx_some_getPtrExcept_some (arr : list (YjsItem A)) (originId : option YjsId) (idx : Z) :
  findLeftIdx originId arr = Some idx ->
  exists p, getPtrExcept arr idx = Some p /\
    match originId with
    | Some id => exists item, p = itemPtr item /\ item_id item = id
    | None => p = First
    end.
Proof using A EqDA.
  rewrite /findLeftIdx; destruct originId as [id|].
  - move=> /fmap_Some [k [Hk ->]].
    move: Hk => /fmap_Some [[k' item] [Hfind Hkeq]]; simpl in Hkeq; subst k.
    have Hfacts := Hfind; apply list_find_Some in Hfacts; destruct Hfacts as (Hlk & HP & _).
    have Hlt : k' < length arr := lookup_lt_Some _ _ _ Hlk.
    exists (itemPtr item); split.
    + rewrite /getPtrExcept.
      destruct (decide (Z.of_nat k' = -1)%Z) as [?|_]; [lia|].
      destruct (decide (Z.of_nat k' = Z.of_nat (length arr))%Z) as [?|_]; [lia|].
      by rewrite Nat2Z.id Hlk /=.
    + exists item; split; [done|exact HP].
  - move=> [= <-]; exists First; split; [|done].
    rewrite /getPtrExcept; destruct (decide ((-1)%Z = -1)%Z) as [_|?]; [done|lia].
Qed.

Lemma findRightIdx_some_getPtrExcept_some (arr : list (YjsItem A)) (originId : option YjsId) (idx : Z) :
  findRightIdx originId arr = Some idx ->
  exists p, getPtrExcept arr idx = Some p /\
    match originId with
    | Some id => exists item, p = itemPtr item /\ item_id item = id
    | None => p = Last
    end.
Proof using A EqDA.
  rewrite /findRightIdx; destruct originId as [id|].
  - move=> /fmap_Some [k [Hk ->]].
    move: Hk => /fmap_Some [[k' item] [Hfind Hkeq]]; simpl in Hkeq; subst k.
    have Hfacts := Hfind; apply list_find_Some in Hfacts; destruct Hfacts as (Hlk & HP & _).
    have Hlt : k' < length arr := lookup_lt_Some _ _ _ Hlk.
    exists (itemPtr item); split.
    + rewrite /getPtrExcept.
      destruct (decide (Z.of_nat k' = -1)%Z) as [?|_]; [lia|].
      destruct (decide (Z.of_nat k' = Z.of_nat (length arr))%Z) as [?|_]; [lia|].
      by rewrite Nat2Z.id Hlk /=.
    + exists item; split; [done|exact HP].
  - move=> [= <-]; exists Last; split; [|done].
    rewrite /getPtrExcept.
    destruct (decide (Z.of_nat (length arr) = -1)%Z) as [?|_]; [lia|].
    destruct (decide (Z.of_nat (length arr) = Z.of_nat (length arr))%Z) as [_|?]; [done|lia].
Qed.

(** Clock-maximality after insertion implies it before (the converse of
    [maximalId_insertIdxIfInBounds]). *)
Lemma maximalId_insert (arr : list (YjsItem A)) (a x : YjsItem A) (idx : nat) :
  maximalId x (insertIdxIfInBounds idx a arr) -> maximalId x arr.
Proof using A EqDA.
  move=> Hmax y Hy Hideq; apply: (Hmax y _ Hideq).
  rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [_|_]; last exact Hy.
  rewrite /ArrSet elem_of_app elem_of_cons.
  have Hyd : y ∈ take idx arr \/ y ∈ drop idx arr by (rewrite -elem_of_app take_drop; exact Hy).
  tauto.
Qed.

(** Index shift of left/right search under insertion of a different-id item. *)
Lemma findLeftIdx_insert (arr : list (YjsItem A)) (a : YjsItem A) (originId : option YjsId)
    (idx : nat) (leftIdx : Z) :
  findLeftIdx originId arr = Some leftIdx -> originId <> Some (item_id a) ->
  findLeftIdx originId (insertIdxIfInBounds idx a arr) =
    Some (if decide (leftIdx < Z.of_nat idx)%Z then leftIdx else (leftIdx + 1)%Z).
Proof using A EqDA.
  rewrite /findLeftIdx; destruct originId as [id|].
  - move=> /fmap_Some [k [Hk Hkeq]] Hne.
    move: Hk => /fmap_Some [[k' item] [Hfind Hk'eq]]; simpl in Hk'eq; subst k.
    subst leftIdx.
    have Hpa : ¬ ((fun item0 => item_id item0 = id) a) by (move=> /= Hpa; apply Hne; by rewrite Hpa).
    rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [Hidx|Hidx].
    + rewrite (list_find_insert_shift (fun item0 => item_id item0 = id) arr idx k' item a Hpa Hidx Hfind) /=.
      destruct (decide (idx <= k')%nat) as [Hle|Hle];
        destruct (decide (Z.of_nat k' < Z.of_nat idx)%Z) as [Hz|Hz];
        [exfalso;lia | f_equal;lia | by [] | exfalso;lia].
    + rewrite Hfind /=.
      have Hk'lt : (k' < length arr)%nat
        by (have Hf := Hfind; apply list_find_Some in Hf; destruct Hf as (Hlk & _ & _); exact: lookup_lt_Some _ _ _ Hlk).
      destruct (decide (Z.of_nat k' < Z.of_nat idx)%Z) as [Hz|Hz]; [done | exfalso; lia].
  - move=> [= <-] Hne.
    destruct (decide ((-1)%Z < Z.of_nat idx)%Z) as [_|Hc]; [done | exfalso; lia].
Qed.

Lemma findRightIdx_insert (arr : list (YjsItem A)) (a : YjsItem A) (originId : option YjsId)
    (idx : nat) (rightIdx : Z) :
  findRightIdx originId arr = Some rightIdx -> originId <> Some (item_id a) ->
  findRightIdx originId (insertIdxIfInBounds idx a arr) =
    Some (if decide (rightIdx < Z.of_nat idx)%Z then rightIdx else (rightIdx + 1)%Z).
Proof using A EqDA.
  rewrite /findRightIdx; destruct originId as [id|].
  - move=> /fmap_Some [k [Hk Hkeq]] Hne.
    move: Hk => /fmap_Some [[k' item] [Hfind Hk'eq]]; simpl in Hk'eq; subst k.
    subst rightIdx.
    have Hpa : ¬ ((fun item0 => item_id item0 = id) a) by (move=> /= Hpa; apply Hne; by rewrite Hpa).
    rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [Hidx|Hidx].
    + rewrite (list_find_insert_shift (fun item0 => item_id item0 = id) arr idx k' item a Hpa Hidx Hfind) /=.
      destruct (decide (idx <= k')%nat) as [Hle|Hle];
        destruct (decide (Z.of_nat k' < Z.of_nat idx)%Z) as [Hz|Hz];
        [exfalso;lia | f_equal;lia | by [] | exfalso;lia].
    + rewrite Hfind /=.
      have Hk'lt : (k' < length arr)%nat
        by (have Hf := Hfind; apply list_find_Some in Hf; destruct Hf as (Hlk & _ & _); exact: lookup_lt_Some _ _ _ Hlk).
      destruct (decide (Z.of_nat k' < Z.of_nat idx)%Z) as [Hz|Hz]; [done | exfalso; lia].
  - move=> [= <-] Hne.
    rewrite /insertIdxIfInBounds; destruct (decide (idx <= length arr)%nat) as [Hidx|Hidx].
    + rewrite length_app /= length_take_le // length_drop.
      destruct (decide (Z.of_nat (length arr) < Z.of_nat idx)%Z) as [Hz|Hz]; [exfalso;lia | f_equal; lia].
    + destruct (decide (Z.of_nat (length arr) < Z.of_nat idx)%Z) as [Hz|Hz]; [done | exfalso; lia].
Qed.

(** A by-id lookup is unaffected by inserting a different-id item. *)
Lemma find_by_id_insert (arr : list (YjsItem A)) (a : YjsItem A) (id : YjsId) (idx : nat) :
  item_id a <> id -> (idx <= length arr)%nat ->
  find_by_id id (insertIdxIfInBounds idx a arr) = find_by_id id arr.
Proof using A EqDA.
  move=> Hne Hidx; rewrite /find_by_id /insertIdxIfInBounds (decide_True _ _ Hidx).
  have Hpa : ¬ ((fun item => item_id item = id) a) by (move=> /= H; apply Hne; exact H).
  destruct (list_find (fun item => item_id item = id) arr) as [[k it]|] eqn:Hf.
  - by rewrite (list_find_insert_shift (fun item => item_id item = id) arr idx k it a Hpa Hidx Hf) /=.
  - by rewrite (list_find_insert_None (fun item => item_id item = id) arr idx a Hpa Hf) /=.
Qed.

(** [toItem] is stable under insertion of a fresh-id item. *)
Lemma toItem_insertIfInBounds (input : IntegrateInput) (arr : list (YjsItem A)) (a item : YjsItem A) (idx : nat) :
  toItem input arr = Some item ->
  uniqueId (insertIdxIfInBounds idx a arr) ->
  toItem input (insertIdxIfInBounds idx a arr) = Some item.
Proof using A EqDA.
  move=> Htoitem Huniq.
  destruct (decide (idx <= length arr)%nat) as [Hidx|Hidx]; last first.
  { rewrite /insertIdxIfInBounds (decide_False _ _ Hidx); exact Htoitem. }
  apply toItem_ok_iff.
  have [o [r [id [c [Hdef [HoL [HoR [Hid Hc]]]]]]]] := proj1 (toItem_ok_iff input arr item) Htoitem.
  exists o, r, id, c; split_and!; [exact Hdef | | | exact Hid | exact Hc].
  - rewrite /isLeftIdPtr in HoL *; destruct (in_originId input) as [id0|]; last exact HoL.
    destruct HoL as [oit [Hoeq Hfind]]; exists oit; split; [exact Hoeq|].
    have Hmem : oit ∈ arr := @find_by_id_mem _ EqDA id0 arr oit Hfind.
    have Hidoit : item_id oit = id0 := @find_by_id_id _ EqDA id0 arr oit Hfind.
    have Hne : item_id a <> id0.
    { have H := @uniqueId_insertIdxIfInBounds_id_neq _ EqDA arr a oit idx Huniq Hidx Hmem.
      by rewrite Hidoit in H. }
    rewrite (find_by_id_insert arr a id0 idx Hne Hidx); exact Hfind.
  - rewrite /isRightIdPtr in HoR *; destruct (in_rightOriginId input) as [id0|]; last exact HoR.
    destruct HoR as [rit [Hreq Hfind]]; exists rit; split; [exact Hreq|].
    have Hmem : rit ∈ arr := @find_by_id_mem _ EqDA id0 arr rit Hfind.
    have Hidrit : item_id rit = id0 := @find_by_id_id _ EqDA id0 arr rit Hfind.
    have Hne : item_id a <> id0.
    { have H := @uniqueId_insertIdxIfInBounds_id_neq _ EqDA arr a rit idx Huniq Hidx Hmem.
      by rewrite Hidrit in H. }
    rewrite (find_by_id_insert arr a id0 idx Hne Hidx); exact Hfind.
Qed.

(** A pointer in the array set has a [findPtrIdx]. *)
Lemma ArrSet_findPtrIdx_some (arr : list (YjsItem A)) (p : YjsPtr A) :
  ArrSet arr p -> exists idx, findPtrIdx p arr = Some idx.
Proof using A EqDA.
  destruct p as [it| |] => Hp.
  - rewrite /findPtrIdx /find_item_idx.
    destruct (list_find (fun i => i = it) arr) as [[k' x]|] eqn:Hf.
    + by eexists.
    + exfalso; apply list_find_None in Hf; rewrite ->Forall_forall in Hf.
      exact: (Hf it Hp eq_refl).
  - by exists (-1)%Z.
  - by exists (Z.of_nat (length arr)).
Qed.

(** The scan terminates with a result whenever the indices it visits are in
    range (origins are resolvable by array closedness). *)
Lemma fii_loop_total (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (arr : list (YjsItem A)) (scanning : bool) (destIdx : Z) :
  YjsArrInvariant arr ->
  (forall j, (j < count)%nat -> (0 <= leftIdx + Z.of_nat offset + Z.of_nat j)%Z /\
     (leftIdx + Z.of_nat offset + Z.of_nat j < Z.of_nat (length arr))%Z) ->
  exists d, fii_loop count offset leftIdx rightIdx cid arr scanning destIdx = Some d.
Proof using A EqDA.
  move=> Harr; move: offset scanning destIdx.
  induction count as [|count' IH] => offset scanning destIdx Hvalid; first by exists destIdx.
  have [Hi0 Hi1] := Hvalid 0%nat ltac:(lia); rewrite Z.add_0_r in Hi0 Hi1.
  have Hi : (Z.to_nat (leftIdx + Z.of_nat offset) < length arr)%nat by lia.
  simpl.
  have [other Hother] : exists other, getElemExcept arr (Z.to_nat (leftIdx + Z.of_nat offset)) = Some other.
  { rewrite /getElemExcept; destruct (lookup_lt_is_Some_2 arr _ Hi) as [other Ho]; by exists other. }
  rewrite Hother /=.
  have Hmem : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hother.
  have Hoset : ArrSet arr (origin other)
    by (destruct other as [o r id c]; exact: (closedLeft _ (yai_closed _ Harr) o r id c Hmem)).
  have Hrset : ArrSet arr (rightOrigin other)
    by (destruct other as [o r id c]; exact: (closedRight _ (yai_closed _ Harr) o r id c Hmem)).
  have [oL HoL] := ArrSet_findPtrIdx_some arr (origin other) Hoset.
  have [oR HoR] := ArrSet_findPtrIdx_some arr (rightOrigin other) Hrset.
  rewrite HoL /= HoR /=.
  have Hrec : forall j, (j < count')%nat ->
    (0 <= leftIdx + Z.of_nat (S offset) + Z.of_nat j)%Z /\
    (leftIdx + Z.of_nat (S offset) + Z.of_nat j < Z.of_nat (length arr))%Z
    by (move=> j Hj; have := Hvalid (S j) ltac:(lia); lia).
  destruct (decide (oL < leftIdx)%Z); first by exists destIdx.
  destruct (decide (oL = leftIdx)%Z).
  - destruct (decide (clientId (item_id other) < cid)%nat).
    + exact: (IH (S offset) false _ Hrec).
    + destruct (decide (oR = rightIdx)%Z); first by exists destIdx.
      exact: (IH (S offset) true _ Hrec).
  - exact: (IH (S offset) scanning _ Hrec).
Qed.

(** [findIntegratedIndex] always succeeds for in-range left/right indices. *)
Lemma findIntegratedIndex_safe (leftIdx rightIdx : Z) (input : IntegrateInput) (arr : list (YjsItem A)) :
  YjsArrInvariant arr ->
  (-1 <= leftIdx)%Z -> (leftIdx <= Z.of_nat (length arr))%Z ->
  (-1 <= rightIdx)%Z -> (rightIdx <= Z.of_nat (length arr))%Z ->
  exists idx, findIntegratedIndex leftIdx rightIdx input arr = Some idx.
Proof using A EqDA.
  move=> Harr Hl1 Hl2 Hr1 Hr2; rewrite /findIntegratedIndex.
  have Hvalid : forall j, (j < Z.to_nat (rightIdx - leftIdx) - 1)%nat ->
    (0 <= leftIdx + Z.of_nat 1 + Z.of_nat j)%Z /\ (leftIdx + Z.of_nat 1 + Z.of_nat j < Z.of_nat (length arr))%Z
    by (move=> j Hj; split; lia).
  have [d Hd] := fii_loop_total (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
    (clientId (in_id input)) arr false (leftIdx + 1)%Z Harr Hvalid.
  rewrite Hd /=; by exists (Z.to_nat d).
Qed.

End commutativity.

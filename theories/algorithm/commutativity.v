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
  invariant_yjsarray findptridx_insert insert_loop.

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

End commutativity.

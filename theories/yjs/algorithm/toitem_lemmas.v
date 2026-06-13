(** Resolving an [IntegrateInput] into a concrete item: the predicates
    [isLeftIdPtr]/[isRightIdPtr] characterise the origin / right-origin pointers,
    [toItem_ok_iff] gives the success characterisation, and the [findLeftIdx]/
    [findRightIdx] index functions agree with [findPtrIdx] on the resolved item.
    Port of the corresponding section in
    [LeanYjs/Algorithm/Invariant/YjsArray.lean]. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray invariant_yjsarray_idx.

Section toitem.
Context {A : Type} `{EqDA : EqDecision A}.

(** The origin pointer determined by an (optional) id: [First] when absent,
    otherwise the item found by that id. *)
Definition isLeftIdPtr (arr : list (YjsItem A)) (id : option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | None => ptr = First
  | Some pid => exists item, ptr = itemPtr item /\ find_by_id pid arr = Some item
  end.

Definition isRightIdPtr (arr : list (YjsItem A)) (id : option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | None => ptr = Last
  | Some pid => exists item, ptr = itemPtr item /\ find_by_id pid arr = Some item
  end.

Lemma isLeftIdPtr_unique (arr : list (YjsItem A)) (id : option YjsId) (ptr1 ptr2 : YjsPtr A) :
  isLeftIdPtr arr id ptr1 -> isLeftIdPtr arr id ptr2 -> ptr1 = ptr2.
Proof using A EqDA.
  destruct id as [pid|] => /= H1 H2.
  - destruct H1 as [it1 [-> Hf1]]; destruct H2 as [it2 [-> Hf2]].
    rewrite Hf1 in Hf2; by injection Hf2 as ->.
  - by rewrite H1 H2.
Qed.

Lemma isRightIdPtr_unique (arr : list (YjsItem A)) (id : option YjsId) (ptr1 ptr2 : YjsPtr A) :
  isRightIdPtr arr id ptr1 -> isRightIdPtr arr id ptr2 -> ptr1 = ptr2.
Proof using A EqDA.
  destruct id as [pid|] => /= H1 H2.
  - destruct H1 as [it1 [-> Hf1]]; destruct H2 as [it2 [-> Hf2]].
    rewrite Hf1 in Hf2; by injection Hf2 as ->.
  - by rewrite H1 H2.
Qed.

(** In a unique-id document, two members with the same id are equal. *)
Lemma uniqueId_id_eq_implies_eq (arr : list (YjsItem A)) :
  uniqueId arr -> forall x y, x ∈ arr -> y ∈ arr -> item_id x = item_id y -> x = y.
Proof using A EqDA.
  move=> Huniq x y Hx Hy Hid.
  have [i Hi] := list_elem_of_lookup_1 _ _ Hx.
  have [j Hj] := list_elem_of_lookup_1 _ _ Hy.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
  - exfalso; apply: (ss_lookup_lt arr i j x y Huniq Hi Hj Hlt); exact: Hid.
  - subst j; rewrite Hj in Hi; by injection Hi as ->.
  - exfalso; apply: (ss_lookup_lt arr j i y x Huniq Hj Hi Hgt); by rewrite Hid.
Qed.

(** [list_find] only inspects list members, so predicates agreeing on them give
    the same result. *)
Lemma list_find_ext_in {X} (P Q : X -> Prop)
    `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} (l : list X) :
  (forall x, x ∈ l -> (P x <-> Q x)) -> list_find P l = list_find Q l.
Proof.
  induction l as [|x l IH]; [done|] => /= HPQ.
  rewrite (decide_ext (P x) (Q x)); [|by apply HPQ; left].
  rewrite IH; [done|]; move=> y Hy; apply HPQ; by right.
Qed.

(** Resolution of the origin / right-origin pointers as monadic lookups. *)
Lemma resolve_left (arr : list (YjsItem A)) (O : option YjsId) (op : YjsPtr A) :
  (match O with Some id => itemPtr <$> find_by_id id arr | None => Some First end) = Some op
  <-> isLeftIdPtr arr O op.
Proof using A EqDA.
  rewrite /isLeftIdPtr; destruct O as [pid|].
  - rewrite fmap_Some; naive_solver.
  - split; [by inversion 1 | by move=> ->].
Qed.

Lemma resolve_right (arr : list (YjsItem A)) (O : option YjsId) (op : YjsPtr A) :
  (match O with Some id => itemPtr <$> find_by_id id arr | None => Some Last end) = Some op
  <-> isRightIdPtr arr O op.
Proof using A EqDA.
  rewrite /isRightIdPtr; destruct O as [pid|].
  - rewrite fmap_Some; naive_solver.
  - split; [by inversion 1 | by move=> ->].
Qed.

(** [toItem] succeeds exactly when the origin / right-origin ids resolve. *)
Lemma toItem_ok_iff (input : IntegrateInput) (arr : list (YjsItem A)) (newItem : YjsItem A) :
  toItem input arr = Some newItem <->
  exists o r id c, newItem = Item o r id c /\
    isLeftIdPtr arr (in_originId input) o /\
    isRightIdPtr arr (in_rightOriginId input) r /\
    id = in_id input /\ c = in_content input.
Proof using A EqDA.
  rewrite /toItem; split.
  - move=> /bind_Some [op [Hop /bind_Some [rp [Hrp [= <-]]]]].
    exists op, rp, (in_id input), (in_content input); split_and!;
      [done | by apply/resolve_left | by apply/resolve_right | done | done].
  - move=> [o [r [id [c [-> [Ho [Hr [-> ->]]]]]]]].
    apply/bind_Some; exists o; split; [by apply/resolve_left|].
    apply/bind_Some; exists r; split; [by apply/resolve_right|done].
Qed.

(** A by-id lookup hit is an array member. *)
Lemma find_by_id_mem (id : YjsId) (arr : list (YjsItem A)) (item : YjsItem A) :
  find_by_id id arr = Some item -> item ∈ arr.
Proof using A EqDA.
  rewrite /find_by_id => /fmap_Some [[k it] [Hfind ->]].
  apply list_find_Some in Hfind; destruct Hfind as (Hlk & _ & _).
  exact: (list_elem_of_lookup_2 _ _ _ Hlk).
Qed.

Lemma findLeftIdx_ArrSet (input : IntegrateInput) (newItem : YjsItem A)
    (arr : list (YjsItem A)) (idx : Z) :
  uniqueId arr ->
  toItem input arr = Some newItem ->
  findLeftIdx (in_originId input) arr = Some idx ->
  ArrSet arr (origin newItem).
Proof using A EqDA.
  move=> _ Htoitem _; apply toItem_ok_iff in Htoitem.
  destruct Htoitem as [o [r [id [c [-> [Ho _]]]]]]; simpl.
  rewrite /isLeftIdPtr in Ho; destruct (in_originId input) as [pid|]; simpl in Ho.
  - destruct Ho as [item [-> Hf]]; exact: (find_by_id_mem pid arr item Hf).
  - rewrite Ho; exact I.
Qed.

Lemma findRightIdx_ArrSet (input : IntegrateInput) (newItem : YjsItem A)
    (arr : list (YjsItem A)) (idx : Z) :
  uniqueId arr ->
  toItem input arr = Some newItem ->
  findRightIdx (in_rightOriginId input) arr = Some idx ->
  ArrSet arr (rightOrigin newItem).
Proof using A EqDA.
  move=> _ Htoitem _; apply toItem_ok_iff in Htoitem.
  destruct Htoitem as [o [r [id [c [-> [_ [Hr _]]]]]]]; simpl.
  rewrite /isRightIdPtr in Hr; destruct (in_rightOriginId input) as [pid|]; simpl in Hr.
  - destruct Hr as [item [-> Hf]]; exact: (find_by_id_mem pid arr item Hf).
  - rewrite Hr; exact I.
Qed.

(** The found item carries the searched id. *)
Lemma find_by_id_id (id : YjsId) (arr : list (YjsItem A)) (item : YjsItem A) :
  find_by_id id arr = Some item -> item_id item = id.
Proof using A EqDA.
  rewrite /find_by_id => /fmap_Some [[k it] [Hfind ->]].
  apply list_find_Some in Hfind; destruct Hfind as (_ & Hp & _); exact: Hp.
Qed.

(** The id-indexed search and the structural search agree on the resolved item:
    [findLeftIdx] coincides with [findPtrIdx] of the resolved origin. *)
Lemma findLeftIdx_findPtrIdx_eq (input : IntegrateInput) (newItem : YjsItem A)
    (arr : list (YjsItem A)) :
  uniqueId arr ->
  toItem input arr = Some newItem ->
  findLeftIdx (in_originId input) arr = findPtrIdx (origin newItem) arr.
Proof using A EqDA.
  move=> Huniq Htoitem; apply toItem_ok_iff in Htoitem.
  destruct Htoitem as [o [r [id [c [-> [Ho _]]]]]]; simpl.
  rewrite /isLeftIdPtr in Ho; destruct (in_originId input) as [pid|]; simpl in Ho.
  - destruct Ho as [originItem [-> Hf]].
    have Hpid : item_id originItem = pid := find_by_id_id pid arr originItem Hf.
    have Hmem : originItem ∈ arr := find_by_id_mem pid arr originItem Hf.
    rewrite /findLeftIdx /findPtrIdx /find_item_idx.
    have Hagree : forall a, a ∈ arr -> (item_id a = pid <-> a = originItem).
    { move=> a Ha; split.
      - move=> Hida; apply: (uniqueId_id_eq_implies_eq arr Huniq a originItem Ha Hmem).
        by rewrite Hida Hpid.
      - move=> ->; exact: Hpid. }
    by rewrite (list_find_ext_in (fun item => item_id item = pid) (fun i => i = originItem) arr Hagree).
  - by rewrite Ho /findLeftIdx /findPtrIdx /=.
Qed.

Lemma findRightIdx_findPtrIdx_eq (input : IntegrateInput) (newItem : YjsItem A)
    (arr : list (YjsItem A)) :
  uniqueId arr ->
  toItem input arr = Some newItem ->
  findRightIdx (in_rightOriginId input) arr = findPtrIdx (rightOrigin newItem) arr.
Proof using A EqDA.
  move=> Huniq Htoitem; apply toItem_ok_iff in Htoitem.
  destruct Htoitem as [o [r [id [c [-> [_ [Hr _]]]]]]]; simpl.
  rewrite /isRightIdPtr in Hr; destruct (in_rightOriginId input) as [pid|]; simpl in Hr.
  - destruct Hr as [rightOriginItem [-> Hf]].
    have Hpid : item_id rightOriginItem = pid := find_by_id_id pid arr rightOriginItem Hf.
    have Hmem : rightOriginItem ∈ arr := find_by_id_mem pid arr rightOriginItem Hf.
    rewrite /findRightIdx /findPtrIdx /find_item_idx.
    have Hagree : forall a, a ∈ arr -> (item_id a = pid <-> a = rightOriginItem).
    { move=> a Ha; split.
      - move=> Hida; apply: (uniqueId_id_eq_implies_eq arr Huniq a rightOriginItem Ha Hmem).
        by rewrite Hida Hpid.
      - move=> ->; exact: Hpid. }
    by rewrite (list_find_ext_in (fun item => item_id item = pid) (fun i => i = rightOriginItem) arr Hagree).
  - by rewrite Hr /findRightIdx /findPtrIdx /=.
Qed.

End toitem.

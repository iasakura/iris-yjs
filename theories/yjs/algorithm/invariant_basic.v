(** The Yjs array invariant (closed item set + order invariant), for a document
    represented as a [list]. Port of [LeanYjs/Algorithm/Invariant/Basic.lean].
    Lean's [Array]/[Fin] indexing is restated with stdpp list lookup [!!]. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant.

Section invariant.
Context {A : Type}.

(** The set of pointers reachable as members of [arr] ([First]/[Last] always). *)
Definition ArrSet (arr : list (YjsItem A)) : YjsPtr A -> Prop :=
  fun a => match a with
  | itemPtr item => item ∈ arr
  | First => True
  | Last => True
  end.

Definition ArrSetClosed (arr : list (YjsItem A)) : Prop := IsClosedItemSet (ArrSet arr).

Lemma push_subset (arr : list (YjsItem A)) (a : YjsItem A) (x : YjsPtr A) :
  ArrSet arr x -> ArrSet (a :: arr) x.
Proof. case: x => [item| |] //= Hin; rewrite elem_of_cons; by right. Qed.

Lemma arr_set_closed_push (arr : list (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr -> ArrSet arr (origin item) -> ArrSet arr (rightOrigin item) ->
  ArrSetClosed (item :: arr).
Proof.
  move=> Hclosed Horigin Hright; split.
  - done.
  - done.
  - move=> o r id c; rewrite /ArrSet /= elem_of_cons => -[Heq | Hin].
    + subst item; clear Hright; move: Horigin; rewrite /origin /=.
      case: o => [o'| |] //= Horigin; rewrite elem_of_cons; by right.
    + apply: push_subset; exact: (closedLeft _ Hclosed o r id c Hin).
  - move=> o r id c; rewrite /ArrSet /= elem_of_cons => -[Heq | Hin].
    + subst item; clear Horigin; move: Hright; rewrite /rightOrigin /=.
      case: r => [r'| |] //= Hright; rewrite elem_of_cons; by right.
    + apply: push_subset; exact: (closedRight _ Hclosed o r id c Hin).
Qed.

(** Items of [arr] occur at some index (Lean's [arr_set_item_exists_index]). *)
Lemma arr_set_item_exists_index (arr : list (YjsItem A)) (item : YjsItem A) :
  ArrSet arr item -> exists i, arr !! i = Some item.
Proof. exact: list_elem_of_lookup_1. Qed.

Lemma arr_set_closed_exists_index_for_origin (arr : list (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr -> ArrSet arr item ->
  origin item = First \/ origin item = Last \/
  exists i it, arr !! i = Some it /\ origin item = itemPtr it.
Proof.
  move=> Hclosed; case: item => [o r id c] Hitem.
  have Ho : ArrSet arr o := closedLeft _ Hclosed o r id c Hitem.
  clear Hitem; rewrite /origin /=; case: o Ho => [it| |] /= Ho.
  - right; right; have [i Hi] := list_elem_of_lookup_1 _ _ Ho; by exists i, it.
  - by left.
  - by right; left.
Qed.

Lemma arr_set_closed_exists_index_for_right_origin (arr : list (YjsItem A)) (item : YjsItem A) :
  ArrSetClosed arr -> ArrSet arr item ->
  rightOrigin item = First \/ rightOrigin item = Last \/
  exists i it, arr !! i = Some it /\ rightOrigin item = itemPtr it.
Proof.
  move=> Hclosed; case: item => [o r id c] Hitem.
  have Hr : ArrSet arr r := closedRight _ Hclosed o r id c Hitem.
  clear Hitem; rewrite /rightOrigin /=; case: r Hr => [it| |] /= Hr.
  - right; right; have [i Hi] := list_elem_of_lookup_1 _ _ Hr; by exists i, it.
  - by left.
  - by right; left.
Qed.

Lemma reachable_in (arr : list (YjsItem A)) (a : YjsPtr A) :
  ArrSetClosed arr ->
  forall x, OriginReachable a x -> ArrSet arr a -> ArrSet arr x.
Proof.
  move=> Hclosed x Hreach; elim: Hreach => [{}x y Hstep | {}x y z Hstep _ IH].
  - case: Hstep => o r id c Hin;
      [exact: (closedLeft _ Hclosed o r id c Hin) | exact: (closedRight _ Hclosed o r id c Hin)].
  - move=> Hin; apply: IH; case: Hstep Hin => o r id c Hin;
      [exact: (closedLeft _ Hclosed o r id c Hin) | exact: (closedRight _ Hclosed o r id c Hin)].
Qed.

Lemma item_set_invariant_push (arr : list (YjsItem A)) (item : YjsItem A) :
  ItemSetInvariant (ArrSet arr) ->
  ArrSetClosed arr ->
  YjsLt' (origin item) (rightOrigin item) ->
  (forall x, OriginReachable item x -> YjsLeq' x (origin item) \/ YjsLeq' (rightOrigin item) x) ->
  (forall x : YjsItem A, ArrSet arr x -> item_id x = item_id item -> x = item) ->
  ItemSetInvariant (ArrSet (item :: arr)).
Proof.
  move=> Hinv Hclosed Horigin Hreach Hsameid; split.
  - move=> o r c id; rewrite /ArrSet /= elem_of_cons => -[Heq | Hin].
    + subst item; exact: Horigin.
    + exact: (origin_not_leq _ Hinv o r c id Hin).
  - move=> o r c id x; rewrite /ArrSet /= elem_of_cons => -[Heq | Hin] Hreachable.
    + subst item; exact: Hreach.
    + exact: (origin_nearest_reachable _ Hinv o r c id x Hin Hreachable).
  - move=> x y Hid; rewrite /ArrSet /= !elem_of_cons => -[Hx | Hx] -[Hy | Hy].
    + by subst x y.
    + subst x; symmetry; apply: Hsameid; [exact: Hy | by rewrite Hid].
    + subst y; apply: Hsameid; [exact: Hx | exact: Hid].
    + exact: (id_unique _ Hinv x y Hid Hx Hy).
Qed.

End invariant.

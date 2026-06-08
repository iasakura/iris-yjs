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
  invariant_yjsarray insert_loop.

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

End commutativity.

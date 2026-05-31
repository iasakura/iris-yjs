(** Sets of items and closure under sub-pointers.

    Port of [LeanYjs/ItemSet.lean]. An item set is a predicate on pointers; it
    is closed when it contains both sentinels and is downward closed along the
    [origin]/[rightOrigin] fields. *)
From stdpp Require Import base.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.

Definition ItemSet (A : Type) := YjsPtr A -> Prop.

Record IsClosedItemSet {A} (P : YjsPtr A -> Prop) : Prop := {
  baseFirst : P First;
  baseLast : P Last;
  closedLeft : forall (o r : YjsPtr A) id c, P (itemPtr (Item o r id c)) -> P o;
  closedRight : forall (o r : YjsPtr A) id c, P (itemPtr (Item o r id c)) -> P r;
}.

Lemma IsClosedItemSet_eq_set {A} (P Q : YjsPtr A -> Prop) :
  IsClosedItemSet P -> (forall x, P x <-> Q x) -> IsClosedItemSet Q.
Proof.
  move=> HP hPQ; split.
  - apply/hPQ; exact: (baseFirst _ HP).
  - apply/hPQ; exact: (baseLast _ HP).
  - move=> o r id c /hPQ Hp; apply/hPQ; exact: (closedLeft _ HP _ _ _ _ Hp).
  - move=> o r id c /hPQ Hp; apply/hPQ; exact: (closedRight _ HP _ _ _ _ Hp).
Qed.

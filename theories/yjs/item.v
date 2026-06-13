(** The Yjs item model.

    Port of [LeanYjs/Item.lean]: identifiers ([YjsId]) with their total order,
    the mutually recursive pointer/item tree ([YjsPtr]/[YjsItem]), and the
    structural [size] measure used for well-founded recursion. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.

(** An identifier pairs the originating client with a per-client clock. *)
Record YjsId := MkYjsId {
  clientId : ClientId;
  clock : nat;
}.
Add Printing Constructor YjsId.

Global Instance YjsId_eq_dec : EqDecision YjsId.
Proof. solve_decision. Defined.

(** Order on identifiers: within the same client a larger clock is "smaller"
    (more to the left); across clients we compare client ids. *)
Definition YjsId_lt (id1 id2 : YjsId) : Prop :=
  if bool_decide (id1.(clientId) = id2.(clientId))
  then id2.(clock) < id1.(clock)
  else id1.(clientId) < id2.(clientId).

Global Instance YjsId_lt_dec id1 id2 : Decision (YjsId_lt id1 id2).
Proof. rewrite /YjsId_lt; case_bool_decide; apply _. Defined.

(** The document is a tree of items. A pointer is either an item or one of the
    two sentinels [First]/[Last]. *)
Inductive YjsPtr (A : Type) : Type :=
  | itemPtr : YjsItem A -> YjsPtr A
  | First : YjsPtr A
  | Last : YjsPtr A
with YjsItem (A : Type) : Type :=
  | Item : YjsPtr A -> YjsPtr A -> YjsId -> A -> YjsItem A.

Arguments itemPtr {A} _.
Arguments First {A}.
Arguments Last {A}.
Arguments Item {A} _ _ _ _.

Coercion itemPtr : YjsItem >-> YjsPtr.

(** Field accessors for [YjsItem]. Since [YjsItem] is defined mutually with
    [YjsPtr] it is an inductive rather than a record, so we project by hand.
    (The id accessor is [item_id] to avoid clashing with [Init]'s [id].) *)
Definition origin {A} (i : YjsItem A) : YjsPtr A :=
  match i with Item o _ _ _ => o end.
Definition rightOrigin {A} (i : YjsItem A) : YjsPtr A :=
  match i with Item _ r _ _ => r end.
Definition item_id {A} (i : YjsItem A) : YjsId :=
  match i with Item _ _ id _ => id end.
Definition content {A} (i : YjsItem A) : A :=
  match i with Item _ _ _ c => c end.

(** Structural size, used as a termination measure for recursion over the
    item tree. *)
Fixpoint YjsPtr_size {A} (p : YjsPtr A) : nat :=
  match p with
  | itemPtr i => YjsItem_size i + 1
  | First => 0
  | Last => 0
  end
with YjsItem_size {A} (i : YjsItem A) : nat :=
  match i with
  | Item o r _ _ => YjsPtr_size o + YjsPtr_size r + 2
  end.

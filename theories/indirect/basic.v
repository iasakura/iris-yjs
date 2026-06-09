(** Indirect document state. Port of [LeanYjs/Indirect/Algorithm/Basic.lean]. *)
From stdpp Require Import base numbers gmap sets.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic.
From yjs.indirect Require Import item.

Record IYjsState (A : Type) := MkIYjsState {
  ist_items : list (IYjsItem A);
  ist_deleted : gset YjsId;
}.
Arguments MkIYjsState {A} _ _.
Arguments ist_items {A} _.
Arguments ist_deleted {A} _.

Definition IYjsState_empty {A} : IYjsState A := MkIYjsState [] ∅.

(** Erase a direct state to its indirect form (items mapped by id). *)
Definition ofDirectState {A} (s : YjsState A) : IYjsState A :=
  MkIYjsState (ofDirectItem <$> st_items s) (st_deleted s).

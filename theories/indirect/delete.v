(** Indirect delete (tombstone). Port of
    [LeanYjs/Indirect/Algorithm/Delete/Basic.lean]. *)
From stdpp Require Import base gmap sets.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.indirect Require Import item basic.

Definition ideleteById {A} (s : IYjsState A) (id : YjsId) : IYjsState A :=
  MkIYjsState (ist_items s) ({[id]} ∪ ist_deleted s).

(** The delete operation (tombstone a [YjsId]) and its laws. Port of
    [LeanYjs/Algorithm/Delete/{Basic,Spec}.lean] and the delete-related
    commutativity files [Commutativity/{DeleteDelete,InsertDelete}.lean]. *)
From stdpp Require Import base gmap sets.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic insert_basic invariant_yjsarray.

Section delete.
Context {A : Type} `{EqDA : EqDecision A}.

(** Mark [id] as deleted (tombstone); the document list is unchanged. *)
Definition deleteById (s : YjsState A) (id : YjsId) : YjsState A :=
  MkYjsState (st_items s) ({[id]} ∪ st_deleted s).

(** Deletion preserves the state invariant (it does not touch the list). *)
Lemma YjsStateInvariant_deleteById (s : YjsState A) (id : YjsId) :
  YjsStateInvariant s -> YjsStateInvariant (deleteById s id).
Proof using A. by []. Qed.

(** Deletions commute. *)
Lemma deleteById_commutative (s : YjsState A) (id1 id2 : YjsId) :
  deleteById (deleteById s id1) id2 = deleteById (deleteById s id2) id1.
Proof using A. rewrite /deleteById /=; f_equal; set_solver. Qed.

(** Insert and delete commute (they act on independent components). *)
Lemma insert_deleteById_commutative (newItem : IntegrateInput) (s : YjsState A) (id : YjsId) :
  (YjsState_insert s newItem ≫= fun newArr => Some (deleteById newArr id)) =
  YjsState_insert (deleteById s id) newItem.
Proof using A EqDA.
  rewrite /YjsState_insert /deleteById /=.
  by destruct (integrateSafe newItem (st_items s)) as [arr|].
Qed.

End delete.

(** Yjs algorithm: basic state types.

    Port of [LeanYjs/Algorithm/Basic.lean]. The document state is the list of
    items (Lean uses an [Array]; all reasoning is on its [toList], so we model it
    directly as a [list]) together with the finite set of deleted ids. The
    integration algorithm is partial, signalling failure with [IntegrateError];
    in the relational/option style we will return [option]/[sum IntegrateError]
    rather than Lean's [Except] monad. *)
From stdpp Require Import base list countable gmap.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item.

(** Structural decidable equality for the mutually-inductive item tree.
    [solve_decision] can't break the YjsPtr/YjsItem cycle, so we go through a
    boolean equality reflected via the mutual induction scheme. *)
Fixpoint YjsPtr_beq {A} (eqA : A -> A -> bool) (p1 p2 : YjsPtr A) : bool :=
  match p1, p2 with
  | itemPtr i1, itemPtr i2 => YjsItem_beq eqA i1 i2
  | First, First => true
  | Last, Last => true
  | _, _ => false
  end
with YjsItem_beq {A} (eqA : A -> A -> bool) (i1 i2 : YjsItem A) : bool :=
  match i1, i2 with
  | Item o1 r1 id1 c1, Item o2 r2 id2 c2 =>
      YjsPtr_beq eqA o1 o2 && YjsPtr_beq eqA r1 r2 && bool_decide (id1 = id2) && eqA c1 c2
  end.

Scheme YjsPtr_mut := Induction for YjsPtr Sort Prop
  with YjsItem_mut := Induction for YjsItem Sort Prop.

Lemma YjsItem_beq_spec {A} (eqA : A -> A -> bool)
    (HA : forall a b, eqA a b = true <-> a = b) :
  forall i1 i2, YjsItem_beq eqA i1 i2 = true <-> i1 = i2.
Proof.
  apply (YjsItem_mut A
    (fun p1 => forall p2, YjsPtr_beq eqA p1 p2 = true <-> p1 = p2)
    (fun i1 => forall i2, YjsItem_beq eqA i1 i2 = true <-> i1 = i2)).
  - move=> i IHi [i2| |] /=; [| by split; (move=> H; congruence) ..].
    rewrite IHi; split; [by move=> -> | by move=> [= ->]].
  - move=> [i2| |] /=; by split; (move=> H; congruence).
  - move=> [i2| |] /=; by split; (move=> H; congruence).
  - move=> o IHo r IHr id c [o2 r2 id2 c2] /=.
    rewrite !andb_true_iff IHo IHr bool_decide_eq_true HA.
    split; [by move=> [[[-> ->] ->] ->] | by move=> [= -> -> -> ->]].
Qed.

Lemma YjsItem_beq_spec_bd {A} `{EqDecision A} (i1 i2 : YjsItem A) :
  YjsItem_beq (fun a b => bool_decide (a = b)) i1 i2 = true <-> i1 = i2.
Proof. apply YjsItem_beq_spec => a b; apply bool_decide_eq_true. Qed.

Global Instance YjsItem_eq_dec {A} `{EqDecision A} : EqDecision (YjsItem A).
Proof.
  intros i1 i2.
  destruct (YjsItem_beq (fun a b => bool_decide (a = b)) i1 i2) eqn:Hb.
  - left. exact: (proj1 (YjsItem_beq_spec_bd i1 i2) Hb).
  - right. move=> Heq; move: Hb.
    by rewrite (proj2 (YjsItem_beq_spec_bd i1 i2) Heq).
Qed.

Global Instance YjsPtr_eq_dec {A} `{EqDecision A} : EqDecision (YjsPtr A).
Proof. solve_decision. Defined.

(** Integration can fail with a single (uninformative) error. *)
Inductive IntegrateError := IntegrateErr.

Global Instance IntegrateError_eq_dec : EqDecision IntegrateError.
Proof. solve_decision. Defined.

(** [YjsId] is a pair of naturals, hence countable — so we can take finite sets
    of ids for the deleted-set. *)
Global Instance YjsId_countable : Countable YjsId.
Proof.
  apply (inj_countable' (fun id => (clientId id, clock id))
                        (fun p => MkYjsId p.1 p.2)).
  by intros [].
Qed.

(** A document state: the item list plus the set of deleted ids. *)
Record YjsState (A : Type) := MkYjsState {
  st_items : list (YjsItem A);
  st_deleted : gset YjsId;
}.
Arguments MkYjsState {A} _ _.
Arguments st_items {A} _.
Arguments st_deleted {A} _.

Definition YjsState_empty {A} : YjsState A := MkYjsState [] ∅.

Definition YjsState_toList {A} (s : YjsState A) : list (YjsItem A) := st_items s.

(** Look up the first item satisfying [p]. *)
Definition YjsState_find {A} (s : YjsState A) (p : YjsItem A -> bool) : option (YjsItem A) :=
  List.find p (st_items s).

(** Mark an id as deleted (idempotent set insert). *)
Definition addDeletedId {A} (s : YjsState A) (id : YjsId) : YjsState A :=
  MkYjsState (st_items s) ({[ id ]} ∪ st_deleted s).

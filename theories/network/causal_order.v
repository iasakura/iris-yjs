(** Causal order and the operation framework (Yjs-independent).

    Port of [LeanYjs/Network/CausalOrder.lean]. The happens-before relation is a
    partial order; operations have an effect on a state. Unlike the Lean model,
    where an effect is a *function* [State -> Except Error State], we model it
    *relationally* as [A -> State -> State -> Prop], because that is what a
    HeapLang program denotes (a relation between pre- and post-state). Relation
    equality is taken pointwise ([≡]) to stay axiom-free. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.

Section causal_order.
Context {A : Type}.

(** Happens-before, packaged as a partial order on [A]. *)
Record CausalOrder := MkCausalOrder {
  co_le : relation A;
  co_po : PartialOrder co_le;
}.
Global Existing Instance co_po.

(** Strict happens-before. *)
Definition co_lt (hb : CausalOrder) (a b : A) : Prop := co_le hb a b /\ a <> b.

(** Two operations are concurrent when neither happens before the other. *)
Definition hb_concurrent (hb : CausalOrder) (a b : A) : Prop :=
  ¬ co_le hb a b /\ ¬ co_le hb b a.

Lemma hb_concurrent_symm hb a b : hb_concurrent hb a b <-> hb_concurrent hb b a.
Proof. rewrite /hb_concurrent; tauto. Qed.

(** A list is causally consistent when every element precedes (in the list) all
    the operations that do not happen before it. *)
Inductive hb_consistent (hb : CausalOrder) : list A -> Prop :=
  | hb_consistent_nil : hb_consistent hb []
  | hb_consistent_cons a ops :
      hb_consistent hb ops ->
      (forall b, b ∈ ops -> ¬ co_le hb b a) ->
      hb_consistent hb (a :: ops).

(** The "strong" variant: each element's strict predecessors all appear in the
    prefix already accumulated. *)
Inductive hb_strong_consistent (hb : CausalOrder) : list A -> list A -> Prop :=
  | hb_strong_consistent_nil ops : hb_strong_consistent hb ops []
  | hb_strong_consistent_cons a ops0 ops1 :
      hb_strong_consistent hb (a :: ops0) ops1 ->
      (forall b, co_lt hb b a -> b ∈ ops0) ->
      hb_strong_consistent hb ops0 (a :: ops1).

Lemma sublist_mem {l1 l2 : list A} (a : A) :
  sublist l1 l2 -> a ∈ l1 -> a ∈ l2.
Proof.
  move=> Hsub; move: a.
  induction Hsub as [| x k1 k2 Hsub IH | x k1 k2 Hsub IH].
  - move=> a Hin; exact: Hin.
  - (* sublist_skip: both keep [x] *)
    move=> a; rewrite !elem_of_cons => -[->|Hin]; [by left | by right; apply: IH].
  - (* sublist_cons: drop [x] from the right *)
    move=> a Hin; apply elem_of_cons; by right; apply: IH.
Qed.

Lemma hb_consistent_sublist hb {ops0 ops1 : list A} :
  hb_consistent hb ops0 -> sublist ops1 ops0 -> hb_consistent hb ops1.
Proof.
  move=> Hcons Hsub; move: Hcons.
  induction Hsub as [| x l1 l2 Hsub IH | x l1 l2 Hsub IH].
  - by [].
  - (* sublist_skip: ops1 = x::l1, ops0 = x::l2 *)
    move=> Hcons; inversion Hcons as [| a ops Hcons' Hno]; subst.
    apply: hb_consistent_cons; first exact: (IH Hcons').
    move=> b Hb; apply: Hno; exact: (sublist_mem b Hsub Hb).
  - (* sublist_cons: ops1 = l1, ops0 = x::l2 *)
    move=> Hcons; apply: IH; by inversion Hcons.
Qed.

Lemma hb_consistent_tail hb a (ops : list A) :
  hb_consistent hb (a :: ops) -> hb_consistent hb ops.
Proof. by inversion 1. Qed.

Lemma hb_consistent_concurrent hb a (ops0 ops1 : list A) :
  hb_consistent hb (ops0 ++ a :: ops1) ->
  forall x, x ∈ ops0 -> ¬ co_le hb a x.
Proof.
  elim: ops0 => [| y ys IH] /=.
  - move=> _ x; rewrite elem_of_nil; by [].
  - move=> Hcons x; rewrite elem_of_cons => -[->|Hx].
    + inversion Hcons as [| ? ? ? Hno]; subst.
      apply: Hno; rewrite elem_of_app elem_of_cons; by right; left.
    + apply: IH => //; exact: (hb_consistent_tail _ _ _ Hcons).
Qed.

(** Suffix analogue of [hb_consistent_concurrent]: an element occurring after
    [a] in a consistent list cannot be [co_le]-below [a]. *)
Lemma hb_consistent_concurrent_r hb a (ops0 ops1 : list A) :
  hb_consistent hb (ops0 ++ a :: ops1) ->
  forall x, x ∈ ops1 -> ¬ co_le hb x a.
Proof.
  elim: ops0 => [| y ys IH] /=.
  - move=> Hcons x Hx; inversion Hcons as [| ? ? ? Hno]; subst.
    by apply: Hno.
  - move=> Hcons; apply: IH; exact: (hb_consistent_tail _ _ _ Hcons).
Qed.

(** Operations and their relational effect on a state. *)
Record Operation := MkOperation {
  op_State : Type;
  op_init : op_State;
  op_effect : A -> op_State -> op_State -> Prop;
}.

Section effects.
Context (O : Operation).
Let St := op_State O.
Implicit Types (R S T : St -> St -> Prop).

(** The effect of a single operation as a relation. *)
Definition effect (a : A) : St -> St -> Prop := op_effect O a.

(** Relational (Kleisli) composition of effects. *)
Definition eff_comp R S : St -> St -> Prop :=
  fun s s'' => exists s', R s s' /\ S s' s''.

(** Pointwise equivalence of effects. *)
Definition eff_equiv R S : Prop := forall s s', R s s' <-> S s s'.

Local Infix "▷" := eff_comp (at level 60).
Local Infix "≅" := eff_equiv (at level 70).

Global Instance eff_equiv_equiv : Equivalence eff_equiv.
Proof.
  split; rewrite /eff_equiv.
  - done.
  - move=> R S H s s'; by rewrite H.
  - move=> R S T H1 H2 s s'; by rewrite H1.
Qed.

Global Instance eff_comp_proper :
  Proper (eff_equiv ==> eff_equiv ==> eff_equiv) eff_comp.
Proof.
  move=> R1 R2 HR S1 S2 HS s s''; rewrite /eff_comp.
  split; move=> [m [H1 H2]]; exists m; split.
  - by apply HR. - by apply HS. - by apply HR. - by apply HS.
Qed.

Lemma eff_comp_assoc R S T : ((R ▷ S) ▷ T) ≅ (R ▷ (S ▷ T)).
Proof.
  move=> s s''; rewrite /eff_comp; split.
  - move=> [m [[m' [HR HS]] HT]]; exists m'; split; [done | by exists m].
  - move=> [m' [HR [m [HS HT]]]]; exists m; split; [by exists m' | done].
Qed.

Lemma eff_comp_id_r R : (R ▷ (=)) ≅ R.
Proof.
  move=> s s'; rewrite /eff_comp; split.
  - move=> [m [HR Heq]]; by subst m.
  - move=> HR; exists s'; by split.
Qed.

Lemma eff_comp_id_l R : ((=) ▷ R) ≅ R.
Proof.
  move=> s s'; rewrite /eff_comp; split.
  - move=> [m [Heq HR]]; by subst m.
  - move=> HR; exists s; by split.
Qed.

(** Applying a list of operations in order, on top of a continuation [K]. *)
Definition apply_ops (K : St -> St -> Prop) (ops : list A) : St -> St -> Prop :=
  foldr eff_comp K (map effect ops).

Lemma apply_ops_cons K a ops :
  apply_ops K (a :: ops) = (effect a) ▷ (apply_ops K ops).
Proof. done. Qed.

(** [s] is a state reachable by running some causally-consistent set of
    operations strictly below [a] (and not above any of them). *)
Definition compatibleOp (hb : CausalOrder) (s : St) (a : A) : Prop :=
  exists ops, hb_consistent hb ops
    /\ (forall b, co_lt hb b a -> b ∈ ops)
    /\ (forall b, b ∈ ops -> ¬ co_le hb a b)
    /\ apply_ops (=) ops (op_init O) s.

(** Concurrent operations of [l] commute, on every state they are both
    compatible with. *)
Definition concurrent_commutative (hb : CausalOrder) (l : list A) : Prop :=
  forall a b, a ∈ l -> b ∈ l -> hb_concurrent hb a b ->
    forall s, compatibleOp hb s a -> compatibleOp hb s b ->
      forall s', ((effect a) ▷ (effect b)) s s' <-> ((effect b) ▷ (effect a)) s s'.

(** A list of operations is applicable from [s], each step from a compatible
    state. *)
Inductive compatibleOps (hb : CausalOrder) : St -> list A -> Prop :=
  | compatibleOps_nil s : compatibleOps hb s []
  | compatibleOps_cons s s' a ops :
      compatibleOp hb s a -> effect a s s' -> compatibleOps hb s' ops ->
      compatibleOps hb s (a :: ops).

End effects.

End causal_order.

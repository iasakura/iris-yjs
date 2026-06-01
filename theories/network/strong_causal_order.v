(** Strong causal order: the convergence framework Yjs uses (Yjs-independent).

    Port of [LeanYjs/Network/StrongCausalOrder.lean]. On top of [causal_order]
    and [hb_closed], this adds operation identifiers ([WithId]/[IdNoDup]), a
    state-validity discipline ([OperationValidity], [OperationReplayValidity]),
    the left-to-right [effect_list], and a validity-conditioned commutativity,
    leading to the strong convergence theorem.

    As in [causal_order], effects are RELATIONAL ([op_effect : A -> St -> St ->
    Prop]); [effect_list] is [apply_ops] with the identity continuation. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.network Require Import causal_order hb_closed.

Section strong_causal_order.
Context {A : Type}.

(** Consistency is preserved by swapping two adjacent concurrent operations. *)
Lemma hb_consistent_swap hb (ops0 ops1 : list A) a b :
  hb_consistent hb (ops0 ++ a :: b :: ops1) ->
  hb_concurrent hb b a ->
  hb_consistent hb (ops0 ++ b :: a :: ops1).
Proof.
  move=> Hcons Hconc; elim: ops0 Hcons => [| x xs IH] /= Hcons.
  - inversion Hcons as [| ? ? Htail Hno_a]; subst.
    inversion Htail as [| ? ? Hops1 Hno_b]; subst.
    apply: hb_consistent_cons.
    + apply: hb_consistent_cons; first exact: Hops1.
      move=> y Hy; apply: Hno_a; rewrite elem_of_cons; by right.
    + move=> y; rewrite elem_of_cons => -[-> | Hy].
      * move: Hconc; rewrite /hb_concurrent; tauto.
      * exact: (Hno_b y Hy).
  - inversion Hcons as [| ? ? Htail Hno_x]; subst.
    apply: hb_consistent_cons; first exact: (IH Htail).
    move=> y Hy; apply: Hno_x; move: Hy; rewrite !elem_of_app !elem_of_cons; tauto.
Qed.

(** Operations carry an identifier of type [S]. *)
Context {S : Type} `{EqDecision S}.
Record WithId := { wid : A -> S }.

(** All operations in a list have distinct identifiers. *)
Definition IdNoDup (W : WithId) (ops : list A) : Prop := NoDup (wid W <$> ops).

Section validity.
Context (O : @Operation A).
Let St := op_State O.

(** Applying a list of operations left to right (relationally), from a state. *)
Definition effect_list (ops : list A) : St -> St -> Prop := apply_ops O (=) ops.

Lemma effect_list_nil s s' : effect_list [] s s' <-> s = s'.
Proof. done. Qed.

Lemma effect_list_cons a ops s s' :
  effect_list (a :: ops) s s' <-> exists m, op_effect O a s m /\ effect_list ops m s'.
Proof. done. Qed.

(** A validity discipline on states: a per-operation precondition
    [isValidState] and a global invariant [StateInv] preserved by valid steps. *)
Record OperationValidity := {
  isValidState : A -> St -> Prop;
  StateInv : St -> Prop;
  stateInv_init : StateInv (op_init O);
  stateInv_effect : forall (op : A) (s s' : St),
    StateInv s -> isValidState op s -> op_effect O op s s' -> StateInv s';
}.

(** When a state is reached by replaying a valid causal history of [a]'s
    predecessors, [a] is valid in it. *)
Record OperationReplayValidity (OV : OperationValidity) (W : WithId)
    (hb : @CausalOrder A) (StateSource : A -> Prop) : Prop := {
  isValidState_of_history :
    forall (a : A) (s : St) (l : list A),
      StateSource a ->
      (forall x, co_lt hb x a -> x ∈ l) ->
      hb_consistent hb l ->
      hbClosed hb l ->
      effect_list l (op_init O) s ->
      IdNoDup W l ->
      isValidState OV a s;
}.

(** Concurrent operations commute on states where both are valid. *)
Definition concurrent_commutative (OV : OperationValidity) (hb : @CausalOrder A)
    (l : list A) : Prop :=
  forall a b (s s' : St), a ∈ l -> b ∈ l -> hb_concurrent hb a b ->
    StateInv OV s -> isValidState OV a s -> isValidState OV b s ->
    eff_comp O (effect O a) (effect O b) s s' ->
    eff_comp O (effect O b) (effect O a) s s'.

End validity.

End strong_causal_order.

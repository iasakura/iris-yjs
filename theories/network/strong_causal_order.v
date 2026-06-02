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
Context {A : Type} `{EqDecision A}.

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

(** Prefix-closure facts used by the convergence proof. *)
Lemma hb_consistent_app_l hb (l1 l2 : list A) :
  hb_consistent hb (l1 ++ l2) -> hb_consistent hb l1.
Proof.
  elim: l1 => [| x xs IH] /=; first by move=> _; exact: hb_consistent_nil.
  move=> Hcons; inversion Hcons as [| ? ? Htail Hno]; subst.
  apply: hb_consistent_cons; first exact: (IH Htail).
  move=> y Hy; apply: Hno; rewrite elem_of_app; by left.
Qed.

Lemma hbClosed_app_l hb (l1 l2 : list A) :
  hbClosed hb (l1 ++ l2) -> hbClosed hb l1.
Proof.
  move=> H a b p q Heq Hlt; apply: (H a b p (q ++ l2)); last done.
  by rewrite Heq -app_assoc.
Qed.

Lemma hbClosed_pred_last hb (ops : list A) a :
  hbClosed hb (ops ++ [a]) -> forall x, co_lt hb x a -> x ∈ ops.
Proof. move=> H x Hlt; exact: (H a x ops [] eq_refl Hlt). Qed.

(** Operations carry an identifier of type [S]. *)
Context {S : Type} `{EqDecision S}.
Record WithId := { wid : A -> S }.

(** All operations in a list have distinct identifiers. *)
Definition IdNoDup (W : WithId) (ops : list A) : Prop := NoDup (wid W <$> ops).

Lemma IdNoDup_app_l (W : WithId) (l1 l2 : list A) :
  IdNoDup W (l1 ++ l2) -> IdNoDup W l1.
Proof. rewrite /IdNoDup fmap_app NoDup_app; tauto. Qed.

Lemma IdNoDup_swap (W : WithId) (ops0 ops1 : list A) (a b : A) :
  IdNoDup W (ops0 ++ a :: b :: ops1) -> IdNoDup W (ops0 ++ b :: a :: ops1).
Proof.
  rewrite /IdNoDup => H.
  have Hperm : (ops0 ++ a :: b :: ops1) ≡ₚ (ops0 ++ b :: a :: ops1)
    by apply: Permutation_app_head; apply: perm_swap.
  by rewrite -Hperm.
Qed.

Lemma not_in_of_idnodup_snoc (W : WithId) (l : list A) (b : A) :
  IdNoDup W (l ++ [b]) -> b ∉ l.
Proof.
  rewrite /IdNoDup fmap_app NoDup_app => -[_ [Hmid _]] Hb.
  apply: (Hmid (wid W b)); first (apply: list_elem_of_fmap_2; exact: Hb).
  rewrite elem_of_cons; by left.
Qed.

Lemma idnodup_mid_not_in (W : WithId) (l1 l2 : list A) (b : A) :
  IdNoDup W (l1 ++ b :: l2) -> b ∉ l1 /\ b ∉ l2.
Proof.
  rewrite /IdNoDup fmap_app fmap_cons NoDup_app NoDup_cons => -[_ [Hmid [Hnotin _]]].
  split=> Hb.
  - apply: (Hmid (wid W b)); first (apply: list_elem_of_fmap_2; exact: Hb).
    rewrite elem_of_cons; by left.
  - apply: Hnotin; apply: list_elem_of_fmap_2; exact: Hb.
Qed.

(** Removing the uniquely-identified [b] from both sides of a same-elements
    relationship. *)
Lemma mem_ops0_prefix_iff_ops1 (W : WithId)
    (ops0_first ops0_last ops1 : list A) (a b : A) :
  IdNoDup W (ops0_first ++ b :: ops0_last ++ [a]) ->
  IdNoDup W (ops1 ++ [b]) ->
  (forall x, x ∈ (ops0_first ++ b :: ops0_last ++ [a]) <-> x ∈ (ops1 ++ [b])) ->
  forall x, x ∈ (ops0_first ++ ops0_last ++ [a]) <-> x ∈ ops1.
Proof.
  move=> Hnd0 Hnd1 Hmem.
  have Hb1 := not_in_of_idnodup_snoc _ _ _ Hnd1.
  have [Hbf Hbr] := idnodup_mid_not_in _ _ _ _ Hnd0.
  move=> x; specialize (Hmem x); set_solver.
Qed.

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

Lemma effect_list_snoc ops a s s' :
  effect_list (ops ++ [a]) s s' <-> exists m, effect_list ops s m /\ op_effect O a m s'.
Proof.
  elim: ops s => [| x xs IH] s.
  - split.
    + move=> [m0 [Ha Heq]]; exists s; split; [by apply/effect_list_nil | by subst].
    + move=> [m [Hm Ha]]; move/effect_list_nil: Hm => Heq; subst m.
      exists s'; split; [exact: Ha | done].
  - have -> : (x :: xs) ++ [a] = x :: (xs ++ [a]) by [].
    split.
    + move=> [m1 [Hx Hrest]].
      have [m [Hxs Ha]] := proj1 (IH m1) Hrest.
      exists m; split; last exact: Ha.
      exists m1; split; [exact: Hx | exact: Hxs].
    + move=> [m [[m1 [Hx Hxs]] Ha]].
      exists m1; split; first exact: Hx.
      apply (proj2 (IH m1)); exists m; split; [exact: Hxs | exact: Ha].
Qed.

Lemma effect_list_app l1 l2 s s' :
  effect_list (l1 ++ l2) s s' <-> exists m, effect_list l1 s m /\ effect_list l2 m s'.
Proof.
  elim: l1 s => [| x xs IH] s.
  - split.
    + move=> Hl2; exists s; split; [by apply/effect_list_nil | exact: Hl2].
    + by move=> [m [/effect_list_nil <- Hl2]].
  - have -> : (x :: xs) ++ l2 = x :: (xs ++ l2) by [].
    split.
    + move=> [m1 [Hx Hrest]]; have [m [Hxs Hl2]] := proj1 (IH m1) Hrest.
      exists m; split; last exact: Hl2.
      exists m1; split; [exact: Hx | exact: Hxs].
    + move=> [m [[m1 [Hx Hxs]] Hl2]].
      exists m1; split; first exact: Hx.
      apply (proj2 (IH m1)); exists m; split; [exact: Hxs | exact: Hl2].
Qed.

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

(** Swapping two consecutive operations at a state where they commute. *)
Lemma eff_swap (a b : A) (m s : St) (R : St -> St -> Prop) :
  (forall s', eff_comp O (effect O a) (effect O b) m s' ->
              eff_comp O (effect O b) (effect O a) m s') ->
  eff_comp O (effect O a) (eff_comp O (effect O b) R) m s ->
  eff_comp O (effect O b) (eff_comp O (effect O a) R) m s.
Proof.
  move=> Hcomm [m1 [Ha [m2 [Hb HR]]]].
  have [m1' [Hb' Ha']] : eff_comp O (effect O b) (effect O a) m m2
    by apply: Hcomm; exists m1; by split.
  exists m1'; split; first done; exists m2; by split.
Qed.

(** Replaying a valid causal history preserves the state invariant. *)
Lemma effect_list_stateInv (OV : OperationValidity) (W : WithId)
    (hb : @CausalOrder A) (StateSource : A -> Prop)
    (RV : OperationReplayValidity OV W hb StateSource) :
  forall (ops : list A) (s : St),
    (forall op, op ∈ ops -> StateSource op) ->
    hb_consistent hb ops -> hbClosed hb ops -> IdNoDup W ops ->
    effect_list ops (op_init O) s -> StateInv OV s.
Proof.
  move=> ops; elim/rev_ind: ops => [| a ops IH] s Hsrc Hcons Hclosed Hnd Heff.
  - move: Heff => /effect_list_nil <-; exact: (stateInv_init OV).
  - move: Heff => /effect_list_snoc [m [Hpre Ha]].
    have Hcons' := hb_consistent_app_l _ _ _ Hcons.
    have Hclosed' := hbClosed_app_l _ _ _ Hclosed.
    have Hnd' := IdNoDup_app_l _ _ _ Hnd.
    have Hsrc' : forall op, op ∈ ops -> StateSource op
      by move=> op Hop; apply: Hsrc; rewrite elem_of_app; by left.
    have HsiM : StateInv OV m := IH m Hsrc' Hcons' Hclosed' Hnd' Hpre.
    have Hva : isValidState OV a m.
    { apply: (isValidState_of_history _ _ _ _ RV a m ops).
      - apply: Hsrc; rewrite elem_of_app elem_of_cons; by right; left.
      - exact: (hbClosed_pred_last _ _ _ Hclosed).
      - exact: Hcons'.
      - exact: Hclosed'.
      - exact: Hpre.
      - exact: Hnd'. }
    exact: (stateInv_effect OV a m s HsiM Hva Ha).
Qed.

(** Moving an operation [a] rightward past a block of operations all concurrent
    with it preserves the resulting state (relational [effect_list]). *)
Lemma effect_list_reorder (OV : OperationValidity) (W : WithId) (hb : @CausalOrder A)
    (StateSource : A -> Prop) (RV : OperationReplayValidity OV W hb StateSource) (a : A) :
  forall (ops0 ops1 : list A) (s : St),
    (forall x, x ∈ (ops0 ++ a :: ops1) -> StateSource x) ->
    concurrent_commutative OV hb (ops0 ++ a :: ops1) ->
    (forall x, x ∈ ops1 -> hb_concurrent hb x a) ->
    hb_consistent hb (ops0 ++ a :: ops1) ->
    hbClosed hb (ops0 ++ a :: ops1) ->
    IdNoDup W (ops0 ++ a :: ops1) ->
    effect_list (ops0 ++ a :: ops1) (op_init O) s ->
    effect_list (ops0 ++ ops1 ++ [a]) (op_init O) s.
Proof.
  move=> ops0 ops1; move: ops0.
  elim: ops1 => [| b ops1 IH] ops0 s Hsrc HC Hconc Hcons Hclosed Hnd Heff.
  - exact: Heff.
  - move: Heff => /effect_list_app [m [Hpre Hrest]].
    have Hcons0 := hb_consistent_app_l _ _ _ Hcons.
    have Hclosed0 := hbClosed_app_l _ _ _ Hclosed.
    have Hnd0 := IdNoDup_app_l _ _ _ Hnd.
    have Hsrc0 : forall x, x ∈ ops0 -> StateSource x
      by move=> x Hx; apply: Hsrc; rewrite elem_of_app; by left.
    have Hsi : StateInv OV m :=
      effect_list_stateInv OV W hb StateSource RV ops0 m Hsrc0 Hcons0 Hclosed0 Hnd0 Hpre.
    have Hba : hb_concurrent hb b a by apply: Hconc; rewrite elem_of_cons; by left.
    have Hva : isValidState OV a m.
    { apply: (isValidState_of_history _ _ _ _ RV a m ops0);
        try by [exact: Hcons0 | exact: Hclosed0 | exact: Hpre | exact: Hnd0].
      - apply: Hsrc; rewrite elem_of_app elem_of_cons; by right; left.
      - move=> x Hlt; exact: (Hclosed a x ops0 (b :: ops1) eq_refl Hlt). }
    have Hvb : isValidState OV b m.
    { apply: (isValidState_of_history _ _ _ _ RV b m ops0);
        try by [exact: Hcons0 | exact: Hclosed0 | exact: Hpre | exact: Hnd0].
      - apply: Hsrc; rewrite elem_of_app !elem_of_cons; by right; right; left.
      - move=> x Hlt.
        have Hx : x ∈ ops0 ++ [a]
          by apply: (Hclosed b x (ops0 ++ [a]) ops1 _ Hlt); rewrite -app_assoc.
        move: Hx; rewrite elem_of_app elem_of_cons elem_of_nil => -[// | [Hxa | []]].
        exfalso; subst x; move: Hba Hlt; rewrite /hb_concurrent /co_lt.
        by move=> [_ Hnab] [Hab _]; apply: Hnab. }
    have Hcomm_m : forall s', eff_comp O (effect O a) (effect O b) m s' ->
                              eff_comp O (effect O b) (effect O a) m s'.
    { move=> s' Hab; apply: (HC a b m s');
        try by [exact: Hsi | exact: Hva | exact: Hvb | exact: Hab].
      - rewrite elem_of_app elem_of_cons; by right; left.
      - rewrite elem_of_app !elem_of_cons; by right; right; left.
      - by rewrite hb_concurrent_symm. }
    have Hswapped : effect_list (ops0 ++ b :: a :: ops1) (op_init O) s.
    { apply/effect_list_app; exists m; split; first exact: Hpre.
      apply: (eff_swap a b m s (effect_list ops1)); [exact: Hcomm_m | exact: Hrest]. }
    have Hgoal : effect_list ((ops0 ++ [b]) ++ ops1 ++ [a]) (op_init O) s.
    { apply: (IH (ops0 ++ [b]) s).
      - move=> x Hx; apply: Hsrc; move: Hx; set_solver.
      - move=> a' b' s0 s0' Ha' Hb'; apply: HC; move: Ha' Hb'; set_solver.
      - move=> x Hx; apply: Hconc; rewrite elem_of_cons; by right.
      - rewrite -app_assoc; exact: (hb_consistent_swap hb ops0 ops1 a b Hcons Hba).
      - rewrite -app_assoc; exact: (hbClosed_swap hb ops0 ops1 a b Hclosed Hba).
      - rewrite -app_assoc; exact: (IdNoDup_swap W ops0 ops1 a b Hnd).
      - rewrite -app_assoc; exact: Hswapped. }
    rewrite -!app_assoc in Hgoal; exact: Hgoal.
Qed.

End validity.

End strong_causal_order.

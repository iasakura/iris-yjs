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
From stdpp Require Import options.
From yjs.crdt.operation Require Import causal_order hb_closed.

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
      (forall x, x ∈ l -> StateSource x) ->
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

(** [concurrent_commutative] is antitone in the operation list: it still holds
    on any sublist (by membership) of a list on which it holds. *)
Lemma concurrent_commutative_mono (OV : OperationValidity) (hb : @CausalOrder A)
    (l1 l2 : list A) :
  (forall x, x ∈ l2 -> x ∈ l1) ->
  concurrent_commutative OV hb l1 ->
  concurrent_commutative OV hb l2.
Proof.
  move=> Hsub Hcc a b s s' Ha Hb.
  exact: (Hcc a b s s' (Hsub _ Ha) (Hsub _ Hb)).
Qed.

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
      - exact: Hsrc'.
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
      - exact: Hsrc0.
      - move=> x Hlt; exact: (Hclosed a x ops0 (b :: ops1) eq_refl Hlt). }
    have Hvb : isValidState OV b m.
    { apply: (isValidState_of_history _ _ _ _ RV b m ops0);
        try by [exact: Hcons0 | exact: Hclosed0 | exact: Hpre | exact: Hnd0].
      - apply: Hsrc; rewrite elem_of_app !elem_of_cons; by right; right; left.
      - exact: Hsrc0.
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

(** Strong convergence: two causally-consistent orderings of the same set of
    operations (with the concurrent ones commuting) produce the same state.
    Stated at top level (operation [O] explicit) so that the section-local
    definitions it relies on appear as their discharged constants. *)
Lemma hb_consistent_effect_convergent {A S : Type} `{EqDecision A} `{EqDecision S}
    (O : @Operation A) (OV : OperationValidity O) (W : @WithId A S)
    (hb : @CausalOrder A) (StateSource : A -> Prop)
    (RV : OperationReplayValidity O OV W hb StateSource) :
  forall (ops0 ops1 : list A) (s : op_State O),
    (forall x, x ∈ ops0 -> StateSource x) -> (forall x, x ∈ ops1 -> StateSource x) ->
    hb_consistent hb ops0 -> hb_consistent hb ops1 ->
    hbClosed hb ops0 -> hbClosed hb ops1 ->
    concurrent_commutative O OV hb ops0 ->
    IdNoDup W ops0 -> IdNoDup W ops1 ->
    (forall x, x ∈ ops0 <-> x ∈ ops1) ->
    effect_list O ops0 (op_init O) s -> effect_list O ops1 (op_init O) s.
Proof.
  move=> ops0 ops1 s; move: ops0 s.
  elim/rev_ind: ops1 => [| b ops1 IH] ops0 s Hsrc0 Hsrc1 Hc0 Hc1 Hcl0 Hcl1 Hcomm Hnd0 Hnd1 Hmem Heff.
  - destruct ops0 as [| x ops0]; first exact: Heff.
    exfalso; move: (Hmem x); rewrite elem_of_nil => -[Hf _].
    apply: Hf; rewrite elem_of_cons; by left.
  - have Hb1 : b ∉ ops1 := not_in_of_idnodup_snoc _ _ _ Hnd1.
    destruct ops0 as [| a ops0' _] using rev_ind.
    + exfalso; move: (Hmem b); rewrite elem_of_nil elem_of_app elem_of_cons => -[_ Hg].
      apply: Hg; by right; left.
    + destruct (decide (a = b)) as [->|Hab].
      * have Hb0 : b ∉ ops0' := not_in_of_idnodup_snoc _ _ _ Hnd0.
        have Hmem' : forall x, x ∈ ops0' <-> x ∈ ops1
          by move=> x; move: (Hmem x); set_solver.
        move: Heff => /effect_list_snoc [m [Hpre Hb]].
        apply/effect_list_snoc; exists m; split; last exact: Hb.
        apply: (IH ops0' m).
        -- move=> x Hx; apply: Hsrc0; rewrite elem_of_app; by left.
        -- move=> x Hx; apply: Hsrc1; rewrite elem_of_app; by left.
        -- exact: (hb_consistent_app_l _ _ _ Hc0).
        -- exact: (hb_consistent_app_l _ _ _ Hc1).
        -- exact: (hbClosed_app_l _ _ _ Hcl0).
        -- exact: (hbClosed_app_l _ _ _ Hcl1).
        -- apply: (concurrent_commutative_mono O OV hb (ops0' ++ [b]) ops0' _ Hcomm).
           move=> x Hx; rewrite elem_of_app; by left.
        -- exact: (IdNoDup_app_l _ _ _ Hnd0).
        -- exact: (IdNoDup_app_l _ _ _ Hnd1).
        -- exact: Hmem'.
        -- exact: Hpre.
      * have Hbin : b ∈ ops0'.
        { have Hb0a : b ∈ ops0' ++ [a]
            by apply/Hmem; rewrite elem_of_app elem_of_cons; by right; left.
          move: Hb0a; rewrite elem_of_app elem_of_cons elem_of_nil => -[// | [Hba | []]].
          exfalso; apply: Hab; by symmetry. }
        have [ops0f [ops0l Hsplit]] := list_elem_of_split _ _ Hbin.
        subst ops0'.
        have Hc0' : hb_consistent hb (ops0f ++ b :: (ops0l ++ [a])) by move: Hc0; rewrite -app_assoc.
        have Hcl0' : hbClosed hb (ops0f ++ b :: (ops0l ++ [a])) by move: Hcl0; rewrite -app_assoc.
        have Hnd0' : IdNoDup W (ops0f ++ b :: (ops0l ++ [a])) by move: Hnd0; rewrite -app_assoc.
        have [Hbf Hbrest] := idnodup_mid_not_in _ _ _ _ Hnd0'.
        have h_conc : forall x, x ∈ ops0l -> hb_concurrent hb x b.
        { move=> x Hx; split.
          - apply: (hb_consistent_concurrent_r hb b ops0f (ops0l ++ [a]) Hc0' x).
            rewrite elem_of_app; by left.
          - have Hxops1 : x ∈ ops1.
            { have Hx1 : x ∈ ops1 ++ [b] by apply/Hmem; set_solver.
              move: Hx1; rewrite elem_of_app elem_of_cons elem_of_nil => -[// | [Hxb | []]].
              exfalso; apply: Hbrest; rewrite -Hxb elem_of_app; by left. }
            exact: (hb_consistent_concurrent hb b ops1 [] Hc1 x Hxops1). }
        have Haconc : hb_concurrent hb a b.
        { split.
          - apply: (hb_consistent_concurrent hb a (ops0f ++ b :: ops0l) [] _ b);
              [by rewrite -app_assoc | rewrite elem_of_app elem_of_cons; by right; left].
          - have Haops1 : a ∈ ops1.
            { have Ha1 : a ∈ ops1 ++ [b]
                by apply/Hmem; rewrite elem_of_app elem_of_cons; by right; left.
              move: Ha1; rewrite elem_of_app elem_of_cons elem_of_nil => -[// | [Hab' | []]].
              by exfalso; apply: Hab. }
            exact: (hb_consistent_concurrent hb b ops1 [] Hc1 a Haops1). }
        have Hclcore : hbClosed hb (ops0f ++ ops0l)
          by apply: (hbClosed_remove_concurrent hb ops0f ops0l a b);
             [exact: Hcl0' | exact: h_conc].
        have Hcccore : hb_consistent hb (ops0f ++ ops0l).
        { apply: (hb_consistent_sublist hb Hc0); rewrite -!app_assoc.
          apply: sublist_app; first reflexivity.
          apply: sublist_cons; apply: sublist_inserts_r; reflexivity. }
        have Hndcore : IdNoDup W (ops0f ++ ops0l).
        { rewrite /IdNoDup; apply: (sublist_NoDup _ (wid W <$> (ops0f ++ b :: ops0l ++ [a]))).
          - by move: Hnd0'; rewrite /IdNoDup.
          - apply: fmap_sublist.
            apply: sublist_app; first reflexivity.
            apply: sublist_cons; apply: sublist_inserts_r; reflexivity. }
        have Hsrccore : forall x, x ∈ (ops0f ++ ops0l) -> StateSource x
          by move=> x Hx; apply: Hsrc0; move: Hx; rewrite !elem_of_app !elem_of_cons; tauto.
        have Hcmcore : concurrent_commutative O OV hb (ops0f ++ ops0l).
        { apply: (concurrent_commutative_mono O OV hb _ _ _ Hcomm).
          move=> x; rewrite !elem_of_app !elem_of_cons; tauto. }
        have Hpred_a : forall x, co_lt hb x a -> x ∈ (ops0f ++ ops0l).
        { move=> x Hlt.
          have Hx : x ∈ ops0f ++ b :: ops0l
            by apply: (Hcl0 a x (ops0f ++ b :: ops0l) [] _ Hlt); rewrite -!app_assoc.
          move: Hx; rewrite !elem_of_app !elem_of_cons => -[? | [Hxb | ?]];
            [by left | | by right].
          exfalso; subst x; by case: Haconc => _ Hnba; apply: Hnba; case: Hlt. }
        have Hclcorea : hbClosed hb (ops0f ++ ops0l ++ [a]).
        { rewrite app_assoc; apply: hbClosed_append_singleton_of_all_lt;
            [exact: Hclcore | exact: Hpred_a]. }
        have Hcccorea : hb_consistent hb (ops0f ++ ops0l ++ [a]).
        { apply: (hb_consistent_sublist hb Hc0); rewrite -!app_assoc.
          apply: sublist_app; first reflexivity. apply: sublist_cons; reflexivity. }
        have Hndcorea : IdNoDup W (ops0f ++ ops0l ++ [a]).
        { rewrite /IdNoDup; apply: (sublist_NoDup _ (wid W <$> (ops0f ++ b :: ops0l ++ [a]))).
          - by move: Hnd0'; rewrite /IdNoDup.
          - apply: fmap_sublist.
            apply: sublist_app; first reflexivity. apply: sublist_cons; reflexivity. }
        have Hsrccorea : forall x, x ∈ (ops0f ++ ops0l ++ [a]) -> StateSource x
          by move=> x Hx; apply: Hsrc0; move: Hx; rewrite -!app_assoc !elem_of_app !elem_of_cons; tauto.
        have Hcmcorea : concurrent_commutative O OV hb (ops0f ++ ops0l ++ [a]).
        { apply: (concurrent_commutative_mono O OV hb _ _ _ Hcomm).
          move=> x; rewrite -!app_assoc !elem_of_app !elem_of_cons; tauto. }
        have Hmemcore : forall x, x ∈ (ops0f ++ ops0l ++ [a]) <-> x ∈ ops1.
        { apply: (mem_ops0_prefix_iff_ops1 W ops0f ops0l ops1 a b);
            [exact: Hnd0' | exact: Hnd1 | move=> x; move: (Hmem x); by rewrite -!app_assoc]. }
        move: Heff; rewrite -app_assoc => Heff.
        have HA : effect_list O ((ops0f ++ ops0l ++ [a]) ++ [b]) (op_init O) s.
        { move: Heff; rewrite (_ : ops0f ++ b :: (ops0l ++ [a]) = (ops0f ++ b :: ops0l) ++ [a]);
            last by rewrite -app_assoc.
          move=> /effect_list_snoc [m' [Hpre' Ha']].
          have Hbmoved : effect_list O (ops0f ++ ops0l ++ [b]) (op_init O) m'.
          { apply: (effect_list_reorder O OV W hb StateSource RV b ops0f ops0l m').
            - move=> x Hx; apply: Hsrc0; move: Hx; rewrite -!app_assoc !elem_of_app !elem_of_cons; tauto.
            - apply: (concurrent_commutative_mono O OV hb _ _ _ Hcomm).
              move=> x; rewrite -!app_assoc !elem_of_app !elem_of_cons; tauto.
            - exact: h_conc.
            - exact: (hb_consistent_app_l _ _ _ Hc0).
            - exact: (hbClosed_app_l _ _ _ Hcl0).
            - exact: (IdNoDup_app_l _ _ _ Hnd0).
            - exact: Hpre'. }
          move: Hbmoved; rewrite app_assoc => /effect_list_snoc [n [Hn Hbn]].
          have Hsin : StateInv O OV n
            := effect_list_stateInv O OV W hb StateSource RV (ops0f ++ ops0l) n
                 Hsrccore Hcccore Hclcore Hndcore Hn.
          have Hva : isValidState O OV a n.
          { apply: (isValidState_of_history _ _ _ _ _ RV a n (ops0f ++ ops0l));
              try by [exact: Hpred_a | exact: Hcccore | exact: Hclcore
                     | exact: Hn | exact: Hndcore].
            - apply: Hsrc0; set_solver.
            - exact: Hsrccore. }
          have Hvb : isValidState O OV b n.
          { apply: (isValidState_of_history _ _ _ _ _ RV b n (ops0f ++ ops0l));
              try by [exact: Hcccore | exact: Hclcore | exact: Hn | exact: Hndcore].
            - apply: Hsrc0; set_solver.
            - exact: Hsrccore.
            - move=> x Hlt.
              have Hx : x ∈ ops0f := Hcl0' b x ops0f (ops0l ++ [a]) eq_refl Hlt.
              rewrite elem_of_app; by left. }
          have Hab2 : eff_comp O (effect O a) (effect O b) n s.
          { apply: (Hcomm b a n s);
              try by [exact: Hsin | exact: Hva | exact: Hvb].
            - set_solver.
            - set_solver.
            - by rewrite hb_concurrent_symm.
            - by exists m'; split; [exact: Hbn | exact: Ha']. }
          move: Hab2 => [p [Hap Hbp]].
          apply/effect_list_snoc; exists p; split; last exact: Hbp.
          rewrite app_assoc; apply/effect_list_snoc; exists n; split;
            [exact: Hn | exact: Hap]. }
        move: HA => /effect_list_snoc [m [Hcorea Hbm]].
        apply/effect_list_snoc; exists m; split; last exact: Hbm.
        apply: (IH (ops0f ++ ops0l ++ [a]) m);
          [ exact: Hsrccorea
          | move=> x Hx; apply: Hsrc1; rewrite elem_of_app; by left
          | exact: Hcccorea
          | exact: (hb_consistent_app_l _ _ _ Hc1)
          | exact: Hclcorea
          | exact: (hbClosed_app_l _ _ _ Hcl1)
          | exact: Hcmcorea
          | exact: Hndcorea
          | exact: (IdNoDup_app_l _ _ _ Hnd1)
          | exact: Hmemcore
          | exact: Hcorea ].
Qed.

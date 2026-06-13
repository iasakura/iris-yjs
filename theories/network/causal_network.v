(** Causal-broadcast networks (Yjs-independent).

    Port of [LeanYjs/Network/CausalNetwork.lean]. A network is a family of
    per-node event histories (broadcast / deliver). The happens-before relation
    [HappensBefore] induced by local order + causal delivery is a strict partial
    order; packaged through [network_causal_order] it yields a [CausalOrder] for
    the [causal_order]/[strong_causal_order] framework. The list of messages
    delivered at a node is then causally consistent and duplicate-free. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id.
From yjs.network Require Import causal_order hb_closed strong_causal_order.

Section causal_network.
Context {A M : Type} `{EqDecisionA : EqDecision A} `{EqDecisionM : EqDecision M}.
(** [messageId] is the [Message] class: every operation carries a message id. *)
Context (messageId : A -> M).

Inductive Event : Type := EvBroadcast (a : A) | EvDeliver (a : A).

Global Instance Event_eq_dec : EqDecision Event.
Proof using A EqDecisionA. solve_decision. Defined.

Definition event_id (e : Event) : M :=
  match e with EvBroadcast a => messageId a | EvDeliver a => messageId a end.

(** Per-node histories, each duplicate-free. *)
Record NodeHistories := {
  histories : ClientId -> list Event;
  event_distinct : forall i, NoDup (histories i);
}.

(** [e1] occurs strictly before [e2] in node [i]'s history. *)
Definition locallyOrdered (nh : NodeHistories) (i : ClientId) (e1 e2 : Event) : Prop :=
  exists l1 l2 l3, histories nh i = l1 ++ [e1] ++ l2 ++ [e2] ++ l3.

(** An element in the middle of a duplicate-free list is absent from its prefix,
    and its split point is unique. *)
Lemma elem_not_in_of_nodup_mid {X} (p s : list X) (x : X) :
  NoDup (p ++ x :: s) -> x ∉ p.
Proof.
  rewrite NoDup_app => -[_ [Hcr _]] Hin.
  by apply: (Hcr x Hin); rewrite elem_of_cons; left.
Qed.

Lemma nodup_app_mid_uniq {X} (x : X) :
  forall (p1 s1 p2 s2 : list X),
  x ∉ p1 -> x ∉ p2 ->
  p1 ++ x :: s1 = p2 ++ x :: s2 -> p1 = p2 /\ s1 = s2.
Proof.
  induction p1 as [|y p1 IH]; intros s1 [|z p2] s2 Hx1 Hx2 Heq; simpl in Heq.
  - injection Heq as Hs; subst; done.
  - injection Heq as Hxz _; subst z; exfalso; apply Hx2; rewrite elem_of_cons; by left.
  - injection Heq as Hxy _; subst y; exfalso; apply Hx1; rewrite elem_of_cons; by left.
  - injection Heq as -> Heq.
    assert (x ∉ p1) as Hx1' by (intros Hin; apply Hx1; rewrite elem_of_cons; by right).
    assert (x ∉ p2) as Hx2' by (intros Hin; apply Hx2; rewrite elem_of_cons; by right).
    by destruct (IH s1 p2 s2 Hx1' Hx2' Heq) as [-> ->].
Qed.

Record NetworkBase := {
  nb_nodes :> NodeHistories;
  deliver_has_a_cause : forall i e,
    EvDeliver e ∈ histories nb_nodes i -> exists j, EvBroadcast e ∈ histories nb_nodes j;
  deliver_locally : forall i e,
    EvDeliver e ∈ histories nb_nodes i ->
    locallyOrdered nb_nodes i (EvBroadcast e) (EvDeliver e);
  msg_id_unique : forall mi mj i j,
    EvBroadcast mi ∈ histories nb_nodes i -> EvBroadcast mj ∈ histories nb_nodes j ->
    messageId mi = messageId mj -> i = j /\ mi = mj;
}.

Inductive HappensBefore (nb : NetworkBase) : A -> A -> Prop :=
  | hb_bb i e1 e2 :
      locallyOrdered nb i (EvBroadcast e1) (EvBroadcast e2) -> HappensBefore nb e1 e2
  | hb_db i e1 e2 :
      locallyOrdered nb i (EvDeliver e1) (EvBroadcast e2) -> HappensBefore nb e1 e2
  | hb_trans e1 e2 e3 :
      HappensBefore nb e1 e2 -> HappensBefore nb e2 e3 -> HappensBefore nb e1 e3.

Inductive HappensBeforeOnlyBroadcast (nb : NetworkBase) : A -> A -> Prop :=
  | hbob_bb i e1 e2 :
      locallyOrdered nb i (EvBroadcast e1) (EvBroadcast e2) -> HappensBeforeOnlyBroadcast nb e1 e2
  | hbob_trans e1 e2 e3 :
      HappensBeforeOnlyBroadcast nb e1 e2 -> HappensBeforeOnlyBroadcast nb e2 e3 ->
      HappensBeforeOnlyBroadcast nb e1 e3.

Definition HappensBeforeOrEqual (nb : NetworkBase) (a b : A) : Prop :=
  a = b \/ HappensBefore nb a b.

Record CausalNetwork := {
  cn_base :> NetworkBase;
  causal_delivery : forall i e1 e2,
    EvDeliver e2 ∈ histories cn_base i -> HappensBefore cn_base e1 e2 ->
    locallyOrdered cn_base i (EvDeliver e1) (EvDeliver e2);
}.

(** ** Happens-before transitivity with [HappensBeforeOrEqual] on one side *)
Lemma HappensBefore_trans1 {nb : NetworkBase} {a b c : A} :
  HappensBeforeOrEqual nb a b -> HappensBefore nb b c -> HappensBefore nb a c.
Proof. move=> [<- //| Hab] Hbc; apply: hb_trans; [exact: Hab | exact: Hbc]. Qed.

Lemma HappensBefore_trans2 {nb : NetworkBase} {a b c : A} :
  HappensBefore nb a b -> HappensBeforeOrEqual nb b c -> HappensBefore nb a c.
Proof. move=> Hab [<- //| Hbc]; apply: hb_trans; [exact: Hab | exact: Hbc]. Qed.

(** Any happens-before either is broadcast-only or factors through a single
    [Deliver a' <_i Broadcast b'] step. *)
Lemma HappensBefore_decompose (cn : CausalNetwork) (a b : A) :
  HappensBefore cn a b ->
  HappensBeforeOnlyBroadcast cn a b \/
  exists a' b' i,
    HappensBeforeOrEqual cn a a' /\
    locallyOrdered cn i (EvDeliver a') (EvBroadcast b') /\
    HappensBeforeOrEqual cn b' b.
Proof.
  move=> H; elim: H => [i e1 e2 Hlo | i e1 e2 Hlo | e1 e2 e3 Hab IH1 Hbc IH2].
  - left; apply: hbob_bb; exact: Hlo.
  - right; exists e1, e2, i; split; [by left | split; [exact: Hlo | by left]].
  - case: IH1 => [Hbob12 | [a' [b' [j [Ha1 [Hlo1 Hb2]]]]]].
    + case: IH2 => [Hbob23 | [a' [b' [j [Ha2 [Hlo2 Hb3]]]]]].
      * left; apply: hbob_trans; [exact: Hbob12 | exact: Hbob23].
      * right; exists a', b', j; split;
          [right; exact: HappensBefore_trans2 Hab Ha2 | split; [exact: Hlo2 | exact: Hb3]].
    + right; exists a', b', j; split;
        [exact: Ha1 | split; [exact: Hlo1 | right; exact: HappensBefore_trans1 Hb2 Hbc]].
Qed.

(** Local order is irreflexive-asymmetric: two events can't be locally ordered
    both ways (the histories are duplicate-free). *)
Lemma locallyOrdered_asymm {nb : NetworkBase} {i : ClientId} {e1 e2 : Event} :
  locallyOrdered nb i e1 e2 -> locallyOrdered nb i e2 e1 -> False.
Proof.
  move=> [L1 [L2 [L3 H1]]] [M1 [M2 [M3 H2]]].
  have Hnd := event_distinct nb i.
  have HL1 : histories nb i = L1 ++ e1 :: (L2 ++ [e2] ++ L3) by rewrite H1.
  have HM1 : histories nb i = (M1 ++ [e2] ++ M2) ++ e1 :: M3 by rewrite H2 -!app_assoc.
  have HndL : NoDup (L1 ++ e1 :: (L2 ++ [e2] ++ L3)) by rewrite -HL1.
  have HndM : NoDup ((M1 ++ [e2] ++ M2) ++ e1 :: M3) by rewrite -HM1.
  have He1L1 := elem_not_in_of_nodup_mid _ _ _ HndL.
  have He1M := elem_not_in_of_nodup_mid _ _ _ HndM.
  have Heq := eq_trans (eq_sym HL1) HM1.
  have [HL1eq _] := nodup_app_mid_uniq e1 _ _ _ _ He1L1 He1M Heq.
  have He2L1 : e2 ∈ L1 by rewrite HL1eq; set_solver.
  move: HndL; rewrite NoDup_app => -[_ [Hcr _]].
  apply: (Hcr e2 He2L1); set_solver.
Qed.

Lemma locallyOrdered_trans {nb : NetworkBase} {i : ClientId} {e1 e2 e3 : Event} :
  locallyOrdered nb i e1 e2 -> locallyOrdered nb i e2 e3 -> locallyOrdered nb i e1 e3.
Proof.
  move=> [L1 [L2 [L3 H1]]] [N1 [N2 [N3 H2]]].
  have Hnd := event_distinct nb i.
  have HP1 : histories nb i = (L1 ++ [e1] ++ L2) ++ e2 :: L3 by rewrite H1 -!app_assoc.
  have HN1 : histories nb i = N1 ++ e2 :: (N2 ++ [e3] ++ N3) by rewrite H2.
  have HndP : NoDup ((L1 ++ [e1] ++ L2) ++ e2 :: L3) by rewrite -HP1.
  have HndN : NoDup (N1 ++ e2 :: (N2 ++ [e3] ++ N3)) by rewrite -HN1.
  have He2P1 := elem_not_in_of_nodup_mid _ _ _ HndP.
  have He2N1 := elem_not_in_of_nodup_mid _ _ _ HndN.
  have Heq := eq_trans (eq_sym HP1) HN1.
  have [_ HL3] := nodup_app_mid_uniq e2 _ _ _ _ He2P1 He2N1 Heq.
  exists L1, (L2 ++ [e2] ++ N2), N3.
  by rewrite H1 HL3 -!app_assoc.
Qed.

Lemma HappensBeforeOnlyBroadcast_locallyOrdered (nb : NetworkBase) (a b : A) :
  HappensBeforeOnlyBroadcast nb a b ->
  exists i, locallyOrdered nb i (EvBroadcast a) (EvBroadcast b).
Proof.
  move=> H; elim: H => [i e1 e2 Hlo | e1 e2 e3 _ IH1 _ IH2].
  - by exists i.
  - have [i Hi] := IH1; have [j Hj] := IH2.
    have Hi_e2 : EvBroadcast e2 ∈ histories nb i
      by case: Hi => l1 [l2 [l3 ->]]; set_solver.
    have Hj_e2 : EvBroadcast e2 ∈ histories nb j
      by case: Hj => l1 [l2 [l3 ->]]; set_solver.
    have [Hij _] := msg_id_unique nb e2 e2 i j Hi_e2 Hj_e2 eq_refl.
    subst j; exists i; exact: locallyOrdered_trans Hi Hj.
Qed.

(** Happens-before is asymmetric (hence irreflexive). *)
Lemma HappensBefore_asymm (cn : CausalNetwork) (a b : A) :
  HappensBefore cn a b -> HappensBefore cn b a -> False.
Proof.
  move=> Hab Hba.
  have Haa : HappensBefore cn a a by apply: hb_trans; [exact: Hab | exact: Hba].
  case: (HappensBefore_decompose cn a a Haa) => [Hbob | [a' [b' [i [Ha [Hlo Hb]]]]]].
  - have [j Hj] := HappensBeforeOnlyBroadcast_locallyOrdered _ _ _ Hbob.
    exact: (locallyOrdered_asymm Hj Hj).
  - have Hmem_da' : EvDeliver a' ∈ histories cn i
      by case: Hlo => l1 [l2 [l3 ->]]; set_solver.
    have Hba' : HappensBefore cn b' a'.
    { apply: (HappensBefore_trans1 Hb).
      apply: (HappensBefore_trans2 Hab).
      right; exact: (HappensBefore_trans2 Hba Ha). }
    have Hlo_db_da : locallyOrdered cn i (EvDeliver b') (EvDeliver a')
      := causal_delivery cn i b' a' Hmem_da' Hba'.
    have Hmem_db' : EvDeliver b' ∈ histories cn i
      by case: Hlo_db_da => l1 [l2 [l3 ->]]; set_solver.
    have Hlo_bb'_db' : locallyOrdered cn i (EvBroadcast b') (EvDeliver b')
      := deliver_locally cn i b' Hmem_db'.
    have Hlo_bb'_da' : locallyOrdered cn i (EvBroadcast b') (EvDeliver a')
      := locallyOrdered_trans Hlo_bb'_db' Hlo_db_da.
    exact: (locallyOrdered_asymm Hlo_bb'_da' Hlo).
Qed.

(** A causal network induces a [CausalOrder] (happens-before-or-equal). *)
Program Definition network_causal_order (cn : CausalNetwork) : @CausalOrder A :=
  MkCausalOrder (HappensBeforeOrEqual cn) _.
Next Obligation.
  move=> cn; split.
  - split.
    + by move=> a; left.
    + move=> a b c Hab Hbc.
      case: Hab => [->|Hab]; first exact: Hbc.
      case: Hbc => [<-|Hbc]; first by right.
      right; apply: hb_trans; [exact: Hab | exact: Hbc].
  - move=> a b Hab Hba.
    case: Hab => [//|Hab]; case: Hba => [Hba|Hba];
      [exact: (eq_sym Hba) | exfalso; exact: (HappensBefore_asymm cn a b Hab Hba)].
Qed.

(** ** Delivered-message lists *)

Definition deliverP (e : Event) : option A :=
  match e with EvDeliver a => Some a | EvBroadcast _ => None end.

(** The messages delivered at node [i], in delivery order. *)
Definition toDeliverMessages (nh : NodeHistories) (i : ClientId) : list A :=
  omap deliverP (histories nh i).

(** Splitting [omap deliverP] at an element reflects back to a split of the
    history at the corresponding [EvDeliver]. *)
Lemma omap_deliver_cons_inv (l : list Event) :
  forall (pre suf : list A) (m : A),
  omap deliverP l = pre ++ m :: suf ->
  exists k1 k2, l = k1 ++ EvDeliver m :: k2 /\ omap deliverP k1 = pre /\ omap deliverP k2 = suf.
Proof.
  induction l as [|x l IH]; intros pre suf m Heq; simpl in Heq.
  - by destruct pre; simplify_eq.
  - destruct x as [a|a]; simpl in Heq.
    + destruct (IH pre suf m Heq) as [k1 [k2 [Hl [Hk1 Hk2]]]].
      exists (EvBroadcast a :: k1), k2; split; [by rewrite Hl | split; [exact: Hk1 | exact: Hk2]].
    + destruct pre as [|p pre]; simpl in Heq.
      * injection Heq as <- Hsuf; by exists [], l.
      * injection Heq as <- Heq.
        destruct (IH pre suf m Heq) as [k1 [k2 [Hl [Hk1 Hk2]]]].
        exists (EvDeliver a :: k1), k2;
          split; [by rewrite Hl | split; [by rewrite -Hk1 | exact: Hk2]].
Qed.

Lemma toDeliverMessages_histories (cn : CausalNetwork) (i : ClientId)
    (l1 l2 l3 : list A) (m m' : A) :
  toDeliverMessages cn i = l1 ++ [m] ++ l2 ++ [m'] ++ l3 ->
  exists k1 k2 k3, histories cn i = k1 ++ [EvDeliver m] ++ k2 ++ [EvDeliver m'] ++ k3.
Proof.
  rewrite /toDeliverMessages => Heq.
  have Heq' : omap deliverP (histories cn i) = l1 ++ m :: (l2 ++ m' :: l3)
    by rewrite Heq.
  have [k1 [k2 [Hl [_ Hk2]]]] := omap_deliver_cons_inv _ _ _ _ Heq'.
  have [k1' [k2' [Hk2eq [_ _]]]] := omap_deliver_cons_inv _ _ _ _ Hk2.
  exists k1, k1', k2'.
  by rewrite Hl Hk2eq.
Qed.

Lemma toDeliverMessages_Nodup (cn : CausalNetwork) (i : ClientId) :
  NoDup (toDeliverMessages cn i).
Proof.
  rewrite /toDeliverMessages.
  move: (event_distinct cn i); elim: (histories cn i) => [|x l IH] /= Hnd.
  - by constructor.
  - move: Hnd; rewrite NoDup_cons => -[Hx Hnd].
    case: x Hx => [a|a] Hx /=; first exact: IH Hnd.
    apply: NoDup_cons_2; last exact: IH Hnd.
    rewrite list_elem_of_omap => -[y [Hy Hdy]].
    case: y Hy Hdy => [b|b] Hy //= [?]; subst b.
    by apply: Hx.
Qed.

(** The messages delivered at a node are causally consistent under the induced
    order: an earlier-delivered message never happens-after a later one. *)
Lemma hb_consistent_local_history (cn : CausalNetwork) (i : ClientId) :
  hb_consistent (network_causal_order cn) (toDeliverMessages cn i).
Proof.
  have Hnd := toDeliverMessages_Nodup cn i.
  suff Haux : forall ms ms', ms ++ ms' = toDeliverMessages cn i ->
    hb_consistent (network_causal_order cn) ms'.
  { exact: (Haux [] _ eq_refl). }
  move=> ms ms'; move: ms; elim: ms' => [|h t IH] ms Hms.
  - constructor.
  - apply: hb_consistent_cons.
    + apply: (IH (ms ++ [h])); by rewrite -app_assoc.
    + move=> mm Hmm Hle.
      have [ta [tb Ht]] := list_elem_of_split _ _ Hmm.
      have Hsplit : toDeliverMessages cn i = ms ++ [h] ++ ta ++ [mm] ++ tb
        by rewrite -Hms Ht.
      have [k1 [k2 [k3 Hhist]]] := toDeliverMessages_histories cn i _ _ _ _ _ Hsplit.
      have Hlo : locallyOrdered cn i (EvDeliver h) (EvDeliver mm) by exists k1, k2, k3.
      case: Hle => [Hmm_eq | Hmm_hb].
      * subst mm.
        move: Hnd; rewrite Hsplit.
        rewrite (_ : ms ++ [h] ++ ta ++ [h] ++ tb = (ms ++ [h] ++ ta) ++ h :: tb);
          last by rewrite -!app_assoc.
        rewrite NoDup_app => -[_ [Hcr _]].
        apply: (Hcr h); [set_solver | by rewrite elem_of_cons; left].
      * have Hmem_dh : EvDeliver h ∈ histories cn i
          by case: Hlo => p1 [p2 [p3 ->]]; set_solver.
        have Hlo' : locallyOrdered cn i (EvDeliver mm) (EvDeliver h)
          := causal_delivery cn i mm h Hmem_dh Hmm_hb.
        exact: (locallyOrdered_asymm Hlo Hlo').
Qed.

End causal_network.

(** The Yjs operation network: a [CausalNetwork]/[OperationNetwork] whose
    messages are Yjs operations, packaged with the per-client total-order
    discipline ([histories_client_id]) and the per-client clock discipline
    ([histories_UniqueId]). Port of [LeanYjs/Network/Yjs/YjsNetwork.lean]
    (the [YjsOperationNetwork] structure and downward). This file derives the
    network-structural facts feeding the abstract convergence theorem
    [yjs_strong_convergence]: the distinct-client-id discipline for concurrent
    operations, and (ultimately) the operation replay validity. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set.
From yjs.algorithm Require Import basic insert_basic invariant_yjsarray
  insert_loop delete commutativity.
From yjs.network Require Import causal_order hb_closed strong_causal_order
  causal_network operation_network yjs_network.

Section yjs_operation_network.
Context {A : Type} `{EqDA : EqDecision A}.

Local Notation Op := (@YjsOperation A).
Local Notation opid := (@YjsOperation_id A).
Local Notation O := (@YjsOp A EqDA).

(** A message is valid in a state when its insert resolves to a valid item. *)
Definition YjsIsValidMessage (s : YjsState A) (op : Op) : Prop :=
  IsValidMessage (st_items s) op.

(** A network's underlying operation network (Yjs operations, Yjs effect). *)
Local Notation YjsOpNet := (@OperationNetwork Op YjsId opid O YjsIsValidMessage).

(** The per-client clock discipline: an operation's clock strictly exceeds the
    clocks of all same-client items already present in the replayed state. *)
Definition YjsOperation_UniqueId (op : Op) (s : YjsState A) : Prop :=
  forall x, x ∈ st_items s ->
    clientId (item_id x) = clientId (opid op) ->
    clock (item_id x) < clock (opid op).

(** The Yjs operation network. Broadcasts carry the broadcasting client's id,
    and the per-client clocks are strictly increasing along any history. *)
Record YjsOperationNetwork := {
  yon_net :> YjsOpNet;
  histories_client_id : forall (e : Op) (i : ClientId),
    EvBroadcast e ∈ histories yon_net i -> clientId (opid e) = i;
  histories_UniqueId : forall (e : Op) (i : ClientId)
      (hist1 hist2 : list Event) (array : YjsState A),
    histories yon_net i = hist1 ++ [EvBroadcast e] ++ hist2 ->
    interpHistory O hist1 (op_init O) array ->
    YjsOperation_UniqueId e array;
}.

(** Two elements of a list are locally ordered one way or the other, or equal. *)
Lemma elem_of_two_split {X} (l : list X) (x y : X) :
  x ∈ l -> y ∈ l ->
  (exists l1 l2 l3, l = l1 ++ [x] ++ l2 ++ [y] ++ l3) \/
  (exists l1 l2 l3, l = l1 ++ [y] ++ l2 ++ [x] ++ l3) \/
  x = y.
Proof.
  move=> Hx Hy.
  have [p [s Hl]] := list_elem_of_split _ _ Hx.
  have Hy' : y ∈ p ++ x :: s by rewrite -Hl.
  move: Hy'; rewrite elem_of_app elem_of_cons => -[Hyp | [Hyx | Hys]].
  - right; left.
    have [pa [pb Hp]] := list_elem_of_split _ _ Hyp.
    by exists pa, pb, s; rewrite Hl Hp -!app_assoc.
  - by right; right; symmetry.
  - left.
    have [sa [sb Hs]] := list_elem_of_split _ _ Hys.
    by exists p, sa, sb; rewrite Hl Hs.
Qed.

(** Two operations broadcast in the same node history are never concurrent:
    they are locally ordered, hence happens-before-related. *)
Lemma same_history_not_hb_concurrent
    (cn : @CausalNetwork Op YjsId opid)
    (i : ClientId) (a b : Op) :
  EvBroadcast a ∈ histories cn i ->
  EvBroadcast b ∈ histories cn i ->
  ¬ hb_concurrent (network_causal_order opid cn) a b.
Proof using A EqDA.
  move=> Ha Hb [Hnab Hnba].
  case: (elem_of_two_split (histories cn i) (EvBroadcast a) (EvBroadcast b) Ha Hb)
    => [Hlo | [Hlo | Heq]].
  - apply: Hnab; right; exact: (hb_bb opid cn i a b Hlo).
  - apply: Hnba; right; exact: (hb_bb opid cn i b a Hlo).
  - apply: Hnab; left; congruence.
Qed.

(** A delivered message reflects an [EvDeliver] in the history. *)
Lemma deliver_mem_of_toDeliver_mem (nh : @NodeHistories Op)
    (k : ClientId) (m : Op) :
  m ∈ toDeliverMessages nh k -> EvDeliver m ∈ histories nh k.
Proof using A.
  rewrite /toDeliverMessages list_elem_of_omap => -[ev [Hev Hdel]].
  destruct ev as [x | x]; simpl in Hdel; [done | injection Hdel as ->; exact Hev].
Qed.

(** An [EvDeliver] in the history reflects a delivered message. *)
Lemma toDeliver_mem_of_deliver_mem (nh : @NodeHistories Op)
    (k : ClientId) (m : Op) :
  EvDeliver m ∈ histories nh k -> m ∈ toDeliverMessages nh k.
Proof using A.
  move=> Hm; rewrite /toDeliverMessages list_elem_of_omap.
  by exists (EvDeliver m).
Qed.

(** The mathematical heart of the id discipline: concurrent delivered messages
    come from distinct clients. Each is broadcast by some client; if their
    client ids agreed, [histories_client_id] would put both broadcasts in the
    same node history, contradicting [same_history_not_hb_concurrent]. *)
Lemma hb_concurrent_diff_id (network : YjsOperationNetwork) (i : ClientId)
    (a b : Op) :
  a ∈ toDeliverMessages network i ->
  b ∈ toDeliverMessages network i ->
  hb_concurrent (network_causal_order opid network) a b ->
  clientId (opid a) <> clientId (opid b).
Proof using A EqDA.
  move=> Ha Hb Hconc Hcid.
  have HdA := deliver_mem_of_toDeliver_mem network i a Ha.
  have HdB := deliver_mem_of_toDeliver_mem network i b Hb.
  have [ia HbA] := deliver_has_a_cause opid network i a HdA.
  have [ib HbB] := deliver_has_a_cause opid network i b HdB.
  have HiA := histories_client_id network a ia HbA.
  have HiB := histories_client_id network b ib HbB.
  have Hii : ia = ib by rewrite -HiA -HiB Hcid.
  rewrite Hii in HbA.
  have Hno := same_history_not_hb_concurrent network ib a b HbA HbB.
  exact: Hno Hconc.
Qed.

(** Mapping a function injective on a list's elements preserves [NoDup]. *)
Lemma NoDup_fmap_inj_on {X Y} (f : X -> Y) (l : list X) :
  (forall x y, x ∈ l -> y ∈ l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (f <$> l).
Proof.
  elim: l => [|x l IH] Hinj Hnd /=.
  - constructor.
  - move: Hnd; rewrite NoDup_cons => -[Hxnotin Hnd].
    apply: NoDup_cons_2.
    + rewrite list_elem_of_fmap => -[y [Hxy Hy]].
      have Hxy' : x = y by apply: Hinj; [set_solver | set_solver | done].
      by subst y; apply: Hxnotin.
    + apply: IH; [move=> a b Ha Hb; apply: Hinj; set_solver | done].
Qed.

(** The list delivered at a node is happens-before-closed: a strict predecessor
    of any delivered message is itself delivered earlier in the list. The
    network's [causal_delivery] places the predecessor's delivery in the
    history, and consistency keeps it out of the suffix. *)
Lemma toDeliverMessages_hbClosed (cn : @CausalNetwork Op YjsId opid) (i : ClientId) :
  hbClosed (network_causal_order opid cn) (toDeliverMessages cn i).
Proof using A EqDA.
  have Hcons := hb_consistent_local_history opid cn i.
  move=> a b l1 l2 Heq Hlt.
  have Ha : a ∈ toDeliverMessages cn i by rewrite Heq; set_solver.
  have HdA := deliver_mem_of_toDeliver_mem cn i a Ha.
  have Hhb : HappensBefore opid cn b a.
  { move: (proj1 Hlt) (proj2 Hlt) => [Heqab | Hhb'] Hne;
      [by case: Hne | exact Hhb']. }
  have Hlocal := causal_delivery opid cn i b a HdA Hhb.
  have HdB : EvDeliver b ∈ histories cn i
    by move: Hlocal => [p1 [p2 [p3 Hh]]]; rewrite Hh; set_solver.
  have Hb := toDeliver_mem_of_deliver_mem cn i b HdB.
  have Hnotin : b ∉ l2.
  { move=> Hbin.
    apply: (hb_consistent_concurrent_r (network_causal_order opid cn) a l1 l2 _ b Hbin
              (proj1 Hlt)).
    by rewrite -Heq. }
  move: Hb; rewrite Heq elem_of_app elem_of_cons => -[Hb1 | [Hba | Hb2]].
  - exact: Hb1.
  - by case: (proj2 Hlt).
  - by case: Hnotin.
Qed.

(** The ids of the messages delivered at a node are duplicate-free: distinct
    deliveries have distinct broadcasts, and [msg_id_unique] makes equal ids
    force equal operations. *)
Lemma toDeliverMessages_IdNoDup (cn : @CausalNetwork Op YjsId opid) (i : ClientId) :
  IdNoDup YjsWithId (toDeliverMessages cn i).
Proof using A EqDA.
  rewrite /IdNoDup.
  apply: NoDup_fmap_inj_on; last exact: (toDeliverMessages_Nodup opid cn i).
  move=> x y Hx Hy Hid.
  have Hdx := deliver_mem_of_toDeliver_mem cn i x Hx.
  have Hdy := deliver_mem_of_toDeliver_mem cn i y Hy.
  have [c1 Hbx] := deliver_has_a_cause opid cn i x Hdx.
  have [c2 Hby] := deliver_has_a_cause opid cn i y Hdy.
  have [_ Heq] := msg_id_unique opid cn x y c1 c2 Hbx Hby Hid.
  exact: Heq.
Qed.

(** The Yjs effect is a (partial) function, so replaying a fixed operation list
    is deterministic. *)
Lemma yjs_op_effect_det (op : Op) (s s1 s2 : YjsState A) :
  op_effect O op s s1 -> op_effect O op s s2 -> s1 = s2.
Proof using A EqDA.
  destruct op as [input | id did]; simpl.
  - by move=> H1 H2; rewrite H1 in H2; injection H2.
  - by move=> -> ->.
Qed.

Lemma effect_list_det (ops : list Op) (s s1 s2 : YjsState A) :
  effect_list O ops s s1 -> effect_list O ops s s2 -> s1 = s2.
Proof using A EqDA.
  elim: ops s s1 s2 => [|op ops IH] s s1 s2.
  - by move=> /(effect_list_nil O) <- /(effect_list_nil O) <-.
  - move=> /(effect_list_cons O) [m1 [H1 Hr1]] /(effect_list_cons O) [m2 [H2 Hr2]].
    have Hm : m1 = m2 := yjs_op_effect_det op s m1 m2 H1 H2.
    subst m2; exact: IH m1 s1 s2 Hr1 Hr2.
Qed.

(** A message's [StateSource]: it is broadcast somewhere in the network. *)
Definition NetStateSource (network : YjsOperationNetwork) (a : Op) : Prop :=
  exists k, EvBroadcast a ∈ histories network k.

(** Network convergence (relational form): replaying the deliveries at any two
    nodes (with the same message set) over the empty document reaches the same
    state. All structural hypotheses of [yjs_strong_convergence] are discharged
    from the network; the operation-replay validity is the remaining input. *)
Lemma YjsOperationNetwork_converge_rel (network : YjsOperationNetwork)
    (i j : ClientId) (s : YjsState A) :
  OperationReplayValidity O YjsOV YjsWithId
    (network_causal_order opid network) (NetStateSource network) ->
  (forall m, m ∈ toDeliverMessages network i <-> m ∈ toDeliverMessages network j) ->
  effect_list O (toDeliverMessages network i) (op_init O) s ->
  effect_list O (toDeliverMessages network j) (op_init O) s.
Proof using A EqDA.
  move=> RV Hmem Heff.
  apply: (yjs_strong_convergence (network_causal_order opid network)
            (NetStateSource network) RV
            (toDeliverMessages network i) (toDeliverMessages network j) s).
  - move=> x Hx; have Hd := deliver_mem_of_toDeliver_mem network i x Hx.
    have [c Hc] := deliver_has_a_cause opid network i x Hd; by exists c.
  - move=> x Hx; have Hd := deliver_mem_of_toDeliver_mem network j x Hx.
    have [c Hc] := deliver_has_a_cause opid network j x Hd; by exists c.
  - exact: hb_consistent_local_history opid network i.
  - exact: hb_consistent_local_history opid network j.
  - exact: toDeliverMessages_hbClosed network i.
  - exact: toDeliverMessages_hbClosed network j.
  - move=> a b Ha Hb Hconc; exact: (hb_concurrent_diff_id network i a b Ha Hb Hconc).
  - exact: toDeliverMessages_IdNoDup network i.
  - exact: toDeliverMessages_IdNoDup network j.
  - exact: Hmem.
  - exact: Heff.
Qed.

(** Network convergence (functional form, matching the Lean [_converge']): the
    final documents at two nodes with the same delivered message set agree. *)
Theorem YjsOperationNetwork_converge (network : YjsOperationNetwork)
    (i j : ClientId) (res0 res1 : YjsState A) :
  OperationReplayValidity O YjsOV YjsWithId
    (network_causal_order opid network) (NetStateSource network) ->
  effect_list O (toDeliverMessages network i) (op_init O) res0 ->
  effect_list O (toDeliverMessages network j) (op_init O) res1 ->
  (forall m, m ∈ toDeliverMessages network i <-> m ∈ toDeliverMessages network j) ->
  res0 = res1.
Proof using A EqDA.
  move=> RV Heff0 Heff1 Hmem.
  have Heff1' := YjsOperationNetwork_converge_rel network i j res0 RV Hmem Heff0.
  exact: effect_list_det _ _ _ _ Heff1' Heff1.
Qed.

End yjs_operation_network.

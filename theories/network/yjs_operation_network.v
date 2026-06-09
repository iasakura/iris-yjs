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
From yjs.network Require Import causal_order strong_causal_order causal_network
  operation_network yjs_network.

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

End yjs_operation_network.

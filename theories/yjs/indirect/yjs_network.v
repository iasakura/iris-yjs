(** Indirect network convergence. Port of
    [LeanYjs/Indirect/Network/Yjs/YjsNetwork.lean]. The realistic by-id replay
    converges because it is the erasure of the verified direct replay: from an
    indirect replay we recover a direct one (threading the state invariant via
    the operation replay validity), then transport the direct convergence. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set.
From yjs.algorithm Require Import basic insert_basic invariant_yjsarray delete.
From yjs.crdt.operation Require Import causal_order hb_closed strong_causal_order.
From yjs.crdt.network Require Import causal_network operation_network.
From yjs.network Require Import yjs_network yjs_operation_network yjs_replay_validity.
From yjs.indirect Require Import item basic insert_basic delete equivalence.

Section indirect_network.
Context {A : Type} `{EqDA : EqDecision A}.

Local Notation Op := (@YjsOperation A).
Local Notation O := (@YjsOp A EqDA).
Local Notation opid := (@YjsOperation_id A).

(** The indirect effect of an operation (relational, like the direct one). *)
Definition ieffect (op : Op) (s s' : IYjsState A) : Prop :=
  match op with
  | OpInsert input => IYjsState_insert s input = Some s'
  | OpDelete _ did => s' = ideleteById s did
  end.

Fixpoint ieffect_list (ops : list Op) (s s' : IYjsState A) : Prop :=
  match ops with
  | [] => s = s'
  | op :: ops' => exists m, ieffect op s m /\ ieffect_list ops' m s'
  end.

(** Recover a direct replay from an indirect one (with the same erasure),
    threading the direct-state invariant via the replay validity. Port of
    [direct_of_indirect_suffix]. *)
Lemma direct_of_indirect_suffix (network : YjsOperationNetwork)
    (RV : OperationReplayValidity O YjsOV YjsWithId
            (network_causal_order opid network) (NetStateSource network)) :
  forall (preOps restOps : list Op) (ds : YjsState A) (ires : IYjsState A),
  (forall x, x ∈ preOps ++ restOps -> NetStateSource network x) ->
  hb_consistent (network_causal_order opid network) (preOps ++ restOps) ->
  hbClosed (network_causal_order opid network) (preOps ++ restOps) ->
  IdNoDup YjsWithId (preOps ++ restOps) ->
  effect_list O preOps (op_init O) ds ->
  ieffect_list restOps (ofDirectState ds) ires ->
  exists dres, effect_list O restOps ds dres /\ ires = ofDirectState dres.
Proof using A EqDA.
  set hb := network_causal_order opid network.
  move=> preOps restOps; move: preOps.
  elim: restOps => [|op restOps IH] preOps ds ires Hsrc Hcons Hclosed Hnd Hpre Hires.
  - exists ds; split; [by apply/(effect_list_nil O) | by move: Hires => /= ->].
  - move: Hires => /= [m [Hstep Hrest]].
    have Hinv : YjsStateInvariant ds.
    { apply: (effect_list_stateInv O YjsOV YjsWithId hb (NetStateSource network) RV preOps ds).
      - move=> x Hx; apply: Hsrc; rewrite elem_of_app; by left.
      - exact: (hb_consistent_app_l hb preOps (op :: restOps) Hcons).
      - exact: (hbClosed_app_l hb preOps (op :: restOps) Hclosed).
      - exact: (IdNoDup_app_l YjsWithId preOps (op :: restOps) Hnd).
      - exact: Hpre. }
    have [ds' [Hstepd Hmeq]] : exists ds', op_effect O op ds ds' /\ m = ofDirectState ds'.
    { destruct op as [input | id did].
      - move: Hstep; rewrite /ieffect (IYjsState_insert_ofDirect ds input Hinv)
          => /fmap_Some [ds' [Hins Hm]].
        by exists ds'.
      - move: Hstep; rewrite /ieffect (ideleteById_ofDirect ds did) => Hm.
        by exists (deleteById ds did). }
    have Hpre' : effect_list O (preOps ++ [op]) (op_init O) ds'
      by apply/(effect_list_snoc O); exists ds.
    have Hassoc : (preOps ++ [op]) ++ restOps = preOps ++ op :: restOps by rewrite -app_assoc.
    rewrite -Hassoc in Hsrc Hcons Hclosed Hnd.
    rewrite Hmeq in Hrest.
    have [dres [Hrestd Hireseq]] :=
      IH (preOps ++ [op]) ds' ires Hsrc Hcons Hclosed Hnd Hpre' Hrest.
    exists dres; split; [apply/(effect_list_cons O); by exists ds' | exact Hireseq].
Qed.

(** Special case: replay from the empty state. *)
Lemma direct_of_indirect (network : YjsOperationNetwork)
    (RV : OperationReplayValidity O YjsOV YjsWithId
            (network_causal_order opid network) (NetStateSource network))
    (ops : list Op) (ires : IYjsState A) :
  (forall x, x ∈ ops -> NetStateSource network x) ->
  hb_consistent (network_causal_order opid network) ops ->
  hbClosed (network_causal_order opid network) ops ->
  IdNoDup YjsWithId ops ->
  ieffect_list ops IYjsState_empty ires ->
  exists dres, effect_list O ops (op_init O) dres /\ ires = ofDirectState dres.
Proof using A EqDA.
  move=> Hsrc Hcons Hclosed Hnd Hires.
  apply: (direct_of_indirect_suffix network RV [] ops (op_init O) ires
            Hsrc Hcons Hclosed Hnd); first by apply/(effect_list_nil O).
  exact Hires.
Qed.

(** **Indirect Yjs network strong eventual consistency** — the realistic by-id
    replay at any two nodes that delivered the same operation set reaches the
    same document. Port of the indirect [YjsOperationNetwork_converge]. *)
Theorem IYjsOperationNetwork_converge (network : YjsOperationNetwork)
    (i j : ClientId) (ires0 ires1 : IYjsState A) :
  ieffect_list (toDeliverMessages network i) IYjsState_empty ires0 ->
  ieffect_list (toDeliverMessages network j) IYjsState_empty ires1 ->
  (forall m, m ∈ toDeliverMessages network i <-> m ∈ toDeliverMessages network j) ->
  ires0 = ires1.
Proof using A EqDA.
  move=> Hi Hj Hmem.
  pose RV := YjsOperationReplayValidity network.
  have Hsrc : forall (k : ClientId) x, x ∈ toDeliverMessages network k -> NetStateSource network x.
  { move=> k x Hx; have Hd := deliver_mem_of_toDeliver_mem network k x Hx.
    have [c Hc] := deliver_has_a_cause opid network k x Hd; by exists c. }
  have [dres0 [Hd0 He0]] := direct_of_indirect network RV (toDeliverMessages network i) ires0
    (Hsrc i) (hb_consistent_local_history opid network i)
    (toDeliverMessages_hbClosed network i) (toDeliverMessages_IdNoDup network i) Hi.
  have [dres1 [Hd1 He1]] := direct_of_indirect network RV (toDeliverMessages network j) ires1
    (Hsrc j) (hb_consistent_local_history opid network j)
    (toDeliverMessages_hbClosed network j) (toDeliverMessages_IdNoDup network j) Hj.
  have Hdeq : dres0 = dres1 :=
    YjsOperationNetwork_converge_final network i j dres0 dres1 Hd0 Hd1 Hmem.
  by rewrite He0 He1 Hdeq.
Qed.

End indirect_network.

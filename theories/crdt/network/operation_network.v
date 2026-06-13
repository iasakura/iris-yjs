(** Operation networks (Yjs-independent).

    Port of [LeanYjs/Network/OperationNetwork.lean]. A [CausalNetwork] whose
    messages are operations of an [Operation], where every broadcast message is
    valid in the state obtained by replaying the broadcasting node's history so
    far. As elsewhere the effect model is RELATIONAL, so [interpHistory] is a
    relation between the initial and resulting state rather than a function. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From stdpp Require Import options.
From yjs.crdt Require Import client_id.
From yjs.crdt.operation Require Import causal_order strong_causal_order.
From yjs.crdt.network Require Import causal_network.

Section operation_network.
Context {A M : Type} `{EqDecisionA : EqDecision A} `{EqDecisionM : EqDecision M}.
Context (messageId : A -> M) (O : @Operation A).
(** [ValidMessage]: when a message may legitimately be broadcast in a state. *)
Context (isValidMessage : op_State O -> A -> Prop).

(** Replay the delivered messages of an event history (relationally). *)
Definition interpHistory (history : list (@Event A)) (init s : op_State O) : Prop :=
  effect_list O (omap deliverP history) init s.

Record OperationNetwork := {
  on_net :> CausalNetwork messageId;
  broadcast_only_valid_messages : forall i e pre post,
    histories on_net i = pre ++ [EvBroadcast e] ++ post ->
    exists s, interpHistory pre (op_init O) s /\ isValidMessage s e;
}.

End operation_network.

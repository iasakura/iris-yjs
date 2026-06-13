(** Instantiating the relational effect framework with the Yjs operations
    (insert / delete). Port of the setup in [LeanYjs/Network/Yjs/YjsNetwork.lean]:
    the [Operation] (effect), [OperationValidity] (state invariant + per-message
    validity), and [WithId] instances. The convergence/commutativity theorems
    build on this foundation. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant.
From yjs.crdt.operation Require Import causal_order hb_closed strong_causal_order.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray insert_loop delete commutativity.

Section yjs_network.
Context {A : Type} `{EqDA : EqDecision A}.

Global Instance IntegrateInput_eq_dec : EqDecision (IntegrateInput (A := A)).
Proof using A EqDA. solve_decision. Defined.

(** A network message: insert a resolved item, or tombstone an id. *)
Inductive YjsOperation : Type :=
  | OpInsert (input : IntegrateInput (A := A))
  | OpDelete (id deletedId : YjsId).

Global Instance YjsOperation_eq_dec : EqDecision YjsOperation.
Proof using A EqDA. solve_decision. Defined.

(** The operation's own id (for the causal-order id discipline). *)
Definition YjsOperation_id (op : YjsOperation) : YjsId :=
  match op with
  | OpInsert input => in_id input
  | OpDelete id _ => id
  end.

(** The (relational) effect of an operation on a document state. *)
Definition yjs_op_effect (op : YjsOperation) (s s' : YjsState A) : Prop :=
  match op with
  | OpInsert input => YjsState_insert s input = Some s'
  | OpDelete _ deletedId => s' = deleteById s deletedId
  end.

Definition YjsOp : @Operation YjsOperation :=
  @MkOperation YjsOperation (YjsState A) YjsState_empty yjs_op_effect.

(** A message is valid in a document when an insert resolves to a valid item
    (deletes are always valid). *)
Definition IsValidMessage (items : list (YjsItem A)) (op : YjsOperation) : Prop :=
  match op with
  | OpInsert input => exists item, toItem input items = Some item /\ IsItemValid item
  | OpDelete _ _ => True
  end.

Definition isValidStateYjs (op : YjsOperation) (s : YjsState A) : Prop :=
  IsValidMessage (st_items s) op.

(** The empty document satisfies the array invariant. *)
Lemma YjsArrInvariant_empty : YjsArrInvariant ([] : list (YjsItem A)).
Proof using A.
  split.
  - split; [done | done | move=> o r id c; rewrite /ArrSet => /elem_of_nil []
                        | move=> o r id c; rewrite /ArrSet => /elem_of_nil []].
  - split; [move=> o r c id; rewrite /ArrSet => /elem_of_nil []
          | move=> o r c id x; rewrite /ArrSet => /elem_of_nil []
          | move=> x y _; rewrite /ArrSet => /elem_of_nil []].
  - constructor.
  - constructor.
Qed.

(** The Yjs operation validity: effects preserve the state invariant. *)
Definition YjsOV : OperationValidity YjsOp.
Proof using A EqDA.
  refine (@Build_OperationValidity YjsOperation YjsOp isValidStateYjs YjsStateInvariant
            YjsArrInvariant_empty _).
  move=> op s s' Hinv Hvalid Heff; destruct op as [input | id did]; simpl in *.
  - destruct Hvalid as [item [Htoitem Hvalid]].
    exact: (YjsStateInvariant_insert s s' input item Hinv Htoitem Hvalid Heff).
  - rewrite Heff; exact: (YjsStateInvariant_deleteById s did Hinv).
Defined.

(** Operations carry their id. *)
Definition YjsWithId : @WithId YjsOperation YjsId := {| wid := YjsOperation_id |}.

(** The mathematical heart of network convergence: operations with distinct
    client ids commute on valid states (the [hb_concurrent] -> distinct-client
    discipline is supplied by the network). *)
Lemma yjs_concurrent_commute (a b : YjsOperation) (s s' : YjsState A) :
  clientId (YjsOperation_id a) <> clientId (YjsOperation_id b) ->
  YjsStateInvariant s -> isValidStateYjs a s -> isValidStateYjs b s ->
  eff_comp YjsOp (effect YjsOp a) (effect YjsOp b) s s' ->
  eff_comp YjsOp (effect YjsOp b) (effect YjsOp a) s s'.
Proof using A EqDA.
  move=> Hcid Hsinv Hva Hvb.
  destruct a as [ia | aid adid]; destruct b as [ib | bid bdid];
    rewrite /eff_comp /effect /=.
  - (* insert / insert *)
    move: Hva Hvb => [aItem [Htoa Hava]] [bItem [Htob Hbvb]] [m [Ha Hb]].
    have Hdo : (YjsState_insert s ia ≫= fun s2 => YjsState_insert s2 ib) = Some s'
      by rewrite Ha /=; exact Hb.
    have Hdo' := insert_commutative ia ib aItem bItem s s' Hsinv Htoa Htob Hcid Hava Hbvb Hdo.
    move: Hdo' => /bind_Some [m' [Hb' Ha']]; by exists m'.
  - (* insert / delete *)
    move=> [m [Ha Hb]].
    have Hdo : (YjsState_insert s ia ≫= fun newArr => Some (deleteById newArr bdid)) = Some s'
      by rewrite Ha /=; rewrite Hb.
    rewrite (insert_deleteById_commutative ia s bdid) in Hdo.
    exists (deleteById s bdid); split; [done | exact Hdo].
  - (* delete / insert *)
    move=> [m [Ha Hb]].
    have Hdo : (YjsState_insert s ib ≫= fun newArr => Some (deleteById newArr adid)) = Some s'.
    { rewrite (insert_deleteById_commutative ib s adid); rewrite -Ha; exact Hb. }
    move: Hdo => /bind_Some [m' [Hins Hdel]]; exists m'; split; [exact Hins | by injection Hdel].
  - (* delete / delete *)
    move=> [m [-> ->]]; exists (deleteById s bdid); split; [done | by rewrite deleteById_commutative].
Qed.

(** Concurrent commutativity holds whenever concurrent operations have distinct
    client ids (the network's per-client-total-order discipline). *)
Lemma yjs_concurrent_commutative (hb : @CausalOrder YjsOperation) (ops : list YjsOperation) :
  (forall a b, a ∈ ops -> b ∈ ops -> hb_concurrent hb a b ->
     clientId (YjsOperation_id a) <> clientId (YjsOperation_id b)) ->
  concurrent_commutative YjsOp YjsOV hb ops.
Proof using A EqDA.
  move=> Hdisc a b s s' Ha Hb Hconc Hsinv Hva Hvb.
  exact: (yjs_concurrent_commute a b s s' (Hdisc a b Ha Hb Hconc) Hsinv Hva Hvb).
Qed.

(** Yjs strong convergence: two histories of the same valid operation set (each
    causally consistent / closed, with unique ids and distinct concurrent client
    ids) reach the same document. Instantiates the generic
    [hb_consistent_effect_convergent] with the Yjs commutativity. *)
Theorem yjs_strong_convergence
    (hb : @CausalOrder YjsOperation) (StateSource : YjsOperation -> Prop)
    (RV : OperationReplayValidity YjsOp YjsOV YjsWithId hb StateSource)
    (ops0 ops1 : list YjsOperation) (s : YjsState A) :
  (forall x, x ∈ ops0 -> StateSource x) -> (forall x, x ∈ ops1 -> StateSource x) ->
  hb_consistent hb ops0 -> hb_consistent hb ops1 -> hbClosed hb ops0 -> hbClosed hb ops1 ->
  (forall a b, a ∈ ops0 -> b ∈ ops0 -> hb_concurrent hb a b ->
     clientId (YjsOperation_id a) <> clientId (YjsOperation_id b)) ->
  IdNoDup YjsWithId ops0 -> IdNoDup YjsWithId ops1 ->
  (forall x, x ∈ ops0 <-> x ∈ ops1) ->
  effect_list YjsOp ops0 (op_init YjsOp) s -> effect_list YjsOp ops1 (op_init YjsOp) s.
Proof using A EqDA.
  move=> Hsrc0 Hsrc1 Hc0 Hc1 Hcl0 Hcl1 Hdisc Hnd0 Hnd1 Hmem Heff.
  apply: (hb_consistent_effect_convergent YjsOp YjsOV YjsWithId hb StateSource RV
    ops0 ops1 s Hsrc0 Hsrc1 Hc0 Hc1 Hcl0 Hcl1 _ Hnd0 Hnd1 Hmem Heff).
  exact: (yjs_concurrent_commutative hb ops0 Hdisc).
Qed.

End yjs_network.

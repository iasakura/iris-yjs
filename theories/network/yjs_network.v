(** Instantiating the relational effect framework with the Yjs operations
    (insert / delete). Port of the setup in [LeanYjs/Network/Yjs/YjsNetwork.lean]:
    the [Operation] (effect), [OperationValidity] (state invariant + per-message
    validity), and [WithId] instances. The convergence/commutativity theorems
    build on this foundation. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set.
From yjs.order Require Import item_order item_set_invariant.
From yjs.network Require Import causal_order strong_causal_order.
From yjs.algorithm Require Import basic insert_basic invariant_basic
  invariant_yjsarray insert_loop delete.

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
Qed.

(** Operations carry their id. *)
Definition YjsWithId : @WithId YjsOperation YjsId := {| wid := YjsOperation_id |}.

End yjs_network.

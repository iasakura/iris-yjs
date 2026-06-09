(** Foundations for the Yjs operation-replay validity (Part of
    [LeanYjs/Network/Yjs/YjsNetwork.lean]): the relational-effect monotonicity
    lemmas that justify "what is present / has a given id stays present through
    replay", and the structural decomposition of an insert effect into an
    [insertIdxIfInBounds]. These feed the [toItem_prefix_invariant] /
    [isValidState_insert_from_source] chain that builds the
    [OperationReplayValidity]. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set.
From yjs.algorithm Require Import basic insert_basic invariant_yjsarray
  insert_loop delete commutativity.
From yjs.network Require Import causal_order hb_closed strong_causal_order
  causal_network operation_network yjs_network yjs_operation_network.

Section yjs_replay_validity.
Context {A : Type} `{EqDA : EqDecision A}.

Local Notation Op := (@YjsOperation A).
Local Notation O := (@YjsOp A EqDA).

(** An [integrate] always returns the input array with one item (of the input's
    id) spliced in at some index. *)
Lemma integrate_insertIdx_form (input : IntegrateInput) (arr res : list (YjsItem A)) :
  integrate input arr = Some res ->
  exists didx item, item_id item = in_id input /\ res = insertIdxIfInBounds didx item arr.
Proof using A EqDA.
  rewrite /integrate => H.
  move: H => /bind_Some [lidx [_ H]].
  move: H => /bind_Some [ridx [_ H]].
  move: H => /bind_Some [didx [_ H]].
  move: H => /bind_Some [item [Hitem Hlast]].
  move: Hlast => [= <-].
  move: Hitem; rewrite /mkItemByIndex => /bind_Some [l [_ H2]].
  move: H2 => /bind_Some [r [_ Hr]].
  move: Hr => [= <-].
  by exists didx, (Item l r (in_id input) (in_content input)); split.
Qed.

(** An insert effect splices an item (of the input's id) at some index and
    leaves the tombstone set untouched. *)
Lemma YjsState_insert_insertIdx_form (s s' : YjsState A) (input : IntegrateInput) :
  YjsState_insert s input = Some s' ->
  exists didx item, item_id item = in_id input /\
    st_items s' = insertIdxIfInBounds didx item (st_items s) /\
    st_deleted s' = st_deleted s.
Proof using A EqDA.
  rewrite /YjsState_insert => /bind_Some [newArr [Hsafe Heq]].
  move: Heq => [= Hs'].
  move: Hsafe; rewrite /integrateSafe.
  case: (isClockSafe (in_id input) (st_items s)); last by [].
  move=> Hint.
  have [didx [item [Hid Hres]]] := integrate_insertIdx_form input (st_items s) newArr Hint.
  exists didx, item; subst s'; by rewrite /=.
Qed.

(** Membership is preserved by a single effect: inserts only add, deletes only
    tombstone. *)
Lemma effect_preserves_mem (op : Op) (s s' : YjsState A) (item : YjsItem A) :
  op_effect O op s s' -> item ∈ st_items s -> item ∈ st_items s'.
Proof using A EqDA.
  destruct op as [input | id did]; simpl.
  - move=> Hins Hmem.
    have [didx [it [_ [Hitems _]]]] := YjsState_insert_insertIdx_form s s' input Hins.
    rewrite Hitems /insertIdxIfInBounds.
    case: (decide (didx <= length (st_items s))%nat) => Hd; last exact: Hmem.
    move: Hmem; rewrite -{1}(take_drop didx (st_items s)).
    rewrite !elem_of_app elem_of_cons; tauto.
  - by move=> -> Hmem.
Qed.

(** Membership is preserved by replaying a list of effects. *)
Lemma effect_list_preserves_mem (ops : list Op) (s0 s : YjsState A) (item : YjsItem A) :
  effect_list O ops s0 s -> item ∈ st_items s0 -> item ∈ st_items s.
Proof using A EqDA.
  elim: ops s0 s => [|op ops IH] s0 s.
  - by move=> /(effect_list_nil O) ->.
  - move=> /(effect_list_cons O) [m [Hop Hrest]] Hmem.
    apply: (IH m s Hrest); exact: effect_preserves_mem op s0 m item Hop Hmem.
Qed.

(** Existence of an item with a given id is preserved by a single effect. *)
Lemma effect_preserves_id_exists (op : Op) (s s' : YjsState A) (targetId : YjsId) :
  op_effect O op s s' ->
  (exists item, item ∈ st_items s /\ item_id item = targetId) ->
  (exists item, item ∈ st_items s' /\ item_id item = targetId).
Proof using A EqDA.
  move=> Heff [item [Hmem Hid]]; exists item.
  split; [exact: effect_preserves_mem op s s' item Heff Hmem | exact Hid].
Qed.

(** Existence of an item with a given id is preserved by replay. *)
Lemma effect_list_preserves_id_exists (ops : list Op) (s0 s : YjsState A) (targetId : YjsId) :
  effect_list O ops s0 s ->
  (exists item, item ∈ st_items s0 /\ item_id item = targetId) ->
  (exists item, item ∈ st_items s /\ item_id item = targetId).
Proof using A EqDA.
  move=> Heff [item [Hmem Hid]]; exists item.
  split; [exact: effect_list_preserves_mem ops s0 s item Heff Hmem | exact Hid].
Qed.

(** Deletion preserves id-uniqueness (it does not touch the list). *)
Lemma uniqueId_deleteById (s : YjsState A) (did : YjsId) :
  uniqueId (st_items s) -> uniqueId (st_items (deleteById s did)).
Proof using A. by []. Qed.

End yjs_replay_validity.

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
  toitem_lemmas insert_invariant insert_loop delete commutativity.
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

(** Clock safety forces the new id to differ from every existing id. *)
Lemma isClockSafe_id_neq (id : YjsId) (arr : list (YjsItem A)) (x : YjsItem A) :
  isClockSafe id arr = true -> x ∈ arr -> item_id x <> id.
Proof using A EqDA.
  rewrite /isClockSafe => Hcs Hx Heq.
  have Hf : Forall (fun item => Is_true (implb (bool_decide (clientId (item_id item) = clientId id))
      (bool_decide (clock (item_id item) < clock id)))) arr
    by apply/forallb_True; rewrite Hcs.
  move: Hf => /Forall_forall Hf.
  have Hgx := Hf x Hx.
  have HP1 : bool_decide (clientId (item_id x) = clientId id) = true
    by apply bool_decide_eq_true; rewrite Heq.
  rewrite HP1 /= in Hgx.
  move: Hgx => /Is_true_eq_true /bool_decide_eq_true Hclk.
  rewrite Heq in Hclk; lia.
Qed.

(** A successful insert is clock-safe in the source state. *)
Lemma YjsState_insert_isClockSafe (s s' : YjsState A) (input : IntegrateInput) :
  YjsState_insert s input = Some s' -> isClockSafe (in_id input) (st_items s) = true.
Proof using A EqDA.
  rewrite /YjsState_insert => /bind_Some [newArr [Hsafe _]].
  by have [Hcs _] := integrateSafe_ok input (st_items s) newArr Hsafe.
Qed.

(** Inserting a clock-safe item preserves id-uniqueness: the new id (the input's
    id) is distinct from every present id, so the splice keeps ids pairwise
    distinct. *)
Lemma insert_preserves_uniqueId (s s' : YjsState A) (input : IntegrateInput) :
  uniqueId (st_items s) -> YjsState_insert s input = Some s' -> uniqueId (st_items s').
Proof using A EqDA.
  move=> Huniq Hins.
  have Hcs := YjsState_insert_isClockSafe s s' input Hins.
  have [didx [item [Hid [Hitems _]]]] := YjsState_insert_insertIdx_form s s' input Hins.
  rewrite Hitems /uniqueId /insertIdxIfInBounds.
  case: (decide (didx <= length (st_items s))%nat) => Hd; last exact: Huniq.
  apply: StronglySorted_insert => //.
  - move=> j y _ Hj; rewrite Hid.
    exact: (isClockSafe_id_neq (in_id input) (st_items s) y Hcs
              (list_elem_of_lookup_2 _ _ _ Hj)).
  - move=> j y _ Hj; rewrite Hid => Heq.
    exact: (isClockSafe_id_neq (in_id input) (st_items s) y Hcs
              (list_elem_of_lookup_2 _ _ _ Hj) (eq_sym Heq)).
Qed.

(** A single effect preserves id-uniqueness. *)
Lemma effect_uniqueId (op : Op) (s s' : YjsState A) :
  uniqueId (st_items s) -> op_effect O op s s' -> uniqueId (st_items s').
Proof using A EqDA.
  destruct op as [input | id did]; simpl.
  - move=> Hu Hins; exact: insert_preserves_uniqueId s s' input Hu Hins.
  - move=> Hu ->; exact: uniqueId_deleteById s did Hu.
Qed.

(** Replaying effects preserves id-uniqueness. *)
Lemma effect_list_uniqueId (ops : list Op) (s0 s : YjsState A) :
  uniqueId (st_items s0) -> effect_list O ops s0 s -> uniqueId (st_items s).
Proof using A EqDA.
  elim: ops s0 s => [|op ops IH] s0 s Hu.
  - by move=> /(effect_list_nil O) <-.
  - move=> /(effect_list_cons O) [m [Hop Hrest]].
    apply: (IH m s _ Hrest); exact: effect_uniqueId op s0 m Hu Hop.
Qed.

(** Any document reachable by replaying from the empty state has unique ids
    (each insert is clock-safe, so no two ids coincide). The Lean version takes
    [IdNoDup] as a hypothesis; here it is unnecessary. *)
Lemma effect_list_uniqueId_init (ops : list Op) (s : YjsState A) :
  effect_list O ops (op_init O) s -> uniqueId (st_items s).
Proof using A EqDA.
  apply: (effect_list_uniqueId ops (op_init O) s); rewrite /uniqueId /=; constructor.
Qed.

(** A single effect only adds items via an insert: every item in the result is
    either already in the source or is the item just inserted (whose id is the
    input's id). *)
Lemma effect_step_mem_src (op : Op) (s s' : YjsState A) (item : YjsItem A) :
  op_effect O op s s' -> item ∈ st_items s' ->
  item ∈ st_items s \/ (exists input, op = OpInsert input /\ in_id input = item_id item).
Proof using A EqDA.
  destruct op as [input | id did]; simpl.
  - move=> Hins Hmem.
    have [didx [it [Hid [Hitems _]]]] := YjsState_insert_insertIdx_form s s' input Hins.
    rewrite Hitems in Hmem.
    case: (decide (didx <= length (st_items s))%nat) => Hd.
    + move: Hmem; rewrite (mem_insertIdxIfInBounds (st_items s) it item didx Hd) => -[Heq | Hin].
      * right; exists input; split; [done | by rewrite Heq Hid].
      * by left.
    + left; move: Hmem; by rewrite /insertIdxIfInBounds (decide_False _ _ Hd).
  - by move=> -> Hmem; left.
Qed.

(** Tracing an item in a replayed state back to its origin: it was either in the
    initial state, or it was contributed by a delivered insert in the list. *)
Lemma effect_list_mem_src (ops : list Op) (s0 s : YjsState A) (item : YjsItem A) :
  effect_list O ops s0 s -> item ∈ st_items s ->
  item ∈ st_items s0 \/ (exists input, OpInsert input ∈ ops /\ in_id input = item_id item).
Proof using A EqDA.
  elim: ops s0 s => [|op ops IH] s0 s.
  - by move=> /(effect_list_nil O) <- Hmem; left.
  - move=> /(effect_list_cons O) [m [Hop Hrest]] Hmem.
    case: (IH m s Hrest Hmem) => [Hin | [input [Hmem' Hid]]].
    + case: (effect_step_mem_src op s0 m item Hop Hin) => [Hin0 | [input [Hopeq Hid]]].
      * by left.
      * right; exists input; split; [rewrite Hopeq elem_of_cons; by left | exact Hid].
    + right; exists input; split; [rewrite elem_of_cons; by right | exact Hid].
Qed.

(** Replaying from the empty state: every item found by id was delivered by an
    insert with that id. (Relational analogue of [effect_list_find?_exists_insert_id].) *)
Lemma effect_list_find_insert (ops : list Op) (s : YjsState A) (id : YjsId) (item : YjsItem A) :
  effect_list O ops (op_init O) s ->
  find_by_id id (st_items s) = Some item ->
  exists input, OpInsert input ∈ ops /\ in_id input = id.
Proof using A EqDA.
  move=> Heff Hfind.
  have Hmem : item ∈ st_items s := @find_by_id_mem _ EqDA id (st_items s) item Hfind.
  have Hidit : item_id item = id := @find_by_id_id _ EqDA id (st_items s) item Hfind.
  case: (effect_list_mem_src ops (op_init O) s item Heff Hmem) => [Hin0 | [input [Hop Hin]]].
  - by move: Hin0; rewrite /= elem_of_nil.
  - exists input; split; [exact Hop | by rewrite Hin Hidit].
Qed.

End yjs_replay_validity.

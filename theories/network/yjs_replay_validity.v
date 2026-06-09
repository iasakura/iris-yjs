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
From yjs Require Import client_id item item_set util.
From yjs.algorithm Require Import basic insert_basic invariant_yjsarray
  toitem_lemmas findptridx_insert insert_invariant insert_loop delete commutativity.
From yjs.network Require Import causal_order hb_closed strong_causal_order
  causal_network operation_network yjs_network yjs_operation_network.

Section yjs_replay_validity.
Context {A : Type} `{EqDA : EqDecision A}.

Local Notation Op := (@YjsOperation A).
Local Notation O := (@YjsOp A EqDA).
Local Notation opid := (@YjsOperation_id A).

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

(** A successful insert splices in exactly [toItem]'s result: the item produced
    by an effect step is the [toItem] resolution of the input against the source
    state. (Extraction part of [integrateValid_exists_insertIdxIfBounds]; needs
    no validity — only that [integrate] resolved the origin/right-origin.) *)
Lemma YjsState_insert_toItem (s s' : YjsState A) (input : IntegrateInput) :
  YjsState_insert s input = Some s' ->
  exists it didx,
    toItem input (st_items s) = Some it /\
    item_id it = in_id input /\
    st_items s' = insertIdxIfInBounds didx it (st_items s) /\
    st_deleted s' = st_deleted s.
Proof using A EqDA.
  rewrite /YjsState_insert => /bind_Some [newArr [Hsafe Heq]].
  move: Heq => [= Hs']; subst s'.
  have [_ Hint] := integrateSafe_ok input (st_items s) newArr Hsafe.
  move: Hint; rewrite /integrate => /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  move: Hr2 => /bind_Some [destIdx [HfindIdx Hr3]].
  move: Hr3 => /bind_Some [item [Hmk Hlast]].
  move: Hlast => [= <-].
  have [lptr [Hgl HLl]] := findLeftIdx_getElemExcept (st_items s) input leftIdx HfindLeft.
  have [rptr [Hgr HRr]] := findRightIdx_getElemExcept (st_items s) input rightIdx HfindRight.
  have Hitem : item = Item lptr rptr (in_id input) (in_content input).
  { move: Hmk; rewrite /mkItemByIndex Hgl Hgr /= => [= H]; by rewrite H. }
  have Htoitem : toItem input (st_items s) = Some item.
  { apply/toItem_ok_iff; exists lptr, rptr, (in_id input), (in_content input).
    rewrite Hitem; split_and!; [done | exact HLl | exact HRr | done | done]. }
  exists item, destIdx; split_and!; [exact Htoitem | by rewrite Hitem | done | done].
Qed.

(** A successful by-id resolution lands at a valid list index. *)
Lemma find_idx_bounds (id : YjsId) (arr : list (YjsItem A)) (idx : Z) :
  (Z.of_nat <$> (fst <$> list_find (fun item => item_id item = id) arr)) = Some idx ->
  (0 <= idx)%Z /\ (idx < Z.of_nat (length arr))%Z.
Proof using A EqDA.
  move=> /fmap_Some [n [Hn Hidxeq]].
  move: Hn => /fmap_Some [[i x] [Hfind Hneq]].
  move: Hfind => /list_find_Some [Hlook _].
  have Hi := lookup_lt_Some _ _ _ Hlook.
  simpl in Hneq; subst n idx; split; lia.
Qed.

Lemma findLeftIdx_ge (oid : option YjsId) (arr : list (YjsItem A)) (leftIdx : Z) :
  findLeftIdx oid arr = Some leftIdx -> (-1 <= leftIdx)%Z.
Proof using A EqDA.
  rewrite /findLeftIdx; destruct oid as [id|].
  - by move=> /(find_idx_bounds id arr leftIdx) [? ?]; lia.
  - move=> [= <-]; lia.
Qed.

Lemma findLeftIdx_lt_size (oid : option YjsId) (arr : list (YjsItem A)) (leftIdx : Z) :
  findLeftIdx oid arr = Some leftIdx -> (leftIdx < Z.of_nat (length arr))%Z.
Proof using A EqDA.
  rewrite /findLeftIdx; destruct oid as [id|].
  - by move=> /(find_idx_bounds id arr leftIdx) [_ ?].
  - move=> [= <-]; lia.
Qed.

Lemma findRightIdx_le_size (rid : option YjsId) (arr : list (YjsItem A)) (rightIdx : Z) :
  findRightIdx rid arr = Some rightIdx -> (rightIdx <= Z.of_nat (length arr))%Z.
Proof using A EqDA.
  rewrite /findRightIdx; destruct rid as [id|].
  - by move=> /(find_idx_bounds id arr rightIdx) [_ ?]; lia.
  - move=> [= <-]; lia.
Qed.

(** The integrated index lands in bounds (so the splice is non-trivial): this
    uses only the index bounds of [leftIdx] / [rightIdx], never item validity.
    (Port of [findIntegratedIndex_ok_le_size_from_eq].) *)
Lemma findIntegratedIndex_le_size (leftIdx rightIdx : Z) (input : IntegrateInput)
    (arr : list (YjsItem A)) (d : nat) :
  (-1 <= leftIdx)%Z -> (leftIdx < Z.of_nat (length arr))%Z ->
  (rightIdx <= Z.of_nat (length arr))%Z ->
  findIntegratedIndex leftIdx rightIdx input arr = Some d ->
  (d <= length arr)%nat.
Proof using A EqDA.
  move=> Hge Hlt Hrle.
  rewrite /findIntegratedIndex => /bind_Some [z [Hloop [= <-]]].
  destruct (decide (leftIdx < rightIdx)%Z) as [Hlr | Hlr].
  - have [_ Hzr] := fii_loop_bounds (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
      (clientId (in_id input)) arr false (leftIdx + 1) z Hge ltac:(lia) ltac:(lia) ltac:(lia) Hloop.
    lia.
  - have Hcount : (Z.to_nat (rightIdx - leftIdx) - 1 = 0)%nat by lia.
    rewrite Hcount /= in Hloop.
    move: Hloop => [= <-]; lia.
Qed.

(** A successful insert actually places an item of the input's id in the result
    (the splice is in-bounds). *)
Lemma YjsState_insert_mem (s s' : YjsState A) (input : IntegrateInput) :
  YjsState_insert s input = Some s' ->
  exists it, item_id it = in_id input /\ it ∈ st_items s'.
Proof using A EqDA.
  rewrite /YjsState_insert => /bind_Some [newArr [Hsafe Heq]].
  move: Heq => [= Hs']; subst s'.
  have [_ Hint] := integrateSafe_ok input (st_items s) newArr Hsafe.
  move: Hint; rewrite /integrate => /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  move: Hr2 => /bind_Some [destIdx [HfindIdx Hr3]].
  move: Hr3 => /bind_Some [item [Hmk Hlast]].
  move: Hlast => [= <-].
  have [lptr [Hgl _]] := findLeftIdx_getElemExcept (st_items s) input leftIdx HfindLeft.
  have [rptr [Hgr _]] := findRightIdx_getElemExcept (st_items s) input rightIdx HfindRight.
  have Hitem : item = Item lptr rptr (in_id input) (in_content input)
    by move: Hmk; rewrite /mkItemByIndex Hgl Hgr /= => [= H]; rewrite H.
  have Hbound : (destIdx <= length (st_items s))%nat
    by apply: (findIntegratedIndex_le_size leftIdx rightIdx input (st_items s) destIdx
      (findLeftIdx_ge _ _ _ HfindLeft) (findLeftIdx_lt_size _ _ _ HfindLeft)
      (findRightIdx_le_size _ _ _ HfindRight) HfindIdx).
  exists item; split; [by rewrite Hitem | ].
  apply: (proj2 (mem_insertIdxIfInBounds (st_items s) item item destIdx Hbound)); by left.
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

(** Strengthening of [effect_step_mem_src]: a freshly-added item is exactly the
    [toItem] resolution of the inserting op against the pre-state. *)
Lemma effect_step_mem_toItem (op : Op) (s s' : YjsState A) (item : YjsItem A) :
  op_effect O op s s' -> item ∈ st_items s' ->
  item ∈ st_items s \/ (exists input, op = OpInsert input /\ toItem input (st_items s) = Some item).
Proof using A EqDA.
  destruct op as [input | id did]; simpl.
  - move=> Hins Hmem.
    have [it [didx [Htoit [_ [Hitems _]]]]] := YjsState_insert_toItem s s' input Hins.
    rewrite Hitems in Hmem.
    case: (decide (didx <= length (st_items s))%nat) => Hd.
    + move: Hmem; rewrite (mem_insertIdxIfInBounds (st_items s) it item didx Hd) => -[Heq | Hin].
      * right; exists input; split; [done | by rewrite Heq].
      * by left.
    + left; move: Hmem; by rewrite /insertIdxIfInBounds (decide_False _ _ Hd).
  - by move=> -> Hmem; left.
Qed.

(** Trace an item in a replayed state to the [toItem] of its delivering insert
    (no bound / validity hypotheses needed — the splice characterisation
    suffices). *)
Lemma effect_list_mem_toItem (ops : list Op) (s0 s : YjsState A) (item : YjsItem A) :
  effect_list O ops s0 s -> item ∈ st_items s ->
  item ∈ st_items s0 \/
  (exists input l1 l2 sMid, ops = l1 ++ OpInsert input :: l2 /\
     effect_list O l1 s0 sMid /\ toItem input (st_items sMid) = Some item).
Proof using A EqDA.
  elim: ops s0 s => [|op ops IH] s0 s.
  - by move=> /(effect_list_nil O) <- Hmem; left.
  - move=> /(effect_list_cons O) [m [Hop Hrest]] Hmem.
    case: (IH m s Hrest Hmem) => [Hin | [input [l1 [l2 [sMid [Hsplit [Heff Htoit]]]]]]].
    + case: (effect_step_mem_toItem op s0 m item Hop Hin) => [Hin0 | [input [Hopeq Htoit]]].
      * by left.
      * right; exists input, [], ops, s0.
        rewrite Hopeq; split; [done | split; [by apply/(effect_list_nil O) | exact Htoit]].
    + right; exists input, (op :: l1), l2, sMid.
      split; [by rewrite Hsplit | split; [apply/(effect_list_cons O); by exists m | exact Htoit]].
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

(** Transport of message validity along a state change that preserves the
    origin/right-origin lookups. If [toItem] succeeds in [state0] and the
    by-id finds it relied on are preserved in [s], then [toItem] resolves to the
    same item in [s] and validity carries over unchanged. Port of
    [toItem_isValid_transport_min_bridge] (the [uniqueId s] hypothesis is
    unnecessary here). *)
Lemma toItem_isValid_transport (input : IntegrateInput) (state0 s : list (YjsItem A))
    (item0 : YjsItem A) :
  toItem input state0 = Some item0 ->
  IsItemValid item0 ->
  (forall oid oit, find_by_id oid state0 = Some oit -> find_by_id oid s = Some oit) ->
  exists item, toItem input s = Some item /\ IsItemValid item.
Proof using A EqDA.
  move=> Ht0 Hvalid Hpres; exists item0; split; last exact Hvalid.
  move: Ht0; rewrite /toItem.
  destruct (in_originId input) as [oid|]; destruct (in_rightOriginId input) as [rid|];
    rewrite /=.
  - move=> /bind_Some [op [Hop Hrest]].
    move: Hop => /fmap_Some [oit [Hfo Hopeq]].
    move: Hrest => /bind_Some [rp [Hrp Hlast]].
    move: Hrp => /fmap_Some [rit [Hfr Hrpeq]]; subst op rp.
    by rewrite (Hpres oid oit Hfo) /= (Hpres rid rit Hfr) /=.
  - move=> /bind_Some [op [Hop Hlast]].
    move: Hop => /fmap_Some [oit [Hfo Hopeq]]; subst op.
    by rewrite (Hpres oid oit Hfo) /=.
  - move=> /bind_Some [rp [Hrp Hlast]].
    move: Hrp => /fmap_Some [rit [Hfr Hrpeq]]; subst rp.
    by rewrite (Hpres rid rit Hfr) /=.
  - by [].
Qed.

(** In an id-unique list, a present item is exactly what a by-id lookup returns:
    there is no earlier item sharing its id. *)
Lemma find_by_id_of_mem_unique (s : list (YjsItem A)) (oid : YjsId) (oit : YjsItem A) :
  uniqueId s -> oit ∈ s -> item_id oit = oid -> find_by_id oid s = Some oit.
Proof using A EqDA.
  move=> Huniq Hmem Hid.
  rewrite /find_by_id.
  have [[i y] Hfind] : is_Some (list_find (fun item => item_id item = oid) s)
    by apply: (list_find_elem_of _ _ oit Hmem); exact Hid.
  rewrite Hfind /=.
  move: Hfind => /list_find_Some [Hlook [Hpy _]].
  have Hymem : y ∈ s := list_elem_of_lookup_2 _ _ _ Hlook.
  have Hyeq : y = oit
    by apply: (uniqueId_id_eq_implies_eq s Huniq y oit Hymem Hmem); rewrite Hpy Hid.
  by rewrite Hyeq.
Qed.

(** The clean reduction of insert-validity replay: given the message was valid
    at broadcast time ([toItem state0] resolves to a valid item) and every item
    its by-id resolution touched is still present in the replayed state [s]
    (which is id-unique), the message is valid in [s]. The remaining (deep)
    obligation is exactly the presence hypothesis — that [insert]'s origin /
    right-origin items, being causal predecessors, survive into [s] — which is
    what [toItem_prefix_invariant] establishes from the network structure. *)
Lemma isValidMessage_replay (input : IntegrateInput) (state0 s : list (YjsItem A)) :
  uniqueId s ->
  (exists item0, toItem input state0 = Some item0 /\ IsItemValid item0) ->
  (forall oid oit, find_by_id oid state0 = Some oit -> oit ∈ s) ->
  exists item, toItem input s = Some item /\ IsItemValid item.
Proof using A EqDA.
  move=> Huniq [item0 [Ht0 Hvalid]] Hpresent.
  apply: (toItem_isValid_transport input state0 s item0 Ht0 Hvalid).
  move=> oid oit Hfind0.
  apply: (find_by_id_of_mem_unique s oid oit Huniq).
  - exact: (Hpresent oid oit Hfind0).
  - exact: (@find_by_id_id _ EqDA oid state0 oit Hfind0).
Qed.

(** An operation delivered in the broadcaster's prefix strictly happens-before
    the operation broadcast there: their deliver / broadcast events are locally
    ordered. (Port of [pre_deliver_lt_insert] / [dep_insert_lt_target].) *)
Lemma pre_deliver_lt_insert (network : YjsOperationNetwork) (i : ClientId)
    (pre post : list Event) (x input : IntegrateInput) :
  histories network i = pre ++ [EvBroadcast (OpInsert input)] ++ post ->
  EvDeliver (OpInsert x) ∈ pre ->
  co_lt (network_causal_order opid network) (OpInsert x) (OpInsert input).
Proof using A EqDA.
  move=> Hhist Hmem.
  have [l1 [l2 Hpre]] := list_elem_of_split _ _ Hmem.
  have Hlo : locallyOrdered network i (EvDeliver (OpInsert x)) (EvBroadcast (OpInsert input))
    by exists l1, l2, post; rewrite Hhist Hpre -!app_assoc.
  have Hhb : HappensBefore opid network (OpInsert x) (OpInsert input)
    := hb_db opid network i (OpInsert x) (OpInsert input) Hlo.
  split.
  - by right.
  - move=> Heq; rewrite Heq in Hhb.
    exact: (HappensBefore_asymm opid network (OpInsert input) (OpInsert input) Hhb Hhb).
Qed.

(** A happens-before predecessor of the last operation of an [hbClosed] list
    sits in the prefix before it. (Port of [hbClosed_predecessor_in_prefix].) *)
Lemma hbClosed_predecessor_in_prefix (hb : @CausalOrder Op)
    (l l' l'' : list Op) (dep target : Op) :
  hbClosed hb l ->
  l = l' ++ [target] ++ l'' ->
  co_lt hb dep target ->
  dep ∈ l'.
Proof using A. move=> Hclosed Hsplit Hlt; exact: (Hclosed target dep l' l'' Hsplit Hlt). Qed.

(** A by-id lookup is functional. (Port of [prefix_find_exact_by_id].) *)
Lemma prefix_find_exact_by_id (s : list (YjsItem A)) (oid : YjsId) (item item' : YjsItem A) :
  find_by_id oid s = Some item -> find_by_id oid s = Some item' -> item' = item.
Proof using A. move=> Hf Hf'; rewrite Hf in Hf'; by injection Hf'. Qed.

(** A delivered insert in a history reflects a member of its delivered ops. *)
Lemma deliver_insert_mem_omap (h : list Event) (z : IntegrateInput (A := A)) :
  OpInsert z ∈ omap deliverP h -> EvDeliver (OpInsert z) ∈ h.
Proof using A.
  rewrite list_elem_of_omap => -[ev [Hev Hdel]].
  destruct ev as [a | a]; simpl in Hdel; [done | injection Hdel as ->; exact Hev].
Qed.

(** The origin / right-origin ids that [toItem] resolves against a broadcaster's
    prefix state were themselves delivered (as inserts) earlier in that prefix.
    (Port of [dep_ids_exist_in_source_prefix].) *)
Lemma dep_ids_exist_in_source_prefix (op : IntegrateInput) (preHist : list Event)
    (s : YjsState A) (item : YjsItem A) :
  interpHistory O preHist (op_init O) s ->
  toItem op (st_items s) = Some item ->
  (match in_originId op with None => True
    | Some oid => exists o, EvDeliver (OpInsert o) ∈ preHist /\ in_id o = oid end) /\
  (match in_rightOriginId op with None => True
    | Some rid => exists r, EvDeliver (OpInsert r) ∈ preHist /\ in_id r = rid end).
Proof using A EqDA.
  move=> Hinterp Htoitem.
  have [o' [r' [id' [c' [_ [HoL [HoR _]]]]]]] :=
    proj1 (toItem_ok_iff op (st_items s) item) Htoitem.
  split.
  - move: HoL; rewrite /isLeftIdPtr; destruct (in_originId op) as [oid|]; last done.
    move=> [oit [_ Hfind]].
    have [inO [Hmem Hid]] := effect_list_find_insert (omap deliverP preHist) s oid oit Hinterp Hfind.
    exists inO; split; [exact: (deliver_insert_mem_omap preHist inO Hmem) | exact Hid].
  - move: HoR; rewrite /isRightIdPtr; destruct (in_rightOriginId op) as [rid|]; last done.
    move=> [rit [_ Hfind]].
    have [inR [Hmem Hid]] := effect_list_find_insert (omap deliverP preHist) s rid rit Hinterp Hfind.
    exists inR; split; [exact: (deliver_insert_mem_omap preHist inR Hmem) | exact Hid].
Qed.

(** ** Item determinism (the heart of [toItem_prefix_invariant])

    Across any two replays of broadcast operations, the item carrying a given id
    is the same. Proven by strong induction on the item's size: items embed
    their origin / right-origin as subterms, so resolving them recurses on
    strictly smaller items. The inserting op is identified up to equality by the
    network's [msg_id_unique] (both operations are broadcast). *)
Lemma item_determinism (network : YjsOperationNetwork) (it1 it2 : YjsItem A)
    (ops1 ops2 : list Op) (s1 s2 : YjsState A) (oid : YjsId) :
  (forall x, x ∈ ops1 -> exists k, EvBroadcast x ∈ histories network k) ->
  (forall x, x ∈ ops2 -> exists k, EvBroadcast x ∈ histories network k) ->
  effect_list O ops1 (op_init O) s1 ->
  effect_list O ops2 (op_init O) s2 ->
  find_by_id oid (st_items s1) = Some it1 ->
  find_by_id oid (st_items s2) = Some it2 ->
  it1 = it2.
Proof using A EqDA.
  remember (YjsItem_size it1) as n eqn:Hn.
  move: it1 it2 ops1 ops2 s1 s2 oid Hn.
  elim/nat_strong_ind: n => n IH it1 it2 ops1 ops2 s1 s2 oid
    Hsize Hsrc1 Hsrc2 Heff1 Heff2 Hf1 Hf2.
    have Hmem1 := @find_by_id_mem _ EqDA oid (st_items s1) it1 Hf1.
    have Hmem2 := @find_by_id_mem _ EqDA oid (st_items s2) it2 Hf2.
    case: (effect_list_mem_toItem ops1 (op_init O) s1 it1 Heff1 Hmem1)
      => [Hnil1 | [inO1 [l1a [l1b [sMid1 [Hsplit1 [Hpre1 Htoit1]]]]]]];
      first by move: Hnil1; rewrite /= elem_of_nil.
    case: (effect_list_mem_toItem ops2 (op_init O) s2 it2 Heff2 Hmem2)
      => [Hnil2 | [inO2 [l2a [l2b [sMid2 [Hsplit2 [Hpre2 Htoit2]]]]]]];
      first by move: Hnil2; rewrite /= elem_of_nil.
    have HidA := @find_by_id_id _ EqDA oid (st_items s1) it1 Hf1.
    have HidB := @find_by_id_id _ EqDA oid (st_items s2) it2 Hf2.
    have HinA : in_id inO1 = oid by rewrite -(@toItem_id _ EqDA inO1 (st_items sMid1) it1 Htoit1).
    have HinB : in_id inO2 = oid by rewrite -(@toItem_id _ EqDA inO2 (st_items sMid2) it2 Htoit2).
    have [k1 Hbc1] : exists k, EvBroadcast (OpInsert inO1) ∈ histories network k
      by apply: Hsrc1; rewrite Hsplit1 elem_of_app elem_of_cons; right; left.
    have [k2 Hbc2] : exists k, EvBroadcast (OpInsert inO2) ∈ histories network k
      by apply: Hsrc2; rewrite Hsplit2 elem_of_app elem_of_cons; right; left.
    have [_ HopEq] := msg_id_unique opid network (OpInsert inO1) (OpInsert inO2) k1 k2 Hbc1 Hbc2
      ltac:(by rewrite /= HinA HinB).
    move: HopEq => [= HinOeq]; subst inO2.
    have HsrcL1 : forall x, x ∈ l1a -> exists k, EvBroadcast x ∈ histories network k
      by move=> x Hx; apply: Hsrc1; rewrite Hsplit1 elem_of_app; left.
    have HsrcL2 : forall x, x ∈ l2a -> exists k, EvBroadcast x ∈ histories network k
      by move=> x Hx; apply: Hsrc2; rewrite Hsplit2 elem_of_app; left.
    have [o1 [r1 [id1 [c1 [Hdef1 [HoL1 [HoR1 [Hidd1 Hcc1]]]]]]]] :=
      proj1 (toItem_ok_iff inO1 (st_items sMid1) it1) Htoit1.
    have [o2 [r2 [id2 [c2 [Hdef2 [HoL2 [HoR2 [Hidd2 Hcc2]]]]]]]] :=
      proj1 (toItem_ok_iff inO1 (st_items sMid2) it2) Htoit2.
    have Ho : o1 = o2.
    { move: HoL1 HoL2; rewrite /isLeftIdPtr; destruct (in_originId inO1) as [oid'|].
      - move=> [ot1 [Ho1eq Hfot1]] [ot2 [Ho2eq Hfot2]].
        have HszOt : (YjsItem_size ot1 < n)%nat by rewrite Hsize Hdef1 Ho1eq /=; lia.
        have Hoteq := IH (YjsItem_size ot1) HszOt ot1 ot2 l1a l2a sMid1 sMid2 oid'
          eq_refl HsrcL1 HsrcL2 Hpre1 Hpre2 Hfot1 Hfot2.
        by rewrite Ho1eq Ho2eq Hoteq.
      - by move=> -> ->. }
    have Hr : r1 = r2.
    { move: HoR1 HoR2; rewrite /isRightIdPtr; destruct (in_rightOriginId inO1) as [rid'|].
      - move=> [rt1 [Hr1eq Hfrt1]] [rt2 [Hr2eq Hfrt2]].
        have HszRt : (YjsItem_size rt1 < n)%nat by rewrite Hsize Hdef1 Hr1eq /=; lia.
        have Hrteq := IH (YjsItem_size rt1) HszRt rt1 rt2 l1a l2a sMid1 sMid2 rid'
          eq_refl HsrcL1 HsrcL2 Hpre1 Hpre2 Hfrt1 Hfrt2.
        by rewrite Hr1eq Hr2eq Hrteq.
      - by move=> -> ->. }
    by rewrite Hdef1 Hdef2 Ho Hr Hidd1 Hidd2 Hcc1 Hcc2.
Qed.

End yjs_replay_validity.

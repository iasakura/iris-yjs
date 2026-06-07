(** Correctness of the integration scan [fii_loop] / [findIntegratedIndex].
    Port of the loop-invariant reasoning in [LeanYjs/Algorithm/Insert/Spec.lean].
    Lean uses a monadic [for]/[ForInStep] loop with [for_in_list_loop_invariant];
    here [fii_loop] is structural recursion over a fuel, so the invariant is
    carried explicitly and maintained by induction on the fuel. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item.
From yjs.algorithm Require Import basic insert_basic.

Section loop.
Context {A : Type} `{EqDA : EqDecision A}.

(** The scan keeps the destination index within [leftIdx+1 .. current], where
    [current = leftIdx + offset] advances by one each step up to [rightIdx].
    Hence the returned index lies in [leftIdx+1 .. rightIdx]. *)
Lemma fii_loop_bounds (count offset : nat) (leftIdx rightIdx : Z) (cid : ClientId)
    (arr : list (YjsItem A)) (scanning : bool) (destIdx d : Z) :
  (-1 <= leftIdx)%Z ->
  (leftIdx + 1 <= destIdx)%Z ->
  (destIdx <= leftIdx + Z.of_nat offset)%Z ->
  (leftIdx + Z.of_nat offset + Z.of_nat count = rightIdx)%Z ->
  fii_loop count offset leftIdx rightIdx cid arr scanning destIdx = Some d ->
  (leftIdx + 1 <= d)%Z /\ (d <= rightIdx)%Z.
Proof using A EqDA.
  move: offset scanning destIdx.
  induction count as [|count' IH] => offset scanning destIdx H0 Ha Hb Hc Hloop.
  - move: Hloop => /= [= <-]; lia.
  - move: Hloop => /=.
    move=> /bind_Some [other [_ Hloop]].
    move: Hloop => /bind_Some [oLeftIdx [_ Hloop]].
    move: Hloop => /bind_Some [oRightIdx [_ Hloop]].
    have Hcur0 : (0 <= leftIdx + Z.of_nat offset)%Z by lia.
    move: Hloop.
    destruct (decide (oLeftIdx < leftIdx)%Z) as [_|_]; [move=> [= <-]; lia|].
    destruct (decide (oLeftIdx = leftIdx)%Z) as [_|_].
    + destruct (decide (clientId (item_id other) < cid)%nat) as [_|_].
      * move=> Hrec; apply: (IH (S offset) false _ H0 _ _ _ Hrec); lia.
      * destruct (decide (oRightIdx = rightIdx)%Z) as [_|_]; [move=> [= <-]; lia|].
        move=> Hrec; apply: (IH (S offset) true _ H0 _ _ _ Hrec); lia.
    + move=> Hrec; apply: (IH (S offset) scanning _ H0 _ _ _ Hrec); destruct scanning; lia.
Qed.

(** [findIntegratedIndex] returns a destination in [0 .. rightIdx]. *)
Lemma findIntegratedIndex_bounds (leftIdx rightIdx : Z) (input : IntegrateInput)
    (arr : list (YjsItem A)) (d : nat) :
  (-1 <= leftIdx)%Z -> (leftIdx < rightIdx)%Z ->
  findIntegratedIndex leftIdx rightIdx input arr = Some d ->
  (Z.of_nat d <= rightIdx)%Z.
Proof using A EqDA.
  rewrite /findIntegratedIndex => H0 Hlr.
  move=> /bind_Some [z [Hloop [= <-]]].
  have [Hlo Hhi] := fii_loop_bounds (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
    (clientId (in_id input)) arr false (leftIdx + 1) z H0 ltac:(lia) ltac:(lia) ltac:(lia) Hloop.
  lia.
Qed.

End loop.

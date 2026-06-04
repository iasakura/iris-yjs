(** Happens-before-closed operation lists (Yjs-independent).

    Port of [LeanYjs/Network/HbClosed.lean]. A list is hb-closed when every
    strict predecessor of an element already appears before it. We give the
    direct definition [hbClosed] and an inductive [hbClosedI] characterisation,
    prove them equivalent, and derive the swap / removal lemmas used by the
    strong convergence proof. All purely about lists and the partial order. *)
From stdpp Require Import base list.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.network Require Import causal_order.

Section hb_closed.
Context {A : Type}.
Implicit Types (hb : @CausalOrder A) (a b x : A) (ops l : list A).

Definition hbClosed hb ops : Prop :=
  forall a b l1 l2, ops = l1 ++ a :: l2 -> co_lt hb b a -> b ∈ l1.

Inductive hbClosedI hb : list A -> Prop :=
  | hbClosedI_nil : hbClosedI hb []
  | hbClosedI_snoc a ops :
      hbClosedI hb ops ->
      (forall b, co_lt hb b a -> b ∈ ops) ->
      hbClosedI hb (ops ++ [a]).

(** [l ++ [a] = k ++ [b]] determines both parts. *)
Lemma snoc_inj (l k : list A) a b : l ++ [a] = k ++ [b] -> l = k /\ a = b.
Proof.
  move=> Heq; have [-> Hab] := app_inj_2 l k [a] [b] eq_refl Heq.
  split; [done | by injection Hab].
Qed.

Lemma hbClosed_hbClosedI hb ops : hbClosed hb ops -> hbClosedI hb ops.
Proof.
  elim/rev_ind: ops => [| x ops IH] Hclosed.
  - exact: hbClosedI_nil.
  - apply: hbClosedI_snoc.
    + apply: IH => a b l1 l2 Heq Hlt.
      apply: (Hclosed a b l1 (l2 ++ [x])); last done.
      by rewrite Heq -app_assoc.
    + move=> b Hlt; exact: (Hclosed x b ops [] eq_refl Hlt).
Qed.

Lemma hbClosedI_hbClosed hb ops : hbClosedI hb ops -> hbClosed hb ops.
Proof.
  induction 1 as [| a ops Hops IH Hall].
  - move=> a b l1 l2 Heq _; by destruct l1; simplify_eq.
  - move=> a' b l1 l2 Heq Hlt.
    destruct l2 as [| y l2 _] using rev_ind.
    + (* l2 = [] : a' is the last element [a] *)
      have Heq' : ops ++ [a] = l1 ++ [a'] by rewrite Heq.
      have [E1 E2] := snoc_inj _ _ _ _ Heq'; subst.
      exact: (Hall b Hlt).
    + (* l2 = l2 ++ [y] : recurse into [ops] *)
      have Heq' : ops ++ [a] = (l1 ++ a' :: l2) ++ [y].
      { by rewrite Heq -!app_assoc. }
      have [Hops_eq _] := snoc_inj _ _ _ _ Heq'.
      exact: (IH a' b l1 l2 Hops_eq Hlt).
Qed.

Lemma hbClosed_iff_hbClosedI hb ops : hbClosed hb ops <-> hbClosedI hb ops.
Proof. split; [exact: hbClosed_hbClosedI | exact: hbClosedI_hbClosed]. Qed.

Lemma hbClosedI_snoc_inv hb l :
  hbClosedI hb l ->
  l = [] \/ exists ops a, l = ops ++ [a] /\ hbClosedI hb ops /\ (forall b, co_lt hb b a -> b ∈ ops).
Proof.
  destruct 1 as [| a ops Hops Hall].
  - by left.
  - right; by exists ops, a.
Qed.

Lemma hbClosed_append_singleton_of_all_lt hb ops a :
  hbClosed hb ops -> (forall x, co_lt hb x a -> x ∈ ops) -> hbClosed hb (ops ++ [a]).
Proof.
  move=> Hclosed Hall; apply: hbClosedI_hbClosed.
  apply: hbClosedI_snoc; [exact: hbClosed_hbClosedI | exact: Hall].
Qed.

(** Clean "peel the last element" characterisation. *)
Lemma hbClosedI_snoc_iff hb ops a :
  hbClosedI hb (ops ++ [a]) <->
  hbClosedI hb ops /\ (forall b, co_lt hb b a -> b ∈ ops).
Proof.
  split; last by move=> [??]; apply: hbClosedI_snoc.
  move=> /hbClosedI_snoc_inv [Hnil | [ops' [a' [Heq [Hops Hall]]]]].
  - by move: Hnil => /(f_equal length); rewrite length_app /=; lia.
  - have [-> ->] := snoc_inj _ _ _ _ Heq; by split.
Qed.

(** Swapping two adjacent concurrent elements preserves hb-closedness. *)
Lemma hbClosedI_swap hb ops0 ops1 a b :
  hbClosedI hb (ops0 ++ a :: b :: ops1) ->
  hb_concurrent hb b a ->
  hbClosedI hb (ops0 ++ b :: a :: ops1).
Proof.
  move=> Hcl Hconc; move: ops0 Hcl.
  elim/rev_ind: ops1 => [| x ops1 IH] ops0 Hcl.
  - (* ops1 = [] : peel [b] then [a], rebuild swapped *)
    rewrite (_ : ops0 ++ a :: b :: [] = (ops0 ++ [a]) ++ [b]) in Hcl;
      last by rewrite -app_assoc.
    move: Hcl => /hbClosedI_snoc_iff [/hbClosedI_snoc_iff [Hops0 Hall_a] Hall_b].
    rewrite (_ : ops0 ++ b :: a :: [] = (ops0 ++ [b]) ++ [a]); last by rewrite -app_assoc.
    apply/hbClosedI_snoc_iff; split.
    + apply/hbClosedI_snoc_iff; split; first exact: Hops0.
      move=> d Hd; move: (Hall_b d Hd).
      rewrite elem_of_app elem_of_cons elem_of_nil => -[// | [Hda | []]].
      subst d; move: Hd Hconc; rewrite /co_lt /hb_concurrent; tauto.
    + move=> d Hd; rewrite elem_of_app; left; exact: (Hall_a d Hd).
  - (* ops1 = ops1 ++ [x] : peel x, swap by IH, re-append *)
    rewrite (_ : ops0 ++ a :: b :: (ops1 ++ [x]) = (ops0 ++ a :: b :: ops1) ++ [x]) in Hcl;
      last by rewrite -!app_assoc.
    move: Hcl => /hbClosedI_snoc_iff [Hcl Hall_x].
    rewrite (_ : ops0 ++ b :: a :: (ops1 ++ [x]) = (ops0 ++ b :: a :: ops1) ++ [x]);
      last by rewrite -!app_assoc.
    apply/hbClosedI_snoc_iff; split; first exact: (IH ops0 Hcl).
    move=> d Hd; move: (Hall_x d Hd).
    rewrite !elem_of_app !elem_of_cons; tauto.
Qed.

Lemma hbClosed_swap hb ops0 ops1 a b :
  hbClosed hb (ops0 ++ a :: b :: ops1) ->
  hb_concurrent hb b a ->
  hbClosed hb (ops0 ++ b :: a :: ops1).
Proof.
  move=> /hbClosed_hbClosedI Hcl Hconc.
  apply: hbClosedI_hbClosed; exact: (hbClosedI_swap _ _ _ _ _ Hcl Hconc).
Qed.

(** Bubble [b] rightward across a block of operations all concurrent with it. *)
Lemma hbClosedI_bubble hb a b ops0 ops1 :
  hbClosedI hb (ops0 ++ b :: ops1 ++ [a]) ->
  (forall x, x ∈ ops1 -> hb_concurrent hb x b) ->
  hbClosedI hb (ops0 ++ ops1 ++ b :: [a]).
Proof.
  move: ops0; elim: ops1 => [| x xs IH] ops0 Hcl Hconc.
  - exact: Hcl.
  - have Hxb : hb_concurrent hb x b by apply: Hconc; rewrite elem_of_cons; left.
    have Hcl' : hbClosedI hb (ops0 ++ b :: x :: (xs ++ [a])) by move: Hcl; rewrite /=.
    have Hswap : hbClosedI hb ((ops0 ++ [x]) ++ b :: xs ++ [a]).
    { move: (hbClosedI_swap hb ops0 (xs ++ [a]) b x Hcl' Hxb).
      by rewrite -!app_assoc. }
    have Hconc' : forall y, y ∈ xs -> hb_concurrent hb y b
      by move=> y Hy; apply: Hconc; rewrite elem_of_cons; right.
    move: (IH (ops0 ++ [x]) Hswap Hconc'); by rewrite -!app_assoc.
Qed.

(** Remove an element [b] together with a block [ops1] of operations all
    concurrent with it (and a trailing [a]) while preserving hb-closedness. *)
Lemma hbClosed_remove_concurrent hb ops0 ops1 a b :
  hbClosed hb (ops0 ++ b :: ops1 ++ [a]) ->
  (forall x, x ∈ ops1 -> hb_concurrent hb x b) ->
  hbClosed hb (ops0 ++ ops1).
Proof.
  move=> /hbClosed_hbClosedI Hcl Hconc.
  move: (hbClosedI_bubble hb a b ops0 ops1 Hcl Hconc).
  rewrite (_ : ops0 ++ ops1 ++ b :: [a] = ((ops0 ++ ops1) ++ [b]) ++ [a]);
    last by rewrite -!app_assoc.
  move=> /hbClosedI_snoc_iff [/hbClosedI_snoc_iff [Hres _] _].
  exact: hbClosedI_hbClosed.
Qed.

End hb_closed.

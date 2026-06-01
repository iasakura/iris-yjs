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

End hb_closed.

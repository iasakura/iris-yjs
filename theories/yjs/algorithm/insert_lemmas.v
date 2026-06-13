(** Lemmas about [findPtrIdx]: where it locates an item, its range, and its
    injectivity. Port of [LeanYjs/Algorithm/Insert/Lemmas.lean] (Array/Int
    indexing restated with stdpp [!!] / [Z]). *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic insert_basic.

Section lemmas.
Context {A : Type} `{EqDA : EqDecision A}.

(** If [findPtrIdx] of an item succeeds, it returns the (nonneg, in-bounds)
    index where that item sits. *)
Lemma findPtrIdx_item_exists (arr : list (YjsItem A)) (x : YjsItem A) (i : Z) :
  findPtrIdx (itemPtr x) arr = Some i ->
  exists j, i = Z.of_nat j /\ j < length arr /\ arr !! j = Some x.
Proof using A EqDA.
  rewrite /findPtrIdx /find_item_idx.
  destruct (list_find (fun i0 => i0 = x) arr) as [[j x']|] eqn:Hf; simpl=> Heq; last done.
  injection Heq as <-.
  apply list_find_Some in Hf; destruct Hf as (Hjx & Hxx & _).
  exists j; split_and!; [done | exact: lookup_lt_Some Hjx | by rewrite Hjx Hxx].
Qed.

Lemma findPtrIdx_ge_minus_1 (arr : list (YjsItem A)) (item : YjsPtr A) (idx : Z) :
  findPtrIdx item arr = Some idx -> (-1 <= idx)%Z.
Proof using A EqDA.
  rewrite /findPtrIdx; destruct item as [it| |].
  - rewrite /find_item_idx; destruct (list_find _ arr) as [[j ?]|] eqn:Hf;
      simpl=> Heq; [injection Heq as <-; lia | done].
  - move=> [<-]; lia.
  - move=> [<-]; lia.
Qed.

Lemma findPtrIdx_le_size (arr : list (YjsItem A)) (item : YjsPtr A) (idx : Z) :
  findPtrIdx item arr = Some idx -> (idx <= Z.of_nat (length arr))%Z.
Proof using A EqDA.
  rewrite /findPtrIdx; destruct item as [it| |].
  - rewrite /find_item_idx; destruct (list_find _ arr) as [[j ?]|] eqn:Hf;
      simpl=> Heq; last done.
    injection Heq as <-.
    apply list_find_Some in Hf; destruct Hf as (Hjx & _ & _).
    have := lookup_lt_Some _ _ _ Hjx; lia.
  - move=> [<-]; lia.
  - move=> [<-]; lia.
Qed.

(** [findPtrIdx] is injective on success. *)
Lemma findPtrIdx_eq_ok_inj (arr : list (YjsItem A)) (x y : YjsPtr A) (i : Z) :
  findPtrIdx x arr = Some i -> findPtrIdx y arr = Some i -> x = y.
Proof using A EqDA.
  destruct x as [xx| |]; destruct y as [yy| |]; move=> Hx Hy.
  - have [jx [Hix [_ Hjx]]] := findPtrIdx_item_exists arr xx i Hx.
    have [jy [Hiy [_ Hjy]]] := findPtrIdx_item_exists arr yy i Hy.
    have Hjj : jx = jy by lia. subst jx.
    rewrite Hjy in Hjx; by injection Hjx as ->.
  - have [jx [Hix [_ _]]] := findPtrIdx_item_exists arr xx i Hx.
    move: Hy => /= [= ?]; lia.
  - have [jx [Hix [Hlt _]]] := findPtrIdx_item_exists arr xx i Hx.
    move: Hy => /= [= ?]; lia.
  - have [jy [Hiy [_ _]]] := findPtrIdx_item_exists arr yy i Hy.
    move: Hx => /= [= ?]; lia.
  - done.
  - move: Hx Hy => /= [= ?] [= ?]; lia.
  - have [jy [Hiy [Hlt _]]] := findPtrIdx_item_exists arr yy i Hy.
    move: Hx => /= [= ?]; lia.
  - move: Hx Hy => /= [= ?] [= ?]; lia.
  - done.
Qed.

End lemmas.

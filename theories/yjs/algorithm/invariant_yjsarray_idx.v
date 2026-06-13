(** Connecting list indices to the order: a sorted list's lookups respect the
    relation, specialised to [YjsArrInvariant]/[YjsLt']. Foundation for the
    [findPtrIdx_*] family. Port of the index lemmas in
    [LeanYjs/Algorithm/Invariant/YjsArray.lean] (Array/Fin -> stdpp [!!]). *)
From stdpp Require Import base list sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.order Require Import item_order.
From yjs.algorithm Require Import invariant_yjsarray.

(** In a [StronglySorted] list, an earlier lookup is [R]-related to a later one. *)
Lemma ss_lookup_lt {X} {R : X -> X -> Prop} :
  forall (l : list X) (i j : nat) (x y : X),
  StronglySorted R l -> l !! i = Some x -> l !! j = Some y -> i < j -> R x y.
Proof.
  induction l as [|a l IH]; intros i j x y Hss Hi Hj Hij; first done.
  apply StronglySorted_inv in Hss; destruct Hss as [Hss Hfa].
  destruct i as [|i]; destruct j as [|j]; simpl in Hi, Hj; try lia.
  - injection Hi as <-.
    move: Hfa => /Forall_forall Hfa; apply: Hfa; exact: (list_elem_of_lookup_2 _ _ _ Hj).
  - apply: (IH i j x y Hss Hi Hj); lia.
Qed.

Section idx.
Context {A : Type}.

Lemma getElem_lt_YjsLt' (arr : list (YjsItem A)) (i j : nat) (x y : YjsItem A) :
  YjsArrInvariant arr -> arr !! i = Some x -> arr !! j = Some y -> i < j ->
  YjsLt' (itemPtr x) (itemPtr y).
Proof. move=> Hinv Hi Hj Hij; exact: (ss_lookup_lt arr i j x y (yai_sorted _ Hinv) Hi Hj Hij). Qed.

Lemma getElem_leq_YjsLeq' (arr : list (YjsItem A)) (i j : nat) (x y : YjsItem A) :
  YjsArrInvariant arr -> arr !! i = Some x -> arr !! j = Some y -> i <= j ->
  YjsLeq' (itemPtr x) (itemPtr y).
Proof.
  move=> Hinv Hi Hj Hij; destruct (decide (i = j)) as [->|Hne].
  - rewrite Hj in Hi; injection Hi as ->; exact: YjsLeq'_leqSame.
  - apply: YjsLeq'_leqLt; apply: (getElem_lt_YjsLt' arr i j x y Hinv Hi Hj); lia.
Qed.

End idx.

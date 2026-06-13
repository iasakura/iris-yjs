(** [findPtrIdx] locates the element at its own index, recovers membership, and
    a sorted/unique list has distinct elements at distinct indices. Port of
    [YjsArrayInvariant_lt_neq], [findPtrIdx_getElem], [findPtrIdx_ArrSet] from
    [LeanYjs/Algorithm/Invariant/YjsArray.lean]. *)
From stdpp Require Import base list numbers sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.algorithm Require Import basic insert_basic insert_lemmas
  invariant_basic invariant_yjsarray invariant_yjsarray_idx.

Section getelem.
Context {A : Type} `{EqDA : EqDecision A}.

(** Distinct indices into a unique-id document hold distinct items. *)
Lemma YjsArrInvariant_lt_neq (arr : list (YjsItem A)) (i j : nat) (x y : YjsItem A) :
  YjsArrInvariant arr -> arr !! i = Some x -> arr !! j = Some y -> i < j -> x <> y.
Proof using A EqDA.
  move=> Hinv Hi Hj Hij Hxy.
  have Hneq : item_id x <> item_id y :=
    ss_lookup_lt arr i j x y (yai_unique _ Hinv) Hi Hj Hij.
  by apply Hneq; rewrite Hxy.
Qed.

(** [findPtrIdx] of the item at index [i] returns [i]. *)
Lemma findPtrIdx_getElem (arr : list (YjsItem A)) (i : nat) (x : YjsItem A) :
  YjsArrInvariant arr -> arr !! i = Some x ->
  findPtrIdx (itemPtr x) arr = Some (Z.of_nat i).
Proof using A EqDA.
  move=> Hinv Hi.
  rewrite /findPtrIdx /find_item_idx.
  have Hfind : list_find (fun i0 => i0 = x) arr = Some (i, x).
  { apply list_find_Some; split_and!; [exact Hi | done |].
    move=> j y Hj Hjlt; exact: (YjsArrInvariant_lt_neq arr j i y x Hinv Hj Hi Hjlt). }
  by rewrite Hfind.
Qed.

(** A successful [findPtrIdx] witnesses membership of the pointer in [arr]. *)
Lemma findPtrIdx_ArrSet (arr : list (YjsItem A)) (p : YjsPtr A) (idx : Z) :
  findPtrIdx p arr = Some idx -> ArrSet arr p.
Proof using A EqDA.
  destruct p as [x| |] => Hfind; rewrite /ArrSet //=.
  have [j [_ [_ Hj]]] := findPtrIdx_item_exists arr x idx Hfind.
  exact: (list_elem_of_lookup_2 _ _ _ Hj).
Qed.

End getelem.

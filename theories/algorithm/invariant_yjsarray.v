(** The full Yjs array invariant [YjsArrInvariant] and document determinism.

    Port of [LeanYjs/Algorithm/Invariant/YjsArray.lean]. The document list is
    closed, satisfies the order invariant, is strictly sorted by [YjsLt'], and
    has unique ids. Lean's [List.Pairwise] is stdpp's [StronglySorted].

    This file holds the invariant definition; the heavy theorems
    ([same_yjs_set_unique] determinism, and the [findPtrIdx_*] family relating
    the algorithm's index functions to the order) are ported on top of it. *)
From stdpp Require Import base list sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item item_set.
From yjs.order Require Import item_order item_set_invariant.
From yjs.algorithm Require Import basic invariant_basic.

Section yjsarray.
Context {A : Type}.

(** Ids occurring in the list are pairwise distinct. *)
Definition uniqueId (items : list (YjsItem A)) : Prop :=
  StronglySorted (fun x y => item_id x <> item_id y) items.

(** The document is closed, order-invariant, [YjsLt']-sorted, and id-unique. *)
Record YjsArrInvariant (arr : list (YjsItem A)) : Prop := {
  yai_closed : IsClosedItemSet (ArrSet arr);
  yai_item_set_inv : ItemSetInvariant (ArrSet arr);
  yai_sorted : StronglySorted (fun x y : YjsItem A => YjsLt' (itemPtr x) (itemPtr y)) arr;
  yai_unique : uniqueId arr;
}.

Definition YjsStateInvariant (s : YjsState A) : Prop := YjsArrInvariant (st_items s).

End yjsarray.

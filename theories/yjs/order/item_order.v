(** The core ordering relation on Yjs pointers.

    Port of [LeanYjs/Order/ItemOrder.lean]: the sentinel order [OriginLt], the
    origin-reachability relations, and the mutually recursive [YjsLt]/[YjsLeq]/
    [ConflictLt] indexed by a derivation height, together with their
    height-erased ([']) variants and the constructor/inversion helpers. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set.
Definition max4 (x y z w : nat) : nat := max (max x y) (max z w).

(** Order between the sentinels and items: [First] is below every item, every
    item is below [Last], and [First] is below [Last]. *)
Inductive OriginLt {A} : YjsPtr A -> YjsPtr A -> Prop :=
  | lt_first item : OriginLt First (itemPtr item)
  | lt_last item : OriginLt (itemPtr item) Last
  | lt_first_last : OriginLt First Last.

(** One step of origin reachability: from an item to its [origin] or
    [rightOrigin]. *)
Inductive OriginReachableStep {A} : YjsPtr A -> YjsPtr A -> Prop :=
  | reachable o r id c : OriginReachableStep (Item o r id c) o
  | reachable_right o r id c : OriginReachableStep (Item o r id c) r.

Inductive OriginReachable {A} : YjsPtr A -> YjsPtr A -> Prop :=
  | reachable_single x y : OriginReachableStep x y -> OriginReachable x y
  | reachable_head x y z :
      OriginReachableStep x y -> OriginReachable y z -> OriginReachable x z.

(** The order relation, with an explicit derivation height to enable
    well-founded recursion. [YjsLt h x y] means "[x] is strictly before [y]";
    [ConflictLt] resolves the conflict between two items sharing structure. *)
Inductive YjsLt {A : Type} : nat -> YjsPtr A -> YjsPtr A -> Prop :=
  | ltConflict h i1 i2 : ConflictLt h i1 i2 -> YjsLt (S h) i1 i2
  | ltOriginOrder i1 i2 : OriginLt i1 i2 -> YjsLt 0 i1 i2
  | ltOrigin h x o r id c : YjsLeq h x o -> YjsLt (S h) x (Item o r id c)
  | ltRightOrigin h o r id c x : YjsLeq h r x -> YjsLt (S h) (Item o r id c) x
with YjsLeq {A : Type} : nat -> YjsPtr A -> YjsPtr A -> Prop :=
  | leqSame h x : YjsLeq h x x
  | leqLt h x y : YjsLt h x y -> YjsLeq (S h) x y
with ConflictLt {A : Type} : nat -> YjsPtr A -> YjsPtr A -> Prop :=
  | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 :
      YjsLt h1 l2 l1 ->
      YjsLt h2 (Item l1 r1 id1 c1) r2 ->
      YjsLt h3 l1 (Item l2 r2 id2 c2) ->
      YjsLt h4 (Item l2 r2 id2 c2) r1 ->
      ConflictLt (max4 h1 h2 h3 h4 + 1) (Item l1 r1 id1 c1) (Item l2 r2 id2 c2)
  | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) :
      YjsLt h1 (Item l r1 id1 c1) r2 ->
      YjsLt h2 (Item l r2 id2 c2) r1 ->
      YjsId_lt id1 id2 ->
      ConflictLt (max h1 h2 + 1) (Item l r1 id1 c1) (Item l r2 id2 c2).

(** Height-erased variants. *)
Definition ConflictLt' {A} (i1 i2 : YjsPtr A) : Prop := exists h, ConflictLt h i1 i2.
Definition YjsLt' {A} (x y : YjsPtr A) : Prop := exists h, YjsLt h x y.
Definition YjsLeq' {A} (x y : YjsPtr A) : Prop := exists h, YjsLeq h x y.

(** Smart constructors for the erased variants. *)
Lemma ConflictLt'_ltOriginDiff {A} (l1 l2 r1 r2 : YjsPtr A) id1 id2 (c1 c2 : A) :
  YjsLt' l2 l1 ->
  YjsLt' (Item l1 r1 id1 c1) r2 ->
  YjsLt' l1 (Item l2 r2 id2 c2) ->
  YjsLt' (Item l2 r2 id2 c2) r1 ->
  ConflictLt' (Item l1 r1 id1 c1) (Item l2 r2 id2 c2).
Proof. move=> [??] [??] [??] [??]; eexists; by apply: ltOriginDiff. Qed.

Lemma ConflictLt'_ltOriginSame {A} (l r1 r2 : YjsPtr A) id1 id2 (c1 c2 : A) :
  YjsLt' (Item l r1 id1 c1) r2 ->
  YjsLt' (Item l r2 id2 c2) r1 ->
  YjsId_lt id1 id2 ->
  ConflictLt' (Item l r1 id1 c1) (Item l r2 id2 c2).
Proof. move=> [??] [??] ?; eexists; by apply: ltOriginSame. Qed.

Lemma YjsLt'_ltConflict {A} (i1 i2 : YjsPtr A) : ConflictLt' i1 i2 -> YjsLt' i1 i2.
Proof. move=> [??]; eexists; by apply: ltConflict. Qed.

Lemma YjsLt'_ltOriginOrder {A} (i1 i2 : YjsPtr A) : OriginLt i1 i2 -> YjsLt' i1 i2.
Proof. move=> ?; eexists; by apply: ltOriginOrder. Qed.

Lemma YjsLt'_ltOrigin {A} (x o r : YjsPtr A) id c :
  YjsLeq' x o -> YjsLt' x (Item o r id c).
Proof. move=> [??]; eexists; by apply: ltOrigin. Qed.

Lemma YjsLt'_ltRightOrigin {A} (o r : YjsPtr A) id c x :
  YjsLeq' r x -> YjsLt' (Item o r id c) x.
Proof. move=> [??]; eexists; by apply: ltRightOrigin. Qed.

Lemma YjsLeq'_leqSame {A} (x : YjsPtr A) : YjsLeq' x x.
Proof. exists 0; apply: leqSame. Qed.

Lemma YjsLeq'_leqLt {A} (x y : YjsPtr A) : YjsLt' x y -> YjsLeq' x y.
Proof. move=> [h ?]; exists (S h); by apply: leqLt. Qed.

Lemma yjs_leq'_imp_eq_or_yjs_lt' {A} (x y : YjsPtr A) :
  YjsLeq' x y -> x = y \/ YjsLt' x y.
Proof.
  move=> [h Hleq]; inversion Hleq; subst.
  - by left.
  - right; by eexists.
Qed.

(** Case analysis on a [YjsLt] derivation. *)
Theorem yjs_lt_cases {A} h (x y : YjsPtr A) :
  YjsLt h x y ->
    (x = First /\ (y = Last \/ exists i, y = itemPtr i)) \/
    (y = Last /\ (x = First \/ exists i, x = itemPtr i)) \/
    (exists x', x = itemPtr x' /\ YjsLeq' (rightOrigin x') y) \/
    (exists y', y = itemPtr y' /\ YjsLeq' x (origin y')) \/
    ConflictLt' x y.
Proof.
  case=> [h' i1 i2 Hc | i1 i2 Hor | h' x' o r id c Hleq | h' o r id c x' Hleq].
  - (* ltConflict *) do 4 right; by exists h'.
  - (* ltOriginOrder *) case: Hor => [item | item |].
    + left; split=> //; right; by exists item.
    + right; left; split=> //; right; by exists item.
    + left; split=> //; by left.
  - (* ltOrigin *) do 3 right; left; exists (Item o r id c); split=> //; by exists h'.
  - (* ltRightOrigin *) do 2 right; left; exists (Item o r id c); split=> //; by exists h'.
Qed.

Theorem yjs_lt'_cases {A} (x y : YjsPtr A) :
  YjsLt' x y ->
    (x = First /\ (y = Last \/ exists i, y = itemPtr i)) \/
    (y = Last /\ (x = First \/ exists i, x = itemPtr i)) \/
    (exists x', x = itemPtr x' /\ YjsLeq' (rightOrigin x') y) \/
    (exists y', y = itemPtr y' /\ YjsLeq' x (origin y')) \/
    ConflictLt' x y.
Proof. move=> [h Hlt]; exact: yjs_lt_cases. Qed.

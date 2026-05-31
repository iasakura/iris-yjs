(** The well-formedness invariant on item sets.

    Port of [LeanYjs/Order/ItemSetInvariant.lean]: [ItemSetInvariant] carves out
    the item sets that arise as the DAG of an insertion history, and the basic
    consequences that the sentinels are extremal for [YjsLt]. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set util.
From yjs.order Require Import item_order.

(** An item set is a valid insertion history when:
    - every item's origin is strictly before its right origin;
    - any pointer reachable from an item via origins lies outside the
      [origin, rightOrigin] interval; and
    - ids identify items uniquely. *)
Record ItemSetInvariant {A} (P : ItemSet A) : Prop := {
  origin_not_leq : forall (o r : YjsPtr A) (c : A) (id : YjsId),
    P (Item o r id c) -> YjsLt' o r;
  origin_nearest_reachable : forall (o r : YjsPtr A) (c : A) (id : YjsId) (x : YjsPtr A),
    P (Item o r id c) -> OriginReachable (Item o r id c) x ->
    YjsLeq' x o \/ YjsLeq' r x;
  id_unique : forall (x y : YjsItem A),
    item_id x = item_id y -> P x -> P y -> x = y;
}.

Lemma origin_p_valid {A} {P : ItemSet A} :
  IsClosedItemSet P -> forall (x : YjsItem A), P x -> P (origin x).
Proof. move=> Hc [o r id c] Hx; exact: (closedLeft _ Hc _ _ _ _ Hx). Qed.

Lemma right_origin_p_valid {A} {P : ItemSet A} :
  IsClosedItemSet P -> forall (x : YjsItem A), P x -> P (rightOrigin x).
Proof. move=> Hc [o r id c] Hx; exact: (closedRight _ Hc _ _ _ _ Hx). Qed.

(** No element of a valid set is strictly below [First]. *)
Lemma not_ptr_lt_first {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall h (o : YjsPtr A), P o -> ¬ YjsLt h o First.
Proof.
  move=> Hclosed Hinv.
  suff H : forall n h (o : YjsPtr A), YjsPtr_size o = n -> P o -> ¬ YjsLt h o First.
  { move=> h o Hpo; exact: (H _ h o eq_refl Hpo). }
  apply: (nat_strong_ind
    (fun n => forall h (o : YjsPtr A), YjsPtr_size o = n -> P o -> ¬ YjsLt h o First)).
  move=> n IH h o Hn Hpo Hlt.
  inversion Hlt as [h' i1 i2 Hc | i1 i2 Hor
                   | h1 x1 o1 r1 id1 c1 Hl1
                   | h' o' r id c x Hleq]; subst.
  - by inversion Hc.
  - by inversion Hor.
  - inversion Hleq as [hh z | hh z1 z2 Hinner]; subst.
    + (* leqSame: r = First *)
      have [h3 Hlt3] : YjsLt' o' First by exact: (origin_not_leq _ Hinv o' First c id Hpo).
      apply: (IH (YjsPtr_size o') _ h3 o' eq_refl _ Hlt3).
      * simpl; lia.
      * exact: (closedLeft _ Hclosed o' First id c Hpo).
    + (* leqLt: Hinner : YjsLt hh r First *)
      apply: (IH (YjsPtr_size r) _ hh r eq_refl _ Hinner).
      * simpl; lia.
      * exact: (closedRight _ Hclosed o' r id c Hpo).
Qed.

Lemma not_ptr_lt'_first {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall (o : YjsPtr A), P o -> ¬ YjsLt' o First.
Proof. move=> Hclosed Hinv o Hpo [h Hlt]; exact: (not_ptr_lt_first Hclosed Hinv h o Hpo Hlt). Qed.

(** Symmetrically, no element of a valid set has [Last] strictly below it. *)
Lemma not_last_lt_ptr {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall h (o : YjsPtr A), P o -> ¬ @YjsLt A h Last o.
Proof.
  move=> Hclosed Hinv.
  suff H : forall n h (o : YjsPtr A), YjsPtr_size o = n -> P o -> ¬ @YjsLt A h Last o.
  { move=> h o Hpo; exact: (H _ h o eq_refl Hpo). }
  apply: (nat_strong_ind
    (fun n => forall h (o : YjsPtr A), YjsPtr_size o = n -> P o -> ¬ @YjsLt A h Last o)).
  move=> n IH h o Hn Hpo Hlt.
  inversion Hlt as [h' i1 i2 Hc | i1 i2 Hor
                   | h' x o' r id c Hleq
                   | h1 o1 r1 id1 c1 x1 Hl1]; subst.
  - by inversion Hc.
  - by inversion Hor.
  - inversion Hleq as [hh z | hh z1 z2 Hinner]; subst.
    + (* leqSame: o' = Last *)
      have [h3 Hlt3] : YjsLt' Last r by exact: (origin_not_leq _ Hinv Last r c id Hpo).
      apply: (IH (YjsPtr_size r) _ h3 r eq_refl _ Hlt3).
      * simpl; lia.
      * exact: (closedRight _ Hclosed Last r id c Hpo).
    + (* leqLt: Hinner : YjsLt hh Last o' *)
      apply: (IH (YjsPtr_size o') _ hh o' eq_refl _ Hinner).
      * simpl; lia.
      * exact: (closedLeft _ Hclosed o' r id c Hpo).
Qed.

Lemma not_last_lt_first {A} {P : ItemSet A} :
  ItemSetInvariant P -> forall h, ¬ @YjsLt A h Last First.
Proof.
  move=> _ h Hlt.
  inversion Hlt as [h' i1 i2 Hc | i1 i2 Hor
                   | h1 x1 o1 r1 id1 c1 Hl1 | h1 o1 r1 id1 c1 x1 Hl1].
  - by inversion Hc.
  - by inversion Hor.
Qed.

Lemma not_first_lt_first {A} {P : ItemSet A} :
  ItemSetInvariant P -> forall h, ¬ @YjsLt A h First First.
Proof.
  move=> _ h Hlt.
  inversion Hlt as [h' i1 i2 Hc | i1 i2 Hor
                   | h1 x1 o1 r1 id1 c1 Hl1 | h1 o1 r1 id1 c1 x1 Hl1].
  - by inversion Hc.
  - by inversion Hor.
Qed.

Lemma not_last_lt_last {A} {P : ItemSet A} :
  ItemSetInvariant P -> forall h, ¬ @YjsLt A h Last Last.
Proof.
  move=> _ h Hlt.
  inversion Hlt as [h' i1 i2 Hc | i1 i2 Hor
                   | h1 x1 o1 r1 id1 c1 Hl1 | h1 o1 r1 id1 c1 x1 Hl1].
  - by inversion Hc.
  - by inversion Hor.
Qed.

Lemma ItemSetInvariant_eq_set {A} (P Q : ItemSet A) :
  IsClosedItemSet P -> ItemSetInvariant P ->
  (forall x, P x <-> Q x) -> ItemSetInvariant Q.
Proof.
  move=> _ HP Hiff; split.
  - move=> o r c id Hq.
    exact: (origin_not_leq _ HP o r c id (proj2 (Hiff _) Hq)).
  - move=> o r c id x Hq Hreach.
    exact: (origin_nearest_reachable _ HP o r c id x (proj2 (Hiff _) Hq) Hreach).
  - move=> x y Hid Hqx Hqy.
    exact: (id_unique _ HP x y Hid (proj2 (Hiff _) Hqx) (proj2 (Hiff _) Hqy)).
Qed.

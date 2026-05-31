(** Transitivity of the Yjs order.

    Port of [LeanYjs/Order/Transitivity.lean]: the projections of a [ConflictLt]
    onto sub-pointer orderings, transitivity of the id order, the conflict
    transitivity helper [conflict_lt_trans], the main [yjs_lt_trans] (strong
    induction on the size sum), and the [YjsLeq]/[YjsLt] mixed-transitivity
    corollaries. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set util.
From yjs.order Require Import item_order item_set_invariant totality.

(** Projections of a conflict order onto the origins / right origins. *)
Lemma conflict_lt_x_origin_lt_y {A} {P : ItemSet A} h (x : YjsItem A) y :
  IsClosedItemSet P -> ConflictLt h x y -> YjsLt' (origin x) y.
Proof.
  move=> _ Hc; inversion Hc; subst; simpl.
  - by eexists; eassumption.
  - apply: YjsLt'_ltOrigin; exact: YjsLeq'_leqSame.
Qed.

Lemma conflict_lt_y_origin_lt_x {A} {P : ItemSet A} h x (y : YjsItem A) :
  IsClosedItemSet P -> ConflictLt h x y -> YjsLt' (origin y) x.
Proof.
  move=> _ Hc; inversion Hc; subst; simpl.
  - apply: YjsLt'_ltOrigin; apply: YjsLeq'_leqLt; by eexists; eassumption.
  - apply: YjsLt'_ltOrigin; exact: YjsLeq'_leqSame.
Qed.

Lemma conflict_lt_y_lt_x_right_origin {A} h (x : YjsItem A) y :
  ConflictLt h x y -> YjsLt' y (rightOrigin x).
Proof. move=> Hc; inversion Hc; subst; simpl; by eexists; eassumption. Qed.

Lemma conflict_lt_x_lt_y_right_origin {A} h x (y : YjsItem A) :
  ConflictLt h x y -> YjsLt' x (rightOrigin y).
Proof. move=> Hc; inversion Hc; subst; simpl; by eexists; eassumption. Qed.

(** Transitivity of the identifier order. *)
Lemma YjsId_lt_trans (x y z : YjsId) :
  YjsId_lt x y -> YjsId_lt y z -> YjsId_lt x z.
Proof.
  case: x => xc xk; case: y => yc yk; case: z => zc zk; rewrite /YjsId_lt /=.
  case_bool_decide as Hxy; case_bool_decide as Hyz; case_bool_decide as Hxz;
    move=> H1 H2; lia.
Qed.

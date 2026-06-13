(** Asymmetry of the Yjs order.

    Port of [LeanYjs/Order/Asymmetry.lean]: the order is irreflexive in the
    strong sense that [x < y] and [y < x] cannot both hold. The proof finds, for
    any mutually-related pair, a strictly smaller mutually-related pair, and
    concludes by strong induction on the size sum. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set util.
From yjs.order Require Import item_order item_set_invariant totality transitivity.

(** Asymmetry of the identifier order. *)
Lemma YjsId_lt_asymm (id1 id2 : YjsId) : YjsId_lt id1 id2 -> ¬ YjsId_lt id2 id1.
Proof.
  case: id1 => c1 k1; case: id2 => c2 k2; rewrite /YjsId_lt /=.
  case_bool_decide as H1; case_bool_decide as H2; move=> P1 P2; lia.
Qed.

(** Two conflicting items related both ways yield a strictly smaller
    mutually-related pair (their origins). *)
Lemma yjs_lt_conflict_lt_decreases {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall (x y : YjsPtr A), P x -> P y -> ConflictLt' x y -> ConflictLt' y x ->
  exists (x' y' : YjsPtr A), P x' /\ P y' /\
    YjsPtr_size x' + YjsPtr_size y' < YjsPtr_size x + YjsPtr_size y /\
    YjsLt' x' y' /\ YjsLt' y' x'.
Proof.
  move=> Hclosed inv x y Hpx Hpy [hxy Hxy] [hyx Hyx].
  destruct x as [[xo xr xid xc] | | ]; [| by inversion Hxy | by inversion Hxy].
  destruct y as [[yo yr yid yc] | | ]; [| by inversion Hxy | by inversion Hxy].
  have Hpxo : P xo by exact: (closedLeft _ Hclosed xo xr xid xc Hpx).
  have Hpyo : P yo by exact: (closedLeft _ Hclosed yo yr yid yc Hpy).
  inversion Hxy as [xa1 xa2 xa3 xa4 xL1 xL2 xR1 xR2 xI1 xI2 xC1 xC2 X1 X2 X3 X4
                   | xa1 xa2 xL xR1 xR2 xI1 xI2 xC1 xC2 X1 X2 XID]; clear Hxy;
  inversion Hyx as [ya1 ya2 ya3 ya4 yL1 yL2 yR1 yR2 yI1 yI2 yC1 yC2 Y1 Y2 Y3 Y4
                   | ya1 ya2 yL yR1 yR2 yI1 yI2 yC1 yC2 Y1 Y2 YID]; clear Hyx;
  (* the same/same case is contradictory (inverse id orders); the others give a
     mutually-[<] pair of origins, distinct or coinciding *)
  simplify_eq;
    try (match goal with
         | HID1 : YjsId_lt ?i ?j, HID2 : YjsId_lt ?j ?i |- _ =>
             exfalso; exact: (YjsId_lt_asymm _ _ HID1 HID2) end).
  all: (match goal with
        | HA : YjsLt _ ?a ?b, HB : YjsLt _ ?b ?a |- _ => exists a, b
        | H : YjsLt _ ?a ?a |- _ => exists a, a
        end;
        split; [by [exact: Hpxo | exact: Hpyo]
               | split; [by [exact: Hpxo | exact: Hpyo]
                        | split; [by (simpl; lia)
                                 | split; by eexists; eassumption]]]).
Qed.

(** If [x]'s right origin is [<= y] but [y < x], the pair [(rightOrigin x, y)]
    is a strictly smaller mutually-related pair. *)
Lemma yjs_leq_right_origin_decreases {A} {P : ItemSet A}
    (inv : ItemSetInvariant P) (x : YjsItem A) (y : YjsPtr A) :
  P x -> P y -> IsClosedItemSet P ->
  YjsLeq' (rightOrigin x) y -> YjsLt' y x ->
  exists (x' y' : YjsPtr A), P x' /\ P y' /\
    YjsPtr_size x' + YjsPtr_size y' < YjsItem_size x + YjsPtr_size y /\
    YjsLt' x' y' /\ YjsLt' y' x'.
Proof.
  move=> Hpx Hpy Hclosed Hxrleq Hyx.
  destruct x as [o r id c]; simpl in Hxrleq |- *.
  have Hpr : P r by exact: (closedRight _ Hclosed o r id c Hpx).
  have Hyr : YjsLt' y r.
  { apply: (yjs_lt_trans inv Hclosed y (Item o r id c) r Hpy Hpx Hpr Hyx).
    apply: YjsLt'_ltRightOrigin; exact: (YjsLeq'_leqSame r). }
  have Hry : YjsLt' r y.
  { case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hxrleq) => [Heq | Hlt].
    - by subst y.
    - exact: Hlt. }
  exists r, y; split; [exact: Hpr |]; split; [exact: Hpy |];
    split; [simpl; lia |]; split; [exact: Hry | exact: Hyr].
Qed.

(** Symmetrically for the origin. *)
Lemma yjs_leq_origin_decreases {A} {P : ItemSet A}
    (inv : ItemSetInvariant P) (x : YjsPtr A) (y : YjsItem A) :
  P x -> P y -> IsClosedItemSet P ->
  YjsLeq' x (origin y) -> YjsLt' y x ->
  exists (x' y' : YjsPtr A), P x' /\ P y' /\
    YjsPtr_size x' + YjsPtr_size y' < YjsPtr_size x + YjsItem_size y /\
    YjsLt' x' y' /\ YjsLt' y' x'.
Proof.
  move=> Hpx Hpy Hclosed Hxoleq Hyx.
  destruct y as [o r id c]; simpl in Hxoleq |- *.
  have Hpo : P o by exact: (closedLeft _ Hclosed o r id c Hpy).
  have Hox : YjsLt' o x.
  { apply: (yjs_lt_trans inv Hclosed o (Item o r id c) x Hpo Hpy Hpx).
    - apply: YjsLt'_ltOrigin; exact: (YjsLeq'_leqSame o).
    - exact: Hyx. }
  have Hxo : YjsLt' x o.
  { case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hxoleq) => [Heq | Hlt].
    - by subst x.
    - exact: Hlt. }
  exists x, o; split; [exact: Hpx |]; split; [exact: Hpo |];
    split; [simpl; lia |]; split; [exact: Hxo | exact: Hox].
Qed.

(** The order is asymmetric on a valid item set. *)
Lemma yjs_lt_asymm {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall (x y : YjsPtr A), P x -> P y -> YjsLt' x y -> YjsLt' y x -> False.
Proof.
  move=> Hclosed inv.
  suff H : forall sz (x y : YjsPtr A), P x -> P y -> YjsLt' x y -> YjsLt' y x ->
    YjsPtr_size x + YjsPtr_size y = sz -> False.
  { move=> x y Hpx Hpy Hxy Hyx; exact: (H _ x y Hpx Hpy Hxy Hyx eq_refl). }
  apply: (nat_strong_ind (fun sz => forall (x y : YjsPtr A), P x -> P y ->
    YjsLt' x y -> YjsLt' y x -> YjsPtr_size x + YjsPtr_size y = sz -> False)).
  move=> sz ih x y Hpx Hpy Hxy Hyx Hsz; subst sz.
  case: (yjs_lt'_cases _ _ Hxy) =>
    [[Hxf _] | [[Hyl _] | [[xi [Hxeq Hxr]] | [[yi [Hyeq Hyo]] | Hconf]]]].
  - (* x = First : y < First impossible *)
    subst x; case: Hyx => [h Hyx']; exact: (not_ptr_lt_first Hclosed inv h y Hpy Hyx').
  - (* y = Last : Last < x impossible *)
    subst y; case: Hyx => [h Hyx']; exact: (not_last_lt_ptr Hclosed inv h x Hpx Hyx').
  - (* x = itemPtr xi, rightOrigin xi <= y *)
    subst x.
    have [x' [y' [Hpx' [Hpy' [Hsz' [Hx'y' Hy'x']]]]]] :=
      yjs_leq_right_origin_decreases inv xi y Hpx Hpy Hclosed Hxr Hyx.
    apply: (ih _ _ x' y' Hpx' Hpy' Hx'y' Hy'x' eq_refl); simpl in Hsz' |- *; lia.
  - (* y = itemPtr yi, x <= origin yi *)
    subst y.
    have [x' [y' [Hpx' [Hpy' [Hsz' [Hx'y' Hy'x']]]]]] :=
      yjs_leq_origin_decreases inv x yi Hpx Hpy Hclosed Hyo Hyx.
    apply: (ih _ _ x' y' Hpx' Hpy' Hx'y' Hy'x' eq_refl); simpl in Hsz' |- *; lia.
  - (* ConflictLt' x y : examine y < x *)
    case: (yjs_lt'_cases _ _ Hyx) =>
      [[Hyf _] | [[Hxl _] | [[yi [Hyeq Hyr]] | [[xi [Hxeq Hxo]] | Hconf']]]].
    + subst y; case: Hxy => [h Hxy']; exact: (not_ptr_lt_first Hclosed inv h x Hpx Hxy').
    + subst x; case: Hxy => [h Hxy']; exact: (not_last_lt_ptr Hclosed inv h y Hpy Hxy').
    + (* y = itemPtr yi, rightOrigin yi <= x *)
      subst y.
      have [x' [y' [Hpx' [Hpy' [Hsz' [Hx'y' Hy'x']]]]]] :=
        yjs_leq_right_origin_decreases inv yi x Hpy Hpx Hclosed Hyr Hxy.
      apply: (ih _ _ x' y' Hpx' Hpy' Hx'y' Hy'x' eq_refl); simpl in Hsz' |- *; lia.
    + (* x = itemPtr xi, y <= origin xi *)
      subst x.
      have [x' [y' [Hpx' [Hpy' [Hsz' [Hx'y' Hy'x']]]]]] :=
        yjs_leq_origin_decreases inv y xi Hpy Hpx Hclosed Hxo Hxy.
      apply: (ih _ _ x' y' Hpx' Hpy' Hx'y' Hy'x' eq_refl); simpl in Hsz' |- *; lia.
    + (* both conflicts *)
      have [x' [y' [Hpx' [Hpy' [Hsz' [Hx'y' Hy'x']]]]]] :=
        yjs_lt_conflict_lt_decreases Hclosed inv x y Hpx Hpy Hconf Hconf'.
      apply: (ih _ _ x' y' Hpx' Hpy' Hx'y' Hy'x' eq_refl); lia.
Qed.

Lemma yjs_lt_of_not_leq {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y : YjsPtr A) :
  IsClosedItemSet P -> P x -> P y -> YjsLt' x y -> ¬ YjsLeq' y x.
Proof.
  move=> Hclosed Hpx Hpy Hxy Hyx.
  have Hyx' : YjsLt' y x.
  { case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hyx) => [Heq | Hlt].
    - by subst y.
    - exact: Hlt. }
  exact: (yjs_lt_asymm Hclosed inv x y Hpx Hpy Hxy Hyx').
Qed.

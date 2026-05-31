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

(** Transitivity of [ConflictLt], assuming the [YjsLt] transitivity induction
    hypothesis [ih] for strictly smaller size sums. *)
Lemma conflict_lt_trans {A} {P : ItemSet A} (inv : ItemSetInvariant P) :
  IsClosedItemSet P ->
  forall (x y z : YjsPtr A), P x -> P y -> P z ->
  (forall m, m < YjsPtr_size x + YjsPtr_size y + YjsPtr_size z ->
    forall (a b c : YjsPtr A), P a -> P b -> P c ->
    forall ha, YjsLt ha a b -> forall hb, YjsLt hb b c ->
    YjsPtr_size a + YjsPtr_size b + YjsPtr_size c = m -> exists h, YjsLt h a c) ->
  forall h1 h2, ConflictLt h1 x y -> ConflictLt h2 y z -> YjsLt' x z.
Proof.
  move=> Hclosed x y z Hpx Hpy Hpz ih h1 h2 Hxy Hyz.
  (* x, z, y are all items *)
  destruct x as [[xo xr xid xc] | | ]; [| by inversion Hxy | by inversion Hxy].
  destruct z as [[zo zr zid zc] | | ]; [| by inversion Hyz | by inversion Hyz].
  destruct y as [[yo yr yid yc] | | ]; [| by inversion Hxy | by inversion Hxy].
  have Hpxo : P xo by exact: (closedLeft _ Hclosed xo xr xid xc Hpx).
  have Hpxr : P xr by exact: (closedRight _ Hclosed xo xr xid xc Hpx).
  have Hpzo : P zo by exact: (closedLeft _ Hclosed zo zr zid zc Hpz).
  have Hpzr : P zr by exact: (closedRight _ Hclosed zo zr zid zc Hpz).
  have Hpyo : P yo by exact: (closedLeft _ Hclosed yo yr yid yc Hpy).
  (* projections of the two conflicts *)
  have Hyzr : YjsLt' (Item yo yr yid yc) zr
    by exact: (conflict_lt_x_lt_y_right_origin _ _ _ Hyz).
  have Hxoy : YjsLt' xo (Item yo yr yid yc)
    by exact: (conflict_lt_x_origin_lt_y _ _ _ Hclosed Hxy).
  (* x < zr and xo < z, via the induction hypothesis through y *)
  have Hxzr : YjsLt' (Item xo xr xid xc) zr.
  { case: Hyzr => [hy' Hyzr'].
    apply: (ih _ _ (Item xo xr xid xc) (Item yo yr yid yc) zr Hpx Hpy Hpzr
              (S h1) (ltConflict _ _ _ Hxy) hy' Hyzr' eq_refl); simpl; lia. }
  have Hxoz : YjsLt' xo (Item zo zr zid zc).
  { case: Hxoy => [hx' Hxoy'].
    apply: (ih _ _ xo (Item yo yr yid yc) (Item zo zr zid zc) Hpxo Hpy Hpz
              hx' Hxoy' (S h2) (ltConflict _ _ _ Hyz) eq_refl); simpl; lia. }
  (* compare xr with z and x with zo *)
  have Hxrz : YjsLeq' xr (Item zo zr zid zc) \/ YjsLt' (Item zo zr zid zc) xr
    by exact: (yjs_lt_total inv Hclosed xr (Item zo zr zid zc) Hpxr Hpz).
  have Hxzo : YjsLeq' (Item xo xr xid xc) zo \/ YjsLt' zo (Item xo xr xid xc)
    by exact: (yjs_lt_total inv Hclosed (Item xo xr xid xc) zo Hpx Hpzo).
  case: Hxrz => [Hxrz | Hzxr];
    first by apply: YjsLt'_ltRightOrigin; exact: Hxrz.
  case: Hxzo => [Hxzo | Hzox];
    first by apply: YjsLt'_ltOrigin; exact: Hxzo.
  (* both sub-comparisons go the "wrong" way: resolve via a new conflict *)
  apply: YjsLt'_ltConflict.
  inversion Hxy as [da1 da2 da3 da4 dL1 dL2 dR1 dR2 dI1 dI2 dC1 dC2 HA HB HC HD
                   | sa1 sa2 sL sR1 sR2 sI1 sI2 sC1 sC2 HSA HSB HID]; clear Hxy;
  inversion Hyz as [eb1 eb2 eb3 eb4 eM1 eM2 eS1 eS2 eJ1 eJ2 eD1 eD2 HE HF HG HH
                   | eb1 eb2 eL eR1 eR2 eI1 eI2 eC1 eC2 HSE HSF HJD]; clear Hyz;
  simplify_eq.
  - (* diff / diff: need zo < xo via ih through yo *)
    apply: (ConflictLt'_ltOriginDiff _ _ xr zr xid zid xc zc);
      [ apply: (ih _ _ _ _ _ Hpzo Hpyo Hpxo _ HE _ HA eq_refl); simpl; lia
      | exact: Hxzr | exact: Hxoz | exact: Hzxr ].
  - (* diff / same: zo = yo, so HA gives zo < xo *)
    apply: (ConflictLt'_ltOriginDiff _ _ xr zr xid zid xc zc);
      [ by eexists; eassumption | exact: Hxzr | exact: Hxoz | exact: Hzxr ].
  - (* same / diff: yo = xo, so HE gives zo < xo *)
    apply: (ConflictLt'_ltOriginDiff _ _ xr zr xid zid xc zc);
      [ by eexists; eassumption | exact: Hxzr | exact: Hxoz | exact: Hzxr ].
  - (* same / same: shared origin, ids transitive *)
    apply: (ConflictLt'_ltOriginSame _ xr zr xid zid xc zc);
      [ exact: Hxzr | exact: Hzxr | exact: (YjsId_lt_trans _ _ _ HID HJD) ].
Qed.

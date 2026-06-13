(** Totality of the Yjs order.

    Port of [LeanYjs/Order/Totality.lean]: any two pointers of a valid item set
    are comparable. The core [yjs_lt_total] is proved by strong induction on the
    sum of the structural sizes, interleaving four sub-comparisons and resolving
    the remaining conflict either by [ConflictLt] or by id uniqueness. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set util.
From yjs.order Require Import item_order item_set_invariant.

Lemma first_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> P First.
Proof. move=> Hc; exact: (baseFirst _ Hc). Qed.

Lemma last_p_valid {A} {P : ItemSet A} : IsClosedItemSet P -> P Last.
Proof. move=> Hc; exact: (baseLast _ Hc). Qed.

(** Trichotomy for identifiers. *)
Lemma YjsId_lt_total (x y : YjsId) :
  YjsId_lt x y \/ YjsId_lt y x \/ x = y.
Proof.
  case: x => xc xk; case: y => yc yk; rewrite /YjsId_lt /=.
  case_bool_decide as H1; case_bool_decide as H2.
  - have [?|[?|Heq]] : yk < xk \/ xk < yk \/ yk = xk by lia.
    + by left.
    + by right; left.
    + by right; right; subst.
  - exfalso; exact: (H2 (eq_sym H1)).
  - exfalso; exact: (H1 (eq_sym H2)).
  - have [?|?] : xc < yc \/ yc < xc by lia.
    + by left.
    + by right; left.
Qed.

(** Any two pointers of a valid item set are comparable. *)
Lemma yjs_lt_total {A} {P : ItemSet A} (inv : ItemSetInvariant P) :
  IsClosedItemSet P ->
  forall (x y : YjsPtr A), P x -> P y -> YjsLeq' x y \/ YjsLt' y x.
Proof.
  move=> Hclosed.
  suff H : forall n (x y : YjsPtr A), P x -> P y ->
    YjsPtr_size x + YjsPtr_size y = n -> YjsLeq' x y \/ YjsLt' y x.
  { move=> x y Hx Hy; exact: (H _ x y Hx Hy eq_refl). }
  apply: (nat_strong_ind (fun n => forall (x y : YjsPtr A), P x -> P y ->
    YjsPtr_size x + YjsPtr_size y = n -> YjsLeq' x y \/ YjsLt' y x)).
  move=> n IH x y Hx Hy Hn.
  destruct x as [xi | | ]; destruct y as [yi | | ].
  - (* itemPtr xi, itemPtr yi : the main case *)
    destruct xi as [xo xr xid xc]; destruct yi as [yo yr yid yc].
    have hxo : P xo by exact: (origin_p_valid Hclosed (Item xo xr xid xc) Hx).
    have hxr : P xr by exact: (right_origin_p_valid Hclosed (Item xo xr xid xc) Hx).
    have hyo : P yo by exact: (origin_p_valid Hclosed (Item yo yr yid yc) Hy).
    have hyr : P yr by exact: (right_origin_p_valid Hclosed (Item yo yr yid yc) Hy).
    simpl in Hn.
    (* (1) compare x with y.origin *)
    have H1 : YjsLeq' (Item xo xr xid xc) yo \/ YjsLt' yo (Item xo xr xid xc).
    { apply: (IH _ _ _ _ Hx hyo eq_refl); simpl; lia. }
    case: H1 => [Hle1 | hltyox];
      [ left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltOrigin; exact: Hle1 | ].
    (* (2) compare y.rightOrigin with x *)
    have H2 : YjsLeq' yr (Item xo xr xid xc) \/ YjsLt' (Item xo xr xid xc) yr.
    { apply: (IH _ _ _ _ hyr Hx eq_refl); simpl; lia. }
    case: H2 => [Hle2 | hltxyr];
      [ right; apply: YjsLt'_ltRightOrigin; exact: Hle2 | ].
    (* (3) compare y with x.origin *)
    have H3 : YjsLeq' (Item yo yr yid yc) xo \/ YjsLt' xo (Item yo yr yid yc).
    { apply: (IH _ _ _ _ Hy hxo eq_refl); simpl; lia. }
    case: H3 => [Hle3 | hltxoy];
      [ right; apply: YjsLt'_ltOrigin; exact: Hle3 | ].
    (* (4) compare x.rightOrigin with y *)
    have H4 : YjsLeq' xr (Item yo yr yid yc) \/ YjsLt' (Item yo yr yid yc) xr.
    { apply: (IH _ _ _ _ hxr Hy eq_refl); simpl; lia. }
    case: H4 => [Hle4 | hltyxr];
      [ left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltRightOrigin; exact: Hle4 | ].
    (* (5) compare the origins *)
    have H5 : YjsLeq' xo yo \/ YjsLt' yo xo.
    { apply: (IH _ _ _ _ hxo hyo eq_refl); simpl; lia. }
    case: H5 => [Hle5 | hltyoxo];
      [ | left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltConflict;
          apply: (ConflictLt'_ltOriginDiff xo yo xr yr xid yid xc yc);
          [exact: hltyoxo | exact: hltxyr | exact: hltxoy | exact: hltyxr] ].
    case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle5) => [Heq | hltxoyo];
      [ | right; apply: YjsLt'_ltConflict;
          apply: (ConflictLt'_ltOriginDiff yo xo yr xr yid xid yc xc);
          [exact: hltxoyo | exact: hltyxr | exact: hltyox | exact: hltxyr] ].
    (* origins are equal: resolve by id comparison *)
    subst yo.
    case: (YjsId_lt_total xid yid) => [Hidlt | [Hidlt | Hideq]];
      [ left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltConflict;
          apply: (ConflictLt'_ltOriginSame xo xr yr xid yid xc yc);
          [exact: hltxyr | exact: hltyxr | exact: Hidlt]
      | right; apply: YjsLt'_ltConflict;
          apply: (ConflictLt'_ltOriginSame xo yr xr yid xid yc xc);
          [exact: hltyxr | exact: hltxyr | exact: Hidlt]
      | subst yid; left;
          rewrite (id_unique _ inv (Item xo xr xid xc) (Item xo yr xid yc) eq_refl Hx Hy);
          apply: YjsLeq'_leqSame ].
  - (* itemPtr xi, First *)
    right; apply: YjsLt'_ltOriginOrder; apply: lt_first.
  - (* itemPtr xi, Last *)
    left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltOriginOrder; apply: lt_last.
  - (* First, itemPtr yi *)
    left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltOriginOrder; apply: lt_first.
  - (* First, First *)
    left; apply: YjsLeq'_leqSame.
  - (* First, Last *)
    left; apply: YjsLeq'_leqLt; apply: YjsLt'_ltOriginOrder; apply: lt_first_last.
  - (* Last, itemPtr yi *)
    right; apply: YjsLt'_ltOriginOrder; apply: lt_last.
  - (* Last, First *)
    right; apply: YjsLt'_ltOriginOrder; apply: lt_first_last.
  - (* Last, Last *)
    left; apply: YjsLeq'_leqSame.
Qed.

Lemma YjsLeq'_or_YjsLt' {A} {P : ItemSet A} {x y : YjsPtr A} :
  ItemSetInvariant P -> IsClosedItemSet P -> P x -> P y -> YjsLeq' x y \/ YjsLt' y x.
Proof. move=> inv HP Hx Hy; exact: (yjs_lt_total inv HP x y Hx Hy). Qed.

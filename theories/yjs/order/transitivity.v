(** Transitivity of the Yjs order.

    Port of [LeanYjs/Order/Transitivity.lean]: the projections of a [ConflictLt]
    onto sub-pointer orderings, transitivity of the id order, the conflict
    transitivity helper [conflict_lt_trans], the main [yjs_lt_trans] (strong
    induction on the size sum), and the [YjsLeq]/[YjsLt] mixed-transitivity
    corollaries. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs.crdt Require Import client_id.
From yjs Require Import item item_set util.
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

(** Main transitivity, by strong induction on the size sum. *)
Lemma yjs_lt_trans {A} {P : ItemSet A} (inv : ItemSetInvariant P) :
  IsClosedItemSet P ->
  forall (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' x y -> YjsLt' y z -> YjsLt' x z.
Proof.
  move=> Hclosed.
  suff H : forall ts (x y z : YjsPtr A), P x -> P y -> P z ->
    forall h0, YjsLt h0 x y -> forall h1, YjsLt h1 y z ->
    YjsPtr_size x + YjsPtr_size y + YjsPtr_size z = ts -> YjsLt' x z.
  { move=> x y z Hpx Hpy Hpz [h0 Hxy] [h1 Hyz].
    exact: (H _ x y z Hpx Hpy Hpz h0 Hxy h1 Hyz eq_refl). }
  apply: (nat_strong_ind (fun ts => forall (x y z : YjsPtr A), P x -> P y -> P z ->
    forall h0, YjsLt h0 x y -> forall h1, YjsLt h1 y z ->
    YjsPtr_size x + YjsPtr_size y + YjsPtr_size z = ts -> YjsLt' x z)).
  move=> ts ih x y z Hpx Hpy Hpz h0 Hxy h1 Hyz Hts; subst ts.
  (* corner cases coming from [x] / [y] in [Hxy] *)
  case: (yjs_lt_cases _ _ _ Hxy) => [[Hxf Hy] | [[Hyl _] | Hxycases]].
  { (* x = First *)
    subst x; case: Hy => [Hyl | [yi Hyi]].
    - (* y = Last : contradicts Last < z *)
      subst y; exfalso; exact: (not_last_lt_ptr Hclosed inv h1 z Hpz Hyz).
    - (* y = itemPtr : compare First with z *)
      subst y; destruct z as [zi | | ].
      + apply: YjsLt'_ltOriginOrder; exact: lt_first.
      + by exfalso; exact: (not_ptr_lt_first Hclosed inv h1 _ Hpy Hyz).
      + apply: YjsLt'_ltOriginOrder; exact: lt_first_last. }
  { (* y = Last : contradicts Last < z *)
    subst y; exfalso; exact: (not_last_lt_ptr Hclosed inv h1 z Hpz Hyz). }
  (* corner cases coming from [y] / [z] in [Hyz] *)
  case: (yjs_lt_cases _ _ _ Hyz) => [[Hyf _] | [[Hzl Hz] | Hyzcases]].
  { (* y = First : contradicts x < First *)
    subst y; exfalso; exact: (not_ptr_lt_first Hclosed inv h0 x Hpx Hxy). }
  { (* z = Last *)
    subst z; case: Hz => [Hyf | [yi Hyi]].
    - (* y = First : contradicts x < First *)
      subst y; exfalso; exact: (not_ptr_lt_first Hclosed inv h0 x Hpx Hxy).
    - (* y = itemPtr : compare x with Last *)
      subst y; destruct x as [xi | | ].
      + apply: YjsLt'_ltOriginOrder; exact: lt_last.
      + apply: YjsLt'_ltOriginOrder; exact: lt_first_last.
      + by exfalso; exact: (not_last_lt_ptr Hclosed inv h0 _ Hpy Hxy). }
  (* main cases *)
  case: Hxycases => [[[xo xr xid xc] [Hxeq Hle]] | [[[yo yr yid yc] [Hyeq Hle]] | Hxyconf]].
  - (* C: x = Item .., rightOrigin x = xr <= y *)
    subst x; simpl in Hle.
    apply: YjsLt'_ltRightOrigin.
    case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle) => [Heq | Hxry].
    + (* xr = y *) subst y; apply: YjsLeq'_leqLt; by exists h1.
    + (* xr < y *) apply: YjsLeq'_leqLt; case: Hxry => [hr Hxry'].
      apply: (ih _ _ xr y z (closedRight _ Hclosed xo xr xid xc Hpx) Hpy Hpz
                hr Hxry' h1 Hyz eq_refl); simpl; lia.
  - (* D: y = Item .., x <= origin y = yo *)
    subst y; simpl in Hle.
    have Hpyo : P yo by exact: (closedLeft _ Hclosed yo yr yid yc Hpy).
    have Hpyr : P yr by exact: (closedRight _ Hclosed yo yr yid yc Hpy).
    case: Hyzcases => [[[yo' yr' yid' yc'] [Hyeq Hle']]
                      | [[[zo zr zid zc] [Hzeq Hle']] | Hyzconf]].
    + (* C': y = Item .., rightOrigin y = yr <= z *)
      injection Hyeq as Eo Er Eid Ec; subst yo' yr' yid' yc'; simpl in Hle'.
      have [hor Horlt] : YjsLt' yo yr by exact: (origin_not_leq _ inv yo yr yc yid Hpy).
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle) => [Hxo | Hxlt];
        case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle') => [Hrz | Hrlt].
      * (* x = yo, yr = z : x < z is yo < yr *)
        subst x z; by exists hor.
      * (* x = yo, yr < z : yo < yr < z *)
        subst x; case: Hrlt => [hrz Hrlt'].
        apply: (ih _ _ yo yr z Hpyo Hpyr Hpz hor Horlt hrz Hrlt' eq_refl);
          simpl; lia.
      * (* x < yo, yr = z : x < yo < yr = z *)
        subst z; case: Hxlt => [hxo Hxlt'].
        apply: (ih _ _ x yo yr Hpx Hpyo Hpyr hxo Hxlt' hor Horlt eq_refl);
          simpl; lia.
      * (* x < yo, yr < z : x < yo < z via (yo < yr < z) *)
        case: Hxlt => [hxo Hxlt']; case: Hrlt => [hrz Hrlt'].
        have [hoz Hoz] : YjsLt' yo z.
        { apply: (ih _ _ yo yr z Hpyo Hpyr Hpz hor Horlt hrz Hrlt' eq_refl);
            simpl; lia. }
        apply: (ih _ _ x yo z Hpx Hpyo Hpz hxo Hxlt' hoz Hoz eq_refl);
          simpl; lia.
    + (* D': z = Item .., y <= origin z = zo *)
      subst z; simpl in Hle'.
      have Hpzo : P zo by exact: (closedLeft _ Hclosed zo zr zid zc Hpz).
      apply: YjsLt'_ltOrigin.
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle') => [Heq | Hyzo].
      * (* y = zo *) subst zo; apply: YjsLeq'_leqLt; by exists h0.
      * (* y < zo *) apply: YjsLeq'_leqLt; case: Hyzo => [hyz' Hyzo'].
        apply: (ih _ _ x (Item yo yr yid yc) zo Hpx Hpy Hpzo h0 Hxy hyz' Hyzo' eq_refl);
          simpl; lia.
    + (* E': ConflictLt' y z *)
      case: Hyzconf => [hc Hyzconf].
      have [ho Hyoz] : YjsLt' yo z
        by exact: (conflict_lt_x_origin_lt_y _ _ _ Hclosed Hyzconf).
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle) => [Heq | Hxlt].
      * (* x = yo *) subst x; by exists ho.
      * (* x < yo *) case: Hxlt => [hxo Hxlt'].
        apply: (ih _ _ x yo z Hpx Hpyo Hpz hxo Hxlt' ho Hyoz eq_refl);
          simpl; lia.
  - (* E: ConflictLt' x y *)
    case: Hxyconf => [hc Hxyconf].
    case: Hyzcases => [[[yo' yr' yid' yc'] [Hyeq Hle']]
                      | [[[zo zr zid zc] [Hzeq Hle']] | Hyzconf]].
    + (* C': y = Item .., rightOrigin y <= z *)
      subst y; simpl in Hle'.
      have [hxr Hxr] : YjsLt' x yr' by exact: (conflict_lt_x_lt_y_right_origin _ _ _ Hxyconf).
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle') => [Heq | Hrz].
      * (* yr' = z *) subst z; by exists hxr.
      * (* yr' < z *) case: Hrz => [hrz Hrz'].
        apply: (ih _ _ x yr' z Hpx (closedRight _ Hclosed yo' yr' yid' yc' Hpy) Hpz
                  hxr Hxr hrz Hrz' eq_refl); simpl; lia.
    + (* D': z = Item .., y <= origin z *)
      subst z; simpl in Hle'.
      have Hpzo : P zo by exact: (closedLeft _ Hclosed zo zr zid zc Hpz).
      apply: YjsLt'_ltOrigin.
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle') => [Heq | Hyzo].
      * (* y = zo *) subst zo; apply: YjsLeq'_leqLt; by exists h0.
      * (* y < zo *) apply: YjsLeq'_leqLt; case: Hyzo => [hyz' Hyzo'].
        apply: (ih _ _ x y zo Hpx Hpy Hpzo h0 Hxy hyz' Hyzo' eq_refl);
          simpl; lia.
    + (* E': ConflictLt' y z : both conflicts, use conflict_lt_trans *)
      case: Hyzconf => [hc' Hyzconf].
      exact: (conflict_lt_trans inv Hclosed x y z Hpx Hpy Hpz ih hc hc' Hxyconf Hyzconf).
Qed.

(** Mixed transitivity corollaries combining [YjsLeq'] and [YjsLt']. *)
Lemma yjs_leq'_p_trans1 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLeq' x y -> YjsLt' y z -> YjsLt' x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hleq Hlt.
  case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq) => [Heq | Hxy].
  - by subst x.
  - exact: (yjs_lt_trans inv Hclosed x y z Hpx Hpy Hpz Hxy Hlt).
Qed.

Lemma yjs_leq'_p_trans2 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLt' x y -> YjsLeq' y z -> YjsLt' x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hlt Hleq.
  case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq) => [Heq | Hyz].
  - by subst z.
  - exact: (yjs_lt_trans inv Hclosed x y z Hpx Hpy Hpz Hlt Hyz).
Qed.

Lemma yjs_leq'_p_trans {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLeq' x y -> YjsLeq' y z -> YjsLeq' x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hleq1 Hleq2.
  case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq1) => [Heq | Hxy].
  - by subst x.
  - case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hleq2) => [Heq | Hyz].
    + subst z; exact: (YjsLeq'_leqLt _ _ Hxy).
    + apply: YjsLeq'_leqLt; exact: (yjs_lt_trans inv Hclosed x y z Hpx Hpy Hpz Hxy Hyz).
Qed.

Lemma yjs_leq_p_trans1 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2 :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLeq h1 x y -> YjsLt h2 y z -> exists h, YjsLt h x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hleq Hlt.
  exact: (yjs_leq'_p_trans1 inv x y z Hpx Hpy Hpz Hclosed (ex_intro _ h1 Hleq) (ex_intro _ h2 Hlt)).
Qed.

Lemma yjs_leq_p_trans2 {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2 :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLt h1 x y -> YjsLeq h2 y z -> exists h, YjsLt h x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hlt Hleq.
  exact: (yjs_leq'_p_trans2 inv x y z Hpx Hpy Hpz Hclosed (ex_intro _ h1 Hlt) (ex_intro _ h2 Hleq)).
Qed.

Lemma yjs_leq_p_trans {A} {P : ItemSet A} (inv : ItemSetInvariant P) (x y z : YjsPtr A) h1 h2 :
  P x -> P y -> P z -> IsClosedItemSet P ->
  YjsLeq h1 x y -> YjsLeq h2 y z -> exists h, YjsLeq h x z.
Proof.
  move=> Hpx Hpy Hpz Hclosed Hleq1 Hleq2.
  exact: (yjs_leq'_p_trans inv x y z Hpx Hpy Hpz Hclosed (ex_intro _ h1 Hleq1) (ex_intro _ h2 Hleq2)).
Qed.

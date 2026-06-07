(** No-cross-origin property.

    Port of [LeanYjs/Order/NoCrossOrigin.lean]: if [x < y] then either [y]'s
    origin is at most [x]'s origin, or [x] is at most [y]'s origin -- the two
    cannot "cross". Proved by strong induction on the size sum, using origin
    reachability/nearest-reachability and the order's transitivity/asymmetry. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import client_id item item_set util.
From yjs.order Require Import item_order item_set_invariant totality transitivity asymmetry.

(** A cyclic equation [itemPtr (Item ..) = <one of its sub-pointers>] is
    impossible by size. *)
Local Lemma not_self_origin {A} (i : YjsItem A) :
  itemPtr i <> origin i /\ itemPtr i <> rightOrigin i.
Proof. case: i => o r id c /=; split; move/(f_equal YjsPtr_size) => /=; lia. Qed.

Lemma no_cross_origin {A} {P : ItemSet A} :
  IsClosedItemSet P -> ItemSetInvariant P ->
  forall (x y : YjsItem A), P x -> P y -> YjsLt' x y ->
  YjsLeq' (origin y) (origin x) \/ YjsLeq' x (origin y).
Proof.
  move=> Hclosed inv.
  suff H : forall n (x y : YjsItem A), P x -> P y -> YjsLt' x y ->
    YjsItem_size x + YjsItem_size y = n ->
    YjsLeq' (origin y) (origin x) \/ YjsLeq' x (origin y).
  { move=> x y Hpx Hpy Hxy; exact: (H _ x y Hpx Hpy Hxy eq_refl). }
  apply: (nat_strong_ind (fun n => forall (x y : YjsItem A), P x -> P y -> YjsLt' x y ->
    YjsItem_size x + YjsItem_size y = n ->
    YjsLeq' (origin y) (origin x) \/ YjsLeq' x (origin y))).
  move=> n ih x y Hpx Hpy Hxy Hn.
  have Hpyo : P (origin y)
    by destruct y as [yo yr yid yc]; exact: (closedLeft _ Hclosed yo yr yid yc Hpy).
  case: (yjs_lt'_cases _ _ Hxy) =>
    [[Habs _] | [[Habs _] | [[xi [Hxeq Hle]] | [[yi [Hyeq Hle]] | Hconf]]]].
  - by [].
  - by [].
  - (* x's right origin is [<= y] *)
    destruct xi as [xo xr xid xc].
    have Ex : x = Item xo xr xid xc by congruence. subst x; simpl in Hle, Hn.
    have Hpxo : P xo by exact: (closedLeft _ Hclosed xo xr xid xc Hpx).
    have Hpxr : P xr by exact: (closedRight _ Hclosed xo xr xid xc Hpx).
    destruct xr as [xr' | | ].
    + (* right origin is an item [xr'] *)
      have Hpxr'o : P (origin xr')
        by destruct xr' as [a b c d]; exact: (closedLeft _ Hclosed a b c d Hpxr).
      case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle) => [Heq | Hlt].
      * (* right origin equals [y] *)
        have Exy : xr' = y by congruence. subst xr'.
        have Hreach : OriginReachable (Item xo (itemPtr y) xid xc) (origin y).
        { apply: (reachable_head _ (itemPtr y)).
          - exact: (reachable_right xo (itemPtr y) xid xc).
          - destruct y as [yo yr yid yc]; apply: reachable_single;
              exact: (reachable yo yr yid yc). }
        case: (origin_nearest_reachable _ inv xo (itemPtr y) xc xid (origin y) Hpx Hreach)
          => [Hle1 | Hle1]; first by left.
        case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle1) => [Heq2 | Hlt2].
        -- exfalso; move: Heq2; have [Hne _] := not_self_origin y; exact: Hne.
        -- exfalso. have Hory : YjsLt' (origin y) (itemPtr y)
             by destruct y as [yo yr yid yc]; apply: YjsLt'_ltOrigin;
                exact: (YjsLeq'_leqSame yo).
           exact: (yjs_lt_asymm Hclosed inv (origin y) (itemPtr y) Hpyo Hpy Hory Hlt2).
      * (* right origin is strictly before [y]: recurse *)
        have Hsz' : YjsItem_size xr' + YjsItem_size y < n by simpl in Hn; lia.
        case: (ih _ Hsz' xr' y Hpxr Hpy Hlt eq_refl) => [Hle2 | Hle2].
        -- (* origin y <= origin xr' <= xo *)
           left.
           have Hreach : OriginReachable (Item xo (itemPtr xr') xid xc) (origin xr').
           { apply: (reachable_head _ (itemPtr xr')).
             - exact: (reachable_right xo (itemPtr xr') xid xc).
             - destruct xr' as [a b c d]; apply: reachable_single;
                 exact: (reachable a b c d). }
           have Hxro : YjsLeq' (origin xr') xo.
           { case: (origin_nearest_reachable _ inv xo (itemPtr xr') xc xid (origin xr') Hpx Hreach)
               => [Hle3 | Hle3]; first exact: Hle3.
             exfalso; case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle3) => [Heq3 | Hlt3].
             - move: Heq3; have [Hne _] := not_self_origin xr'; exact: Hne.
             - have Hor : YjsLt' (origin xr') (itemPtr xr')
                 by destruct xr' as [a b c d]; apply: YjsLt'_ltOrigin;
                    exact: (YjsLeq'_leqSame a).
               exact: (yjs_lt_asymm Hclosed inv (origin xr') (itemPtr xr') Hpxr'o Hpxr Hor Hlt3). }
           exact: (yjs_leq'_p_trans inv (origin y) (origin xr') xo Hpyo Hpxr'o Hpxo Hclosed Hle2 Hxro).
        -- (* x < xr' <= origin y *)
           right; apply: (yjs_leq'_p_trans inv (Item xo (itemPtr xr') xid xc) (itemPtr xr')
                            (origin y) Hpx Hpxr Hpyo Hclosed _ Hle2).
           apply: YjsLeq'_leqLt; apply: YjsLt'_ltRightOrigin; exact: (YjsLeq'_leqSame (itemPtr xr')).
    + (* right origin is [First]: contradicts origin < First *)
      exfalso; case: (origin_not_leq _ inv xo First xc xid Hpx) => [h Hlt].
      exact: (not_ptr_lt_first Hclosed inv h xo Hpxo Hlt).
    + (* right origin is [Last]: contradicts Last < y *)
      exfalso; case: (yjs_leq'_imp_eq_or_yjs_lt' _ _ Hle) => [Heq | [h Hlt]];
        first by []. exact: (not_last_lt_ptr Hclosed inv h (itemPtr y) Hpy Hlt).
  - (* [x <= y's origin] directly *)
    have Eyi : yi = y by congruence. subst yi; by right.
  - (* conflict: origins are comparable *)
    case: Hconf => [hc Hconf]; left.
    inversion Hconf; subst.
    + apply: YjsLeq'_leqLt; by eexists; eassumption.
    + exact: (YjsLeq'_leqSame _).
Qed.

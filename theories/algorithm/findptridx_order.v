(** [findPtrIdx] order: index comparison reflects the document order [YjsLt'].
    Port of the [findPtrIdx_lt_YjsLt'] / [findPtrIdx_leq_YjsLeq'] theorems from
    [LeanYjs/Algorithm/Invariant/YjsArray.lean]. Kept separate from the
    sorted-index helpers so the heavy [gset] imports (via [insert_basic]) don't
    perturb those proofs. *)
From stdpp Require Import base list numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.
From yjs.order Require Import item_order.
From yjs.algorithm Require Import basic insert_basic insert_lemmas invariant_yjsarray invariant_yjsarray_idx.

Section findptridx_order.
Context {A : Type} `{EqDA : EqDecision A}.

Lemma findPtrIdx_lt_YjsLt' (arr : list (YjsItem A)) (x y : YjsPtr A) (i j : Z) :
  YjsArrInvariant arr ->
  findPtrIdx x arr = Some i -> findPtrIdx y arr = Some j -> (i < j)%Z ->
  YjsLt' x y.
Proof using A EqDA.
  move=> Hinv Hx Hy Hij; destruct x as [xx| |]; destruct y as [yy| |].
  - have [ix [Hix [_ Hax]]] := findPtrIdx_item_exists arr xx i Hx.
    have [jy [Hjy [_ Hay]]] := findPtrIdx_item_exists arr yy j Hy.
    apply: (getElem_lt_YjsLt' arr ix jy xx yy Hinv Hax Hay); lia.
  - have [ix [Hix [_ _]]] := findPtrIdx_item_exists arr xx i Hx.
    move: Hy => /= [= ?]; lia.
  - exists 0; apply: ltOriginOrder; apply: lt_last.
  - exists 0; apply: ltOriginOrder; apply: lt_first.
  - move: Hx Hy => /= [= ?] [= ?]; lia.
  - exists 0; apply: ltOriginOrder; apply: lt_first_last.
  - have [jy [Hjy [Hlty _]]] := findPtrIdx_item_exists arr yy j Hy.
    move: Hx => /= [= ?]; lia.
  - move: Hx Hy => /= [= ?] [= ?]; lia.
  - move: Hx Hy => /= [= ?] [= ?]; lia.
Qed.

Lemma findPtrIdx_leq_YjsLeq' (arr : list (YjsItem A)) (x y : YjsPtr A) (i j : Z) :
  YjsArrInvariant arr ->
  findPtrIdx x arr = Some i -> findPtrIdx y arr = Some j -> (i <= j)%Z ->
  YjsLeq' x y.
Proof using A EqDA.
  move=> Hinv Hx Hy Hij; destruct (decide (i = j)) as [->|Hne].
  - have Hxy : x = y := findPtrIdx_eq_ok_inj arr x y j Hx Hy.
    rewrite Hxy; exact: YjsLeq'_leqSame.
  - apply: YjsLeq'_leqLt; apply: (findPtrIdx_lt_YjsLt' arr x y i j Hinv Hx Hy); lia.
Qed.

End findptridx_order.

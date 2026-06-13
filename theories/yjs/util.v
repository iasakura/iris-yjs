(** Small general-purpose lemmas reused across the development. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.

(** Strong (course-of-values) induction on [nat]. *)
Lemma nat_strong_ind (Q : nat -> Prop) :
  (forall n, (forall m, m < n -> Q m) -> Q n) -> forall n, Q n.
Proof.
  move=> H n; apply: (H n).
  elim: n => [|n IH] m Hm; first (exfalso; lia).
  apply: (H m) => k Hk; apply: IH; lia.
Qed.

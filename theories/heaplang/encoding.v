(** HeapLang value encodings for the indirect Yjs model, and a heap linked-list
    representation predicate. This is the foundation of the HeapLang
    implementation: the imperative program operates on encoded values, and its
    specs are proven to refine the verified indirect functional model
    ([yjs.indirect]). Content is taken to be a HeapLang [val]. *)
From iris.heap_lang Require Import proofmode notation.
From yjs Require Import client_id item.
From yjs.indirect Require Import item.

(** Items whose content is a HeapLang value. *)
Notation IItem := (IYjsItem val).

(** Value encodings (pure, since ids / refs / items are immutable). *)
Definition encode_id (id : YjsId) : val := (#(clientId id), #(clock id)).

Definition encode_ref (r : YjsRef) : val :=
  match r with
  | RefId id => InjLV (encode_id id)
  | RefFirst => InjRV (InjLV #())
  | RefLast => InjRV (InjRV #())
  end.

Definition encode_item (it : IItem) : val :=
  (encode_ref (iorigin it), encode_ref (irightOrigin it), encode_id (iid it), icontent it).

(** Encoding an optional index as the result of a lookup. *)
Definition encode_oidx (o : option Z) : val :=
  match o with Some z => InjRV #z | None => InjLV #() end.

Section heaplang.
Context `{!heapGS Σ}.

(** A heap-allocated singly-linked list of values. *)
Fixpoint is_list (vs : list val) (v : val) : iProp Σ :=
  match vs with
  | [] => ⌜v = NONEV⌝
  | x :: xs => ∃ (l : loc) (v' : val), ⌜v = SOMEV #l⌝ ∗ l ↦ (x, v') ∗ is_list xs v'
  end.

(** Decide id equality by comparing the two integer fields. *)
Definition id_eq : val :=
  λ: "a" "b", (Fst "a" = Fst "b") && (Snd "a" = Snd "b").

Lemma id_eq_spec (i1 i2 : YjsId) :
  {{{ True }}} id_eq (encode_id i1) (encode_id i2)
  {{{ RET #(bool_decide (i1 = i2)); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". destruct i1 as [c1 k1], i2 as [c2 k2].
  rewrite /id_eq /encode_id /=. wp_pures.
  case_bool_decide as Hc; wp_pures.
  - injection Hc as Hc1 Hk1.
    rewrite bool_decide_eq_true_2; [|by rewrite Hc1]. wp_pures.
    rewrite bool_decide_eq_true_2; [|by rewrite Hk1]. by iApply "HΦ".
  - case_bool_decide as Hcc; wp_pures.
    + rewrite bool_decide_eq_false_2; [by iApply "HΦ"|].
      intros Hkk. apply Hc. f_equal; apply Nat2Z.inj; congruence.
    + by iApply "HΦ".
Qed.

End heaplang.

(** HeapLang implementation of the indirect Yjs lookups, with specs proving
    refinement of the verified functional model. The document is a heap
    singly-linked list of encoded items ([encoding.is_list]). *)
From iris.heap_lang Require Import proofmode notation.
From stdpp Require Import list numbers.
From yjs Require Import client_id item.
From yjs.indirect Require Import item insert_basic.
From yjs.heaplang Require Import encoding.

Section impl.
Context `{!heapGS Σ}.

(** Index of the first list element whose id equals [tid], starting the counter
    at [i]; [NONE] if absent. *)
Definition find_id : val :=
  rec: "go" "i" "tid" "l" :=
    match: "l" with
      NONE => NONE
    | SOME "p" =>
        let: "cell" := !"p" in
        if: id_eq (Snd (Fst (Fst "cell"))) "tid" then SOME "i"
        else "go" ("i" + #1) "tid" (Snd "cell")
    end.

Lemma find_id_spec (items : list IItem) (id : YjsId) (i : Z) (v : val) :
  {{{ is_list (encode_item <$> items) v }}}
    find_id #i (encode_id id) v
  {{{ r, RET r; is_list (encode_item <$> items) v ∗
      ⌜r = match list_find (fun it => iid it = id) items with
           | Some (j, _) => SOMEV #(i + Z.of_nat j)
           | None => NONEV end⌝ }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  iInduction items as [|it items IH] forall (i v Φ); simpl.
  - iDestruct "Hl" as %->. wp_rec. wp_pures. iApply "HΦ". by iFrame.
  - iDestruct "Hl" as (l v') "(-> & Hcell & Hrest)".
    wp_rec. wp_load. wp_pures.
    wp_apply (id_eq_spec (iid it) id with "[//]"); iIntros "_".
    case_bool_decide as Hcase; wp_pures.
    + iModIntro. iApply "HΦ". iSplitL "Hcell Hrest".
      { iExists l, v'. by iFrame. }
      iPureIntro. rewrite decide_True; [|exact Hcase]. simpl. do 3 f_equal. lia.
    + wp_apply ("IH" with "Hrest"). iIntros (r) "[Hrest %Hr]".
      iApply "HΦ". iSplitL "Hcell Hrest".
      { iExists l, v'. by iFrame. }
      iPureIntro. rewrite decide_False; [|exact Hcase]. rewrite Hr.
      destruct (list_find (fun it => iid it = id) items) as [[j y]|]; simpl;
        [do 3 f_equal; lia | done].
Qed.

(** List length (with an accumulator). *)
Definition llen : val :=
  rec: "go" "n" "l" :=
    match: "l" with NONE => "n" | SOME "p" => "go" ("n" + #1) (Snd (!"p")) end.

Lemma llen_spec (vs : list val) (n : Z) (v : val) :
  {{{ is_list vs v }}} llen #n v {{{ RET #(n + length vs); is_list vs v }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  iInduction vs as [|x vs IH] forall (n v Φ); simpl.
  - iDestruct "Hl" as %->. wp_rec. wp_pures.
    rewrite Z.add_0_r. iApply "HΦ". done.
  - iDestruct "Hl" as (l v') "(-> & Hcell & Hrest)".
    wp_rec. wp_load. wp_pures.
    wp_apply ("IH" with "Hrest"). iIntros "Hrest".
    rewrite (_ : (n + 1 + length vs)%Z = (n + S (length vs))%Z); last lia.
    iApply "HΦ". iExists l, v'. by iFrame.
Qed.

(** Resolve a [YjsRef] to an index, refining the functional [findRefIdx]. *)
Definition findRefIdx_impl : val :=
  λ: "r" "l",
    match: "r" with
      InjL "id" => find_id #0 "id" "l"
    | InjR "x" =>
        match: "x" with
          InjL <> => SOME #(-1)
        | InjR <> => SOME (llen #0 "l")
        end
    end.

Lemma findRefIdx_impl_spec (items : list IItem) (r : YjsRef) (v : val) :
  {{{ is_list (encode_item <$> items) v }}}
    findRefIdx_impl (encode_ref r) v
  {{{ res, RET res; is_list (encode_item <$> items) v ∗
      ⌜res = encode_oidx (findRefIdx r items)⌝ }}}.
Proof.
  iIntros (Φ) "Hl HΦ". destruct r as [id| |]; rewrite /findRefIdx_impl /encode_ref.
  - wp_pures. wp_apply (find_id_spec with "Hl"); iIntros (res) "[Hl %Hres]".
    iApply "HΦ". iFrame. iPureIntro.
    rewrite /findRefIdx Hres.
    destruct (list_find (fun it => iid it = id) items) as [[j y]|]; simpl;
      [do 3 f_equal; lia | done].
  - wp_pures. iApply "HΦ". by iFrame.
  - wp_pures. wp_apply (llen_spec with "Hl"); iIntros "Hl".
    wp_pures. iApply "HΦ". iFrame. iPureIntro.
    rewrite /findRefIdx /=. by rewrite length_fmap Z.add_0_l.
Qed.

End impl.

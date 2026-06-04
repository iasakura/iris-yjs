# Agent guide for iris-yjs

Porting the Yjs CRDT core and its proofs from `lean-yjs` (Lean 4) to Rocq/Iris.
Effects are modelled **relationally** (`op_effect : A → St → St → Prop`), not
functionally, because a HeapLang program denotes a relation. Proofs are written
in **ssreflect** style and must stay **axiom-free** (`Print Assumptions` =
"Closed under the global context").

## Build

Toolchain lives in the `iris_tutorial` opam switch (Rocq 9.1.1, coq-lsp/pet
0.2.5). Always build through it:

```sh
opam exec --switch iris_tutorial -- make
```

`_CoqProject` maps `-Q theories yjs`, so a file under `theories/foo/bar.v` is
`yjs.foo.bar`. A *correct* proof compiles in seconds; a multi-minute `make`
usually means a real error causing backtracking, not just proof size.

## Interactive proofs with rocq-mcp

The `rocq-mcp` MCP server (`mcp__rocq-mcp__*`) lets you inspect/step goals
without the full-file `make` loop. **Use it for any non-trivial proof.** But its
backing `petanque` (0.2.5) has sharp edges — read this before relying on it:

- **Only `rocq_start(theorem=NAME)` gives a steppable open goal.** And
  `find_thm` re-elaborates the statement in the file's *post-import* environment,
  so it **fails for any theorem whose statement mentions section-local
  definitions** (e.g. a record/def declared inside the `Section`) — even for
  already-compiled lemmas. `rocq_start(position=…)` only ever returns the
  proof's *terminal* state (post-`Qed`, or "goals you gave up" under `admit`),
  never an intermediate goal. `preamble` mode's `Require` silently loads
  nothing. `rocq_compile_file` fails ("coqc not found" — 9.x ships
  `rocq compile`, no `coqc`).

- **Working recipe for a section-nested / hard lemma:**
  1. Make the file compile (temporarily `Proof. Admitted.` the hard lemma) and
     `make` once so its `.vo` exists.
  2. In a scratch `.v` under `theories/` (so the `-Q theories yjs` load path
     applies), put the imports header + `From yjs… Require Import <module>.`,
     then state the lemma **at top level** with the section context as explicit
     binders (`{A S} \`{EqDecision A} … (O : @Operation A) (OV : OperationValidity O) …`).
     Get the discharged signatures with `rocq_query(command="Check @foo.",
     file=scratch)` against the **built `.vo`** — inline file-mode queries are
     unreliable (they see only the post-import env, not the file's own defs).
  3. `rocq_start(theorem="scratch_lemma", file=scratch, timeout=180)` → real
     initial goal; then `rocq_check(from_state=ID, body="…", timeout=180)` to
     advance in chunks. On error it returns `last_valid_state_id` to resume
     from. Pass `force_restart=true` after rebuilding a dependency `.vo`.
  4. Once it goes through, write the proof into the real file. A top-level lemma
     (operation `O` explicit) transplants 1:1; putting it back **inside** the
     section means de-`O`-ing every helper call (`effect_list O …` →
     `effect_list …`, `isValidState_of_history _ _ _ _ _ RV` → `… _ _ _ _ RV`,
     etc.) — error-prone, so top-level placement after `End` is often simplest.

- **Gotchas while stepping:** chunked `rocq_check` across `}`/bullet boundaries
  can report "0/2 focused goals" — `rocq_query(command="Show.", from_state=ID)`
  will say to issue `}` to unfocus. `set_solver` on list `∈` can throw "No
  matching clauses for match" when a needed `∉`/`≠` fact is absent from context
  (add it as a `have` first). `/=` that unfolds an `op_effect` record projection
  also triggers that error — destructure the definitional `∃`/`∧` instead.

## stdpp / Rocq idioms that bit us

- `++` is right-associative: `l ++ m ++ [a]` is `l ++ (m ++ [a])`; relate to
  `(l ++ m) ++ [a]` with `rewrite app_assoc` (forward = right→left assoc) /
  `-app_assoc` (backward). Don't add `rewrite -app_assoc` "just in case" — it
  errors with "no subterm" when the list is already right-associated.
- Names that moved: `list_elem_of_split` (not `elem_of_list_split`),
  `sublist_NoDup : NoDup l2 → l1 ⊑ l2 → NoDup l1` (not `NoDup_sublist`; its
  `l2` is positional, use `sublist_NoDup _ big`), `list_elem_of_fmap_2`.
  There is no `sublist_drop_mid` — build sublists from `sublist_app` +
  `sublist_cons` (drops head) + `sublist_inserts_r` (drops suffix);
  `reflexivity` closes `sublist l l`.
- ssreflect `=> ->` rewrites the goal only; to rewrite hyps use a named eq +
  `subst`. `rewrite Heq` needs the LHS of `Heq` to occur in the goal — mind the
  direction (`-Heq`).

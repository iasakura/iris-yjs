(** Common prelude for the iris-yjs development.

    Re-exports the HeapLang language and the Iris proof mode, which form the
    basis for verifying the Yjs core algorithm. *)
From iris.heap_lang Require Export lang notation proofmode.
From iris.prelude Require Export options.

# iris-yjs

Verification of the Yjs CRDT core algorithm in Iris/HeapLang.

This project ports the Yjs core algorithm and its correctness proofs from
[iasakura/lean-yjs](https://github.com/iasakura/lean-yjs) (originally
formalized in Lean 4) to the [Iris](https://iris-project.org/) separation
logic framework instantiated on HeapLang, with the goal of verifying an
implementation closer to a real one.

## Build

```sh
opam install . --deps-only
make
```

## Dependencies

- Rocq 9.2.0
- Iris 4.5.0
- Iris HeapLang 4.5.0

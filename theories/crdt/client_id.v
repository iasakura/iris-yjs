(** Client identifiers.

    Port of [LeanYjs/ClientId.lean]. A client id is just a natural number; it
    inherits the usual order and decidable equality from [nat]. *)
From stdpp Require Import base numbers.
From stdpp Require Import options.

Definition ClientId := nat.

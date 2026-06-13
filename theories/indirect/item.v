(** The "indirect" (by-id-reference) item representation: an item references
    its origin / right-origin by [YjsId] instead of embedding them structurally.
    Port of [LeanYjs/Indirect/Item.lean]. This is closer to a real Yjs
    implementation — a flat array of records with id references, rather than the
    structurally-nested "direct" [YjsItem]. The [Equivalence] layer shows the
    indirect algorithm computes the same result as the verified direct one. *)
From stdpp Require Import base numbers.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From yjs Require Import item.

(** A reference: to an item by id, or to a document boundary. *)
Inductive YjsRef := RefId (id : YjsId) | RefFirst | RefLast.

Global Instance YjsRef_eq_dec : EqDecision YjsRef.
Proof. solve_decision. Defined.

Definition ofDirectPtr {A} (p : YjsPtr A) : YjsRef :=
  match p with
  | itemPtr item => RefId (item_id item)
  | First => RefFirst
  | Last => RefLast
  end.

Definition ofOriginId (o : option YjsId) : YjsRef :=
  match o with Some id => RefId id | None => RefFirst end.

Definition ofRightOriginId (o : option YjsId) : YjsRef :=
  match o with Some id => RefId id | None => RefLast end.

(** An indirect item: origin / right-origin are id references. *)
Record IYjsItem (A : Type) := MkIYjsItem {
  iorigin : YjsRef;
  irightOrigin : YjsRef;
  iid : YjsId;
  icontent : A;
}.
Arguments MkIYjsItem {A} _ _ _ _.
Arguments iorigin {A} _.
Arguments irightOrigin {A} _.
Arguments iid {A} _.
Arguments icontent {A} _.

Global Instance IYjsItem_eq_dec {A} `{EqDecision A} : EqDecision (IYjsItem A).
Proof. solve_decision. Defined.

(** Erase a direct item to its indirect (by-id) form. *)
Definition ofDirectItem {A} (item : YjsItem A) : IYjsItem A :=
  MkIYjsItem (ofDirectPtr (origin item)) (ofDirectPtr (rightOrigin item))
             (item_id item) (content item).

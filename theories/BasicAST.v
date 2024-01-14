From Coq Require Import Utf8.

Definition level := nat.

Inductive mode := mKind | mType | mGhost | mProp.

Inductive cmode := cType | cProp.

(* Variable role: regular or parametricity. *)
Inductive role := reg | prm.

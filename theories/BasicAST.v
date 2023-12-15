From Coq Require Import Utf8.

Definition level := nat.

Inductive mode := mKind | mType | mGhost | mProp.

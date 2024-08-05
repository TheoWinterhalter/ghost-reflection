From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped RAsimpl CCAST_rasimpl GAST_rasimpl.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Univ.

Import ListNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Notation "A ⇒[ i | j / mx | m ] B" :=
  (Pi i j m mx A (shift ⋅ B))
  (at level 20, i, j, mx, m at next level, right associativity).

Notation top := (bot ⇒[ 0 | 0 / mProp | mProp ] bot).

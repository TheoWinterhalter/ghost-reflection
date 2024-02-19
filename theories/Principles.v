(*** Testing principles obtained from parametricity ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory CCMetaTheory Admissible
  Erasure Revival Param.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** f : erased A → B has to be the constant function

  But to even state it we need more base types, so not great is it?
  Typically B should be a base type. We could maybe add bool to do it…

**)

Transparent close ignore epm_lift rpm_lift.

Section Principles.

  Context (A : term).

  Eval lazy in  ⟦ [] | Erased A ⇒[ 0 | 0 / mGhost | mType ] A ⟧p.

End Principles.

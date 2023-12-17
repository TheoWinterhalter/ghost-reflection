(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.
  We rely here on the notion of action to include both renamings and
  substitution.

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import unscoped.

Class Action (A G : Type) :=
  action : A → G → G.

#[export] Instance ActionSubst1 X Y (H : Subst1 X Y Y) : Action X Y :=
  subst1.

#[export] Instance ActionRen1 X Y (H : Ren1 X Y Y) : Action X Y :=
  ren1.

Notation "a ⋅ x" :=
  (action a x) (at level 7, right associativity) : subst_scope.

Notation "↑" := (shift) : subst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

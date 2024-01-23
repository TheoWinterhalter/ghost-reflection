(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import core unscoped GAST CCAST.

Notation "a ⋅ x" :=
  (ren1 a x) (at level 20, right associativity) : subst_scope.

Notation "t <[ s ]" :=
  (subst1 s t) (at level 10, right associativity) : subst_scope.

Notation "↑" := (shift) : subst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Ltac autosubst_unfold :=
  unfold Ren_cterm, upRen_cterm_cterm, Subst_cterm, VarInstance_cterm,
    upRen_cterm_cterm, Ren_term, Subst_term.

Ltac resubst :=
  rewrite ?renRen_cterm, ?renSubst_cterm, ?substRen_cterm, ?substSubst_cterm,
    ?renRen_term, ?renSubst_term, ?substRen_term.

Ltac ssimpl :=
  asimpl ;
  autosubst_unfold ;
  asimpl ;
  repeat unfold_funcomp ;
  resubst ;
  asimpl ;
  repeat unfold_funcomp.

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST CCAST.
From GhostTT Require Import BasicAST.

(** Contexts store for each variable its type and mode.

  The mode is redundant information already contained in the type, but we only
  establish that later. Storing this information is useful to perform syntactic
  transformations: typically conversion and the syntactic model.

**)

Notation decl := (mode * term)%type.

Notation context := (list decl).

Notation scope := (list mode).

Definition sc (Γ : context) : scope :=
  map fst Γ.

Notation "'∙'" :=
  (@nil decl).

Notation "Γ ,, d" :=
  (@cons decl d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@app decl Δ Γ) (at level 25, Δ at next level, left associativity).


(** Same thing for CC **)

Notation cdecl := (cmode * cterm)%type.

Notation ccontext := (list cdecl).

Notation cscope := (list cmode).

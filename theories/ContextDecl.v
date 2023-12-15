From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST.
From GhostTT Require Import BasicAST.

(** Contexts store for each variable its type and mode.

  The mode is redundant information already contained in the type, but we only
  establish that later. Storing this information is useful to perform syntactic
  transformations: typically conversion and the syntactic model.

**)

Definition decl := (mode * term)%type.

Definition context := list decl.

Notation "'∙'" :=
  (@nil term).

Notation "Γ ,, d" :=
  (@cons term d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@app term Δ Γ) (at level 25, Δ at next level, left associativity).

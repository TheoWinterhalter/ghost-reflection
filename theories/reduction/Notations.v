From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import BasicAST ContextDecl Scoping TermNotations.

(** General notations **)

(* Substitution of var 0 *)
Notation "s '··'" := (scons s ids) (at level 1, format "s ··") : subst_scope.

(* scope and context *)
(* A is of scope m *)
Notation "Γ ⊢ A ∷ m" := (scoping (sc Γ) A m) 
  (at level 80, Γ constr, A, m at next level, format "Γ ⊢ A ∷ m").
Notation "Γ ⊨ A ∷ m" := (scoping Γ A m) 
  (at level 80, A, m at next level, format "Γ ⊨ A ∷ m").

(*Mode abreviations*)
Notation ℙ := mProp.
Notation 𝔾 := mGhost.
Notation 𝕋 := mType.
Notation 𝕂 := mKind.

Notation "⊥" := bot.
Notation "⊤" := top.
Notation "⋆" := (lam ℙ ⊥ (var 0)).

(** Notation for reductions **)

(* Multi-step reduction *)
Reserved Notation "Γ ⊨ u ⇶ v"
  (at level 80, u, v at next level, format "Γ ⊨ u ⇶ v").
Reserved Notation "Γ ⊨ u ⇶* v"
  (at level 80, u, v at next level, format "Γ ⊨ u ⇶* v").
Reserved Notation "Γ ⊨ u ε⇶ v"
        (at level 80, u, v at next level, format "Γ ⊨ u ε⇶ v").

(* Step by step reduction *)
Reserved Notation "u ↣ v"
  (at level 80, v at next level, format "u ↣ v").
 

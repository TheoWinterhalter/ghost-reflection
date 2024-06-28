(* All global notations defined in the reduction folder *)
(* Some notations used in this folder come from other parts of the repository 
 and aren't listed here (for example from GhostTT.SubstNotations or Coq.Utf8) *)
(* List of special caracters used : 
   · ℙ 𝔾 𝕋 𝕂 ⊥ ⊤ ⋆ ⊢ ⊨ ∷ ⇶ ε □ ¹ ² ↣ ⇜ *)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import BasicAST ContextDecl Scoping Typing.
From GhostTT Require Export SubstNotations.

(** General notations **)

(* Substitution of var 0 *)
Notation "s '··'" := (scons s ids) (at level 1, format "s ··") : subst_scope.


Declare Scope term_scope.
Open Scope term_scope.

(*Mode abreviations*)
Notation "'ℙ'" := mProp : term_scope.
Notation "'𝔾'" := mGhost : term_scope.
Notation "'𝕋'" := mType : term_scope.
Notation "'𝕂'" := mKind : term_scope.

(*Term abreviations*)
Notation "⊥" := bot : term_scope.
Notation "⊤" := (Pi 0 0 ℙ ℙ ⊥ ⊥) : term_scope.
Notation "⋆" := (lam ℙ ⊥ (var 0)) : term_scope.



(* A is of scope m *)
Notation "Γ '⊢' A ∷ m" := (scoping (sc Γ) A m) 
  (at level 80, A, m at next level, format "Γ ⊢ A ∷ m") : term_scope.
Notation "Γ '⊨' A ∷ m" := (scoping Γ A m) 
  (at level 80, A, m at next level, format "Γ ⊨ A ∷ m") : term_scope.

(** Notation for reductions **)
Declare Scope red_scope.
Open Scope red_scope.

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


(** Notation for wrapping **)
Declare Scope wrap_scope.
Open Scope wrap_scope.
 
Reserved Notation "□¹_term" (at level 0).
Reserved Notation "□²_term" (at level 0).
Reserved Notation "□_term" (at level 0).
Reserved Notation "C '[□/' t ']'" (at level 70).
Reserved Notation "C '[□¹/' t ']'" (at level 70).
Reserved Notation "C '[□²/' t ']'" (at level 70).

Reserved Notation "Γ ⇜~ C" (at level 70).
Reserved Notation "Γ ⇜ C" (at level 70).

Reserved Notation "Γ ⇜ C ⊢ t : A"
  (at level 80, t, A at next level, format "Γ ⇜ C ⊢ t : A", only printing).
Reserved Notation "Γ ⇜ C ⊢ t ∷ m"
  (at level 80, t, m at next level, format "Γ ⇜ C ⊢ t ∷ m", only printing).
Reserved Notation "Γ ⇜ C ⊨ t ∷ m"
  (at level 80, t, m at next level, format "Γ ⇜ C ⊨ t ∷ m", only printing).

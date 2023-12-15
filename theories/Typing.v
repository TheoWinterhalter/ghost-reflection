From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST.
From GhostTT Require Import BasicAST ContextDecl CastRemoval TermMode.

Set Default Goal Selector "!".

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢  t  :  A").

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Inductive typing (Γ : context) : term → term → Prop :=

| type_var :
    ∀ x m A,
      nth_error Γ x = Some (m, A) →
      Γ ⊢ var x : A

where "Γ ⊢ t : A" := (typing Γ t A)

with conversion (Γ : context) : term → term → Prop :=

(* Computation rules *)

(* Congruence rules *)

| cong_Pi :
    ∀ m mx A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      Γ ⊢ Pi m mx A B ≡ Pi m mx A' B'


(* Structural rules *)

| conv_refl :
    ∀ u,
      Γ ⊢ u ≡ u

| conv_sym :
    ∀ u v,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ u

| conv_trans :
    ∀ u v w,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ w →
      Γ ⊢ u ≡ w

where "Γ ⊢ u ≡ v" := (conversion Γ u v).

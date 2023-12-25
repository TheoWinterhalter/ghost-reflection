(** Scoping for CC

  Stating that all variables are in a given cscope, and in a given mode.

  TODO: Using cscoping is going to conflict with cscoping...

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl.

Import ListNotations.

Set Default Goal Selector "!".

(* Inductive cscoping (Γ : cscope) : cterm → cmode → Prop :=

| cscope_var :
    ∀ x m,
      nth_error Γ x = Some m →
      scoping Γ (var x) m

| scpoe_sort :
    ∀ m i,
      scoping Γ (Sort m i) mKind

| cscope_pi :
    ∀ i j mx m A B,
      scoping Γ A mKind →
      scoping (mx :: Γ) B mKind →
      scoping Γ (Pi i j m mx A B) mKind

| cscope_lam :
    ∀ mx m A B t,
      scoping Γ A mKind →
      scoping (mx :: Γ) B mKind →
      scoping (mx :: Γ) t m →
      scoping Γ (lam mx A B t) m

| cscope_app :
    ∀ mx m t u,
      scoping Γ t m →
      scoping Γ u mx →
      scoping Γ (app t u) m

| cscope_erased :
    ∀ A,
      scoping Γ A mKind →
      scoping Γ (Erased A) mKind

| cscope_erase :
    ∀ t,
      scoping Γ t mType →
      scoping Γ (erase t) mGhost

| cscope_reveal :
    ∀ m t P p,
      In m [ mProp ; mGhost ] →
      scoping Γ t mGhost →
      scoping Γ P mKind →
      scoping Γ p m →
      scoping Γ (reveal t P p) m

| cscope_revealP :
    ∀ t p,
      scoping Γ t mGhost →
      scoping Γ p mKind →
      scoping Γ (revealP t p) mKind

| cscope_gheq :
    ∀ A u v,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ (gheq A u v) mKind

| cscope_ghrefl :
    ∀ A u,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ (ghrefl A u) mProp

| cscope_ghcast :
    ∀ m A u v e P t,
      m ≠ mKind →
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ e mProp →
      scoping Γ P mKind →
      scoping Γ t m →
      scoping Γ (ghcast e P t) m

| cscope_bot :
    scoping Γ bot mKind

| cscope_bot_elim :
    ∀ m A p,
      scoping Γ A mKind →
      scoping Γ p mProp →
      scoping Γ (bot_elim m A p) m
.

Notation cscoping Γ := (scoping (sc Γ)). *)

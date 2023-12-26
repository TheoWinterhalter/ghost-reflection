(** Scoping for CC

  Stating that all variables are in a given cscope, and in a given mode.

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl.

Import ListNotations.

Set Default Goal Selector "!".

Inductive ccscoping (Γ : cscope) : cterm → cmode → Prop :=

| cscope_var :
    ∀ x m,
      nth_error Γ x = Some m →
      ccscoping Γ (cvar x) m

| scpoe_sort :
    ∀ m i,
      ccscoping Γ (cSort m i) cType

| cscope_pi :
    ∀ mx A B,
      ccscoping Γ A cType →
      ccscoping (mx :: Γ) B cType →
      ccscoping Γ (cPi mx A B) cType

| cscope_lam :
    ∀ mx m A t,
      ccscoping Γ A cType →
      ccscoping (mx :: Γ) t m →
      ccscoping Γ (clam mx A t) m

| cscope_app :
    ∀ mx m t u,
      ccscoping Γ t m →
      ccscoping Γ u mx →
      ccscoping Γ (capp t u) m

| cscope_bot :
    ccscoping Γ cbot cType

| cscope_bot_elim :
    ∀ m A p,
      ccscoping Γ A cType →
      ccscoping Γ p cProp →
      ccscoping Γ (cbot_elim m A p) m
.

Notation ccxscoping Γ := (ccscoping (csc Γ)).

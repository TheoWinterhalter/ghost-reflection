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
      nth_error Γ x = Some (Some m) →
      ccscoping Γ (cvar x) m

| scpoe_sort :
    ∀ m i,
      ccscoping Γ (cSort m i) cType

| cscope_pi :
    ∀ mx A B,
      ccscoping Γ A cType →
      ccscoping (Some mx :: Γ) B cType →
      ccscoping Γ (cPi mx A B) cType

| cscope_lam :
    ∀ mx m A t,
      ccscoping Γ A cType →
      ccscoping (Some mx :: Γ) t m →
      ccscoping Γ (clam mx A t) m

| cscope_app :
    ∀ mx m t u,
      ccscoping Γ t m →
      ccscoping Γ u mx →
      ccscoping Γ (capp t u) m

| cscope_unit :
    ccscoping Γ cunit cType

| cscope_tt :
    ccscoping Γ ctt cType

| cscope_top :
    ccscoping Γ ctop cType

| cscope_star :
    ccscoping Γ cstar cProp

| cscope_bot :
    ccscoping Γ cbot cType

| cscope_bot_elim :
    ∀ m A p,
      ccscoping Γ A cType →
      ccscoping Γ p cProp →
      ccscoping Γ (cbot_elim m A p) m

| cscope_ty :
    ∀ i,
      ccscoping Γ (cty i) cType

| cscope_tyval :
    ∀ A a,
      ccscoping Γ (ctyval A a) cType

| cscope_tyerr :
    ccscoping Γ ctyerr cType

| cscope_El :
    ∀ T,
      ccscoping Γ (cEl T) cType

| cscope_Err :
    ∀ T,
      ccscoping Γ (cErr T) cType
.

Notation ccxscoping Γ := (ccscoping (csc Γ)).

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

| cscope_sort :
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
    ∀ mk A a,
      ccscoping Γ A cType →
      ccscoping Γ a cType →
      ccscoping Γ (ctyval mk A a) cType

| cscope_tyerr :
    ccscoping Γ ctyerr cType

| cscope_El :
    ∀ T,
      ccscoping Γ T cType →
      ccscoping Γ (cEl T) cType

| cscope_Err :
    ∀ T,
      ccscoping Γ T cType →
      ccscoping Γ (cErr T) cType

| cscope_squash :
    ∀ A,
      ccscoping Γ A cType →
      ccscoping Γ (squash A) cType

| cscope_sq :
    ∀ t,
      ccscoping Γ t cType →
      ccscoping Γ (sq t) cProp

| cscope_sq_elim :
    ∀ e P t,
      ccscoping Γ e cProp →
      ccscoping Γ P cType →
      ccscoping Γ t cProp →
      ccscoping Γ (sq_elim e P t) cProp

| cscope_teq :
    ∀ A u v,
      ccscoping Γ A cType →
      ccscoping Γ u cType →
      ccscoping Γ v cType →
      ccscoping Γ (teq A u v) cType

| cscope_trefl :
    ∀ A u,
      ccscoping Γ A cType →
      ccscoping Γ u cType →
      ccscoping Γ (trefl A u) cType

| cscope_tJ :
    ∀ e P t m,
      ccscoping Γ e cType →
      ccscoping Γ P cType →
      ccscoping Γ t m →
      ccscoping Γ (tJ e P t) m

| cscope_ebool :
    ccscoping Γ ebool cType

| cscope_etrue :
    ccscoping Γ etrue cType

| cscope_efalse :
    ccscoping Γ efalse cType

| cscope_bool_err :
    ccscoping Γ bool_err cType

| cscope_eif :
    ∀ m b P t f e,
      ccscoping Γ b cType →
      ccscoping Γ P cType →
      ccscoping Γ t m →
      ccscoping Γ f m →
      ccscoping Γ e m →
      ccscoping Γ (eif m b P t f e) m

| cscope_pbool :
    ccscoping Γ pbool cType

| cscope_ptrue :
    ccscoping Γ ptrue cProp

| cscope_pfalse :
    ccscoping Γ pfalse cProp

| cscope_pif :
    ∀ bP P t f,
      ccscoping Γ bP cProp →
      ccscoping Γ P cType →
      ccscoping Γ t cProp →
      ccscoping Γ f cProp →
      ccscoping Γ (pif bP P t f) cProp

| cscope_enat :
    ccscoping Γ enat cType

| cscope_ezero :
    ccscoping Γ ezero cType

| cscope_esucc :
    ∀ n,
      ccscoping Γ n cType →
      ccscoping Γ (esucc n) cType

| cscope_enat_elim :
    ∀ n P z s,
      ccscoping Γ n cType →
      ccscoping Γ P cType →
      ccscoping Γ z cType →
      ccscoping Γ s cType →
      ccscoping Γ (enat_elim n P z s) cType
.

Notation ccxscoping Γ := (ccscoping (csc Γ)).

Create HintDb cc_scope discriminated.

Hint Constructors ccscoping : cc_scope.

Ltac escope :=
  unshelve typeclasses eauto with cc_scope shelvedb ; shelve_unifiable.

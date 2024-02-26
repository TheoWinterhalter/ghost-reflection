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

| cscope_pnat :
    ccscoping Γ pnat cType

| cscope_pzero :
    ccscoping Γ pzero cProp

| cscope_psucc :
    ∀ n,
      ccscoping Γ n cProp →
      ccscoping Γ (psucc n) cProp

| cscope_pnat_elim :
    ∀ ne nP Pe PP ze zP se sP,
      ccscoping Γ ne cType →
      ccscoping Γ nP cProp →
      ccscoping Γ Pe cType →
      ccscoping Γ PP cType →
      ccscoping Γ ze cType →
      ccscoping Γ zP cProp →
      ccscoping Γ se cType →
      ccscoping Γ sP cProp →
      ccscoping Γ (pnat_elim ne nP Pe PP ze zP se sP) cProp

| cscope_pnat_elimP :
    ∀ ne nP Pe PP zP sP,
      ccscoping Γ ne cType →
      ccscoping Γ nP cProp →
      ccscoping Γ Pe cType →
      ccscoping Γ PP cType →
      ccscoping Γ zP cProp →
      ccscoping Γ sP cProp →
      ccscoping Γ (pnat_elimP ne nP Pe PP zP sP) cProp

| cscope_evec :
    ∀ A,
      ccscoping Γ A cType →
      ccscoping Γ (evec A) cType

| cscope_evnil :
    ∀ A,
      ccscoping Γ A cType →
      ccscoping Γ (evnil A) cType

| cscope_evcons :
    ∀ a v,
      ccscoping Γ a cType →
      ccscoping Γ v cType →
      ccscoping Γ (evcons a v) cType

| cscope_evec_elim :
    ∀ v P z s,
      ccscoping Γ v cType →
      ccscoping Γ P cType →
      ccscoping Γ z cType →
      ccscoping Γ s cType →
      ccscoping Γ (evec_elim v P z s) cType

| cscope_pvec :
    ∀ A AP n nP,
      ccscoping Γ A cType →
      ccscoping Γ AP cType →
      ccscoping Γ n cType →
      ccscoping Γ nP cProp →
      ccscoping Γ (pvec A AP n nP) cType

| cscope_pvnil :
    ∀ AP,
      ccscoping Γ AP cType →
      ccscoping Γ (pvnil AP) cProp

| cscope_pvcons :
    ∀ aP nP vP,
      ccscoping Γ aP cProp →
      ccscoping Γ nP cProp →
      ccscoping Γ vP cProp →
      ccscoping Γ (pvcons aP nP vP) cProp

| cscope_pvec_elim :
    ∀ A AP n nP v vP P PP z zP s sP,
      ccscoping Γ A cType →
      ccscoping Γ AP cType →
      ccscoping Γ n cType →
      ccscoping Γ nP cProp →
      ccscoping Γ v cType →
      ccscoping Γ vP cProp →
      ccscoping Γ P cType →
      ccscoping Γ PP cType →
      ccscoping Γ z cType →
      ccscoping Γ zP cProp →
      ccscoping Γ s cType →
      ccscoping Γ sP cProp →
      ccscoping Γ (pvec_elim A AP n nP v vP P PP z zP s sP) cProp

| cscope_pvec_elimP :
    ∀ A AP n nP v vP P PP z s,
      ccscoping Γ A cType →
      ccscoping Γ AP cType →
      ccscoping Γ n cType →
      ccscoping Γ nP cProp →
      ccscoping Γ v cType →
      ccscoping Γ vP cProp →
      ccscoping Γ P cType →
      ccscoping Γ PP cType →
      ccscoping Γ z cProp →
      ccscoping Γ s cProp →
      ccscoping Γ (pvec_elimP A AP n nP v vP P PP z s) cProp
.

Notation ccxscoping Γ := (ccscoping (csc Γ)).

Create HintDb cc_scope discriminated.

Hint Constructors ccscoping : cc_scope.

Ltac escope :=
  unshelve typeclasses eauto with cc_scope shelvedb ; shelve_unifiable.

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST ContextDecl CastRemoval TermMode.

(* TODO The substitution notation is broken, make new better ones? *)
(* Import SubstNotations UnscopedNotations. *)

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

| conv_irr :
    ∀ p q,
      md Γ p = mProp →
      md Γ q = mProp →
      Γ ⊢ p ≡ q

| conv_beta :
    ∀ mx A t u,
      md Γ u = mx →
      (* Γ ⊢ app (lam mx A t) u ≡ t [ u .. ] *)
      Γ ⊢ app (lam mx A t) u ≡ subst1 (scons u ids) t

| reveal_erase :
    ∀ t P p,
      In (md Γ p) [ mProp ; mGhost ] →
      In (md Γ t) [ mType ; mKind ] →
      Γ ⊢ reveal (erase t) P p ≡ app p t

| revealP_erase :
    ∀ t P p,
      md Γ p = mKind →
      md Γ t = mType →
      Γ ⊢ revealP (erase t) p ≡ app p t

(* Congruence rules *)

| cong_Pi :
    ∀ m mx A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      Γ ⊢ Pi m mx A B ≡ Pi m mx A' B'

| cong_lam :
    ∀ mx A A' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ t ≡ t' →
      Γ ⊢ lam mx A t ≡ lam mx A' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

| cong_Erased :
    ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ Erased A ≡ Erased A'

| cong_erase :
    ∀ u u',
      Γ ⊢ u ≡ u' →
      Γ ⊢ erase u ≡ erase u'

| cong_reveal :
    ∀ t t' P P' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ reveal t P p ≡ reveal t' P' p'

| cong_revealP :
    ∀ t t' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ revealP t p ≡ revealP t' p'

| cong_gheq :
    ∀ A A' u u' v v',
      Γ ⊢ A ≡ A' →
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ gheq A u v ≡ gheq A' u' v'

(* No need for it thanks to proof irrelevance *)
(* | cong_ghrefl :
    ∀ A A' u u',
      Γ ⊢ A ≡ A' →
      Γ ⊢ u ≡ u' →
      Γ ⊢ ghrefl A u ≡ ghrefl A' u' *)

| cong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ A ≡ A' →
      Γ ⊢ bot_elim m A p ≡ bot_elim m A' p'

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

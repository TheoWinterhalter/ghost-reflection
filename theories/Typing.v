From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST ContextDecl CastRemoval TermMode.

Import ListNotations.

(* TODO The substitution notation is broken, make new better ones? *)
(* Import SubstNotations UnscopedNotations. *)

Set Default Goal Selector "!".

Notation "A ⇒[ mx | m ] B" :=
  (Pi m mx A (ren1 shift B))
  (at level 20, mx, m at next level, right associativity).

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢  t  :  A").

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Inductive typing (Γ : context) : term → term → Prop :=

| type_var :
    ∀ x m A,
      nth_error Γ x = Some (m, A) →
      Γ ⊢ var x : A

| type_sort :
    ∀ m i j,
      i < j →
      Γ ⊢ Sort m i : Sort m j

| type_pi :
    ∀ mx m i j A B,
      mdc Γ A = mKind →
      mdc (Γ ,, (mx, A)) B = mKind →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ Pi m mx A B : Sort m (max i j)

| type_lam :
    ∀ mx m i j A B t,
      mdc Γ A = mKind →
      mdc (Γ ,, (mx, A)) t = m →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ,, (mx, A) ⊢ t : B →
      Γ ⊢ lam mx A t : Pi m mx A B

| type_app :
    ∀ mx m A B t u,
      mdc Γ t = m →
      mdc Γ u = mx →
      Γ ⊢ t : Pi m mx A B →
      Γ ⊢ u : A →
      Γ ⊢ app t u : subst1 (scons u ids) B

| type_erased :
    ∀ i A,
      mdc Γ A = mKind →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ Erased A : Sort mGhost i

| type_erase :
    ∀ i A t,
      mdc Γ A = mKind →
      mdc Γ t = mType →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ t : A →
      Γ ⊢ erase t : Erased A

| type_reveal :
    ∀ i m A t P p,
      mdc Γ p = m →
      mdc Γ t = mGhost →
      mdc Γ P = mKind →
      In m [ mProp ; mGhost ] →
      Γ ⊢ t : Erased A →
      Γ ⊢ P : Erased A ⇒[ mGhost | mKind ] Sort m i →
      Γ ⊢ p : Pi m mType A (app P (erase (var 0))) →
      Γ ⊢ reveal t P p : app P t

| type_revealP :
    ∀ A t p,
      mdc Γ t = mGhost →
      mdc Γ p = mKind →
      Γ ⊢ t : Erased A →
      Γ ⊢ p : A ⇒[ mType | mKind ] Sort mProp 0 →
      Γ ⊢ revealP t p : Sort mProp 0

| type_gheq :
    ∀ i A u v,
      mdc Γ A = mKind →
      mdc Γ u = mGhost →
      mdc Γ v = mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ gheq A u v : Sort mProp 0

| type_ghrefl :
    ∀ i A u,
      mdc Γ A = mKind →
      mdc Γ u = mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ ghrefl A u : gheq A u u

| type_ghcast :
    ∀ i m A u v e P t,
      mdc Γ A = mKind →
      mdc Γ P = mKind →
      mdc Γ u = mGhost →
      mdc Γ v = mGhost →
      mdc Γ t = m →
      mdc Γ e = mProp →
      m ≠ mKind →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ e : gheq A u v →
      Γ ⊢ P : A ⇒[ mGhost | mKind ] Sort m i →
      Γ ⊢ ghcast e P t : app P v

| type_bot :
    Γ ⊢ bot : Sort mProp 0

| type_bot_elim :
    ∀ i m A p,
      mdc Γ A = mKind →
      mdc Γ p = mProp →
      Γ ⊢ A : Sort m i →
      Γ ⊢ p : bot →
      Γ ⊢ bot_elim m A p : A

| type_conv :
    ∀ i m A B t,
      mdc Γ B = mKind →
      mdc Γ t = m →
      Γ ⊢ t : A →
      Γ ⊢ A ≡ B →
      Γ ⊢ B : Sort m i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A)

with conversion (Γ : context) : term → term → Prop :=

(* Computation rules *)

| conv_irr :
    ∀ p q,
      mdc Γ p = mProp →
      mdc Γ q = mProp →
      Γ ⊢ p ≡ q

| conv_beta :
    ∀ mx A t u,
      mdc Γ u = mx →
      (* Γ ⊢ app (lam mx A t) u ≡ t [ u .. ] *)
      Γ ⊢ app (lam mx A t) u ≡ subst1 (scons u ids) t

| reveal_erase :
    ∀ t P p,
      In (mdc Γ p) [ mProp ; mGhost ] →
      In (mdc Γ t) [ mType ; mKind ] →
      Γ ⊢ reveal (erase t) P p ≡ app p t

| revealP_erase :
    ∀ t p,
      mdc Γ p = mKind →
      mdc Γ t = mType →
      Γ ⊢ revealP (erase t) p ≡ app p t

(* Congruence rules *)

(* A rule to quotient away all levels of Prop, making it impredicative *)
| cong_Prop :
    ∀ i j,
      Γ ⊢ Sort mProp i ≡ Sort mProp j

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

(*** Typing rules for GRTT, the version with reflection

  We reuse syntax and scoping from GTT, we simply remove the typing rule for
  casts instead of coming up with a new syntax that does not feature them.
  We conjecture it would work as well.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode.
From GhostTT Require Export Univ TermNotations.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Reserved Notation "Γ ⊢ˣ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢ˣ  t  :  A").

Reserved Notation "Γ ⊢ˣ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢ˣ  u  ≡  v").

Inductive conversion (Γ : context) : term → term → Prop :=

(** Computation rules **)

| rconv_beta :
    ∀ m mx A B t u,
      cscoping Γ A mKind →
      scoping (mx :: sc Γ) B mKind →
      scoping (mx :: sc Γ) t m →
      cscoping Γ u mx →
      Γ ⊢ˣ app (lam mx A B t) u ≡ t <[ u .. ]

| reveal_hide :
    ∀ mp t P p,
      cscoping Γ t mType →
      cscoping Γ P mKind →
      cscoping Γ p mp →
      In mp [ mProp ; mGhost ] →
      Γ ⊢ˣ reveal (hide t) P p ≡ app p t

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| cong_Prop :
    ∀ i j,
      Γ ⊢ˣ Sort mProp i ≡ Sort mProp j

| cong_Pi :
    ∀ i i' j j' m mx A A' B B',
      Γ ⊢ˣ A ≡ A' →
      Γ ,, (mx, A) ⊢ˣ B ≡ B' →
      ueq mx i i' →
      ueq m j j' →
      Γ ⊢ˣ Pi i j m mx A B ≡ Pi i' j' m mx A' B'

| cong_lam :
    ∀ mx A A' B B' t t',
      Γ ⊢ˣ A ≡ A' →
      Γ ,, (mx, A) ⊢ˣ B ≡ B' →
      Γ ,, (mx, A) ⊢ˣ t ≡ t' →
      Γ ⊢ˣ lam mx A B t ≡ lam mx A' B' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ˣ u ≡ u' →
      Γ ⊢ˣ v ≡ v' →
      Γ ⊢ˣ app u v ≡ app u' v'

| cong_Erased :
    ∀ A A',
      Γ ⊢ˣ A ≡ A' →
      Γ ⊢ˣ Erased A ≡ Erased A'

| cong_hide :
    ∀ u u',
      Γ ⊢ˣ u ≡ u' →
      Γ ⊢ˣ hide u ≡ hide u'

| cong_reveal :
    ∀ t t' P P' p p',
      Γ ⊢ˣ t ≡ t' →
      Γ ⊢ˣ P ≡ P' →
      Γ ⊢ˣ p ≡ p' →
      Γ ⊢ˣ reveal t P p ≡ reveal t' P' p'

| cong_Reveal :
    ∀ t t' p p',
      Γ ⊢ˣ t ≡ t' →
      Γ ⊢ˣ p ≡ p' →
      Γ ⊢ˣ Reveal t p ≡ Reveal t' p'

| cong_gheq :
    ∀ A A' u u' v v',
      Γ ⊢ˣ A ≡ A' →
      Γ ⊢ˣ u ≡ u' →
      Γ ⊢ˣ v ≡ v' →
      Γ ⊢ˣ gheq A u v ≡ gheq A' u' v'

(* No need for it thanks to proof irrelevance *)
(* | cong_ghrefl :
    ∀ A A' u u',
      Γ ⊢ˣ A ≡ A' →
      Γ ⊢ˣ u ≡ u' →
      Γ ⊢ˣ ghrefl A u ≡ ghrefl A' u' *)

(* Maybe not needed? *)
| cong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ˣ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ˣ p ≡ p' →
      Γ ⊢ˣ bot_elim m A p ≡ bot_elim m A' p'

(** Structural rules **)

| rconv_refl :
    ∀ u,
      Γ ⊢ˣ u ≡ u

| rconv_sym :
    ∀ u v,
      Γ ⊢ˣ u ≡ v →
      Γ ⊢ˣ v ≡ u

| rconv_trans :
    ∀ u v w,
      Γ ⊢ˣ u ≡ v →
      Γ ⊢ˣ v ≡ w →
      Γ ⊢ˣ u ≡ w

(** Proof irrelevance **)

| rconv_irr :
    ∀ p q,
      cscoping Γ p mProp →
      cscoping Γ q mProp →
      Γ ⊢ˣ p ≡ q

where "Γ ⊢ˣ u ≡ v" := (conversion Γ u v).

Inductive typing (Γ : context) : term → term → Prop :=

| rtype_var :
    ∀ x m A,
      nth_error Γ x = Some (m, A) →
      Γ ⊢ˣ var x : (plus (S x)) ⋅ A

| rtype_sort :
    ∀ m i,
      Γ ⊢ˣ Sort m i : Sort mKind (usup m i)

| rtype_pi :
    ∀ i j mx m A B,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      Γ ⊢ˣ A : Sort mx i →
      Γ ,, (mx, A) ⊢ˣ B : Sort m j →
      Γ ⊢ˣ Pi i j m mx A B : Sort m (umax mx m i j)

| rtype_lam :
    ∀ mx m i j A B t,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping (Γ ,, (mx, A)) t m →
      Γ ⊢ˣ A : Sort mx i →
      Γ ,, (mx, A) ⊢ˣ B : Sort m j →
      Γ ,, (mx, A) ⊢ˣ t : B →
      Γ ⊢ˣ lam mx A B t : Pi i j m mx A B

| rtype_app :
    ∀ i j mx m A B t u,
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping Γ t m →
      cscoping Γ u mx →
      cscoping Γ A mKind →
      Γ ⊢ˣ t : Pi i j m mx A B →
      Γ ⊢ˣ u : A →
      Γ ⊢ˣ A : Sort mx i →
      Γ ,, (mx, A) ⊢ˣ B : Sort m j →
      Γ ⊢ˣ app t u : B <[ u .. ]

| rtype_erased :
    ∀ i A,
      cscoping Γ A mKind →
      Γ ⊢ˣ A : Sort mType i →
      Γ ⊢ˣ Erased A : Sort mGhost i

| rtype_hide :
    ∀ i A t,
      cscoping Γ A mKind →
      cscoping Γ t mType →
      Γ ⊢ˣ A : Sort mType i →
      Γ ⊢ˣ t : A →
      Γ ⊢ˣ hide t : Erased A

| rtype_reveal :
    ∀ i m A t P p,
      cscoping Γ p m →
      cscoping Γ t mGhost →
      cscoping Γ P mKind →
      cscoping Γ A mKind →
      In m [ mProp ; mGhost ] →
      Γ ⊢ˣ t : Erased A →
      Γ ⊢ˣ P : Erased A ⇒[ i | S i / mGhost | mKind ] Sort m i →
      Γ ⊢ˣ p : Pi i (S i) m mType A (app (S ⋅ P) (hide (var 0))) →
      Γ ⊢ˣ A : Sort mType i →
      Γ ⊢ˣ reveal t P p : app P t

| rtype_Reveal :
    ∀ i A t p,
      cscoping Γ t mGhost →
      cscoping Γ p mKind →
      Γ ⊢ˣ t : Erased A →
      Γ ⊢ˣ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ˣ A : Sort mType i →
      cscoping Γ A mKind →
      Γ ⊢ˣ Reveal t p : Sort mProp 0

| rtype_toRev :
    ∀ i A t p u,
      cscoping Γ t mType →
      cscoping Γ p mKind →
      cscoping Γ u mProp →
      Γ ⊢ˣ t : A →
      Γ ⊢ˣ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ˣ u : app p t →
      Γ ⊢ˣ toRev t p u : Reveal (hide t) p

| rtype_fromRev :
    ∀ i A t p u,
      cscoping Γ t mType →
      cscoping Γ p mKind →
      cscoping Γ u mProp →
      Γ ⊢ˣ t : A →
      Γ ⊢ˣ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ˣ u : Reveal (hide t) p →
      Γ ⊢ˣ fromRev t p u : app p t

| rtype_gheq :
    ∀ i A u v,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      Γ ⊢ˣ A : Sort mGhost i →
      Γ ⊢ˣ u : A →
      Γ ⊢ˣ v : A →
      Γ ⊢ˣ gheq A u v : Sort mProp 0

| rtype_ghrefl :
    ∀ i A u,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      Γ ⊢ˣ A : Sort mGhost i →
      Γ ⊢ˣ u : A →
      Γ ⊢ˣ ghrefl A u : gheq A u u

| rtype_bot :
    Γ ⊢ˣ bot : Sort mProp 0

| rtype_bot_elim :
    ∀ i m A p,
      cscoping Γ A mKind →
      cscoping Γ p mProp →
      Γ ⊢ˣ A : Sort m i →
      Γ ⊢ˣ p : bot →
      Γ ⊢ˣ bot_elim m A p : A

| rtype_conv :
    ∀ i m A B t,
      cscoping Γ A mKind →
      cscoping Γ B mKind →
      cscoping Γ t m →
      Γ ⊢ˣ t : A →
      Γ ⊢ˣ A ≡ B →
      Γ ⊢ˣ B : Sort m i →
      Γ ⊢ˣ t : B

| reflection :
    ∀ i m A u v e P t,
      cscoping Γ A mKind →
      cscoping Γ P mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      cscoping Γ t m →
      cscoping Γ e mProp →
      m ≠ mKind →
      Γ ⊢ˣ A : Sort mGhost i →
      Γ ⊢ˣ u : A →
      Γ ⊢ˣ v : A →
      Γ ⊢ˣ e : gheq A u v →
      Γ ⊢ˣ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i →
      Γ ⊢ˣ t : app P u →
      Γ ⊢ˣ t : app P v

where "Γ ⊢ˣ t : A" := (typing Γ t A).

(** Context formation **)

Inductive rwf : context → Prop :=
| rwf_nil : rwf nil
| rwf_cons :
    ∀ Γ m i A,
      rwf Γ →
      cscoping Γ A mKind →
      Γ ⊢ˣ A : Sort m i →
      rwf (Γ ,, (m, A)).

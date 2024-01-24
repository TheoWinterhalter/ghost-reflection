From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Definition mode_eqb (m m' : mode) : bool :=
  match m, m' with
  | mProp, mProp
  | mGhost, mGhost
  | mType, mType
  | mKind, mKind => true
  | _,_ => false
  end.

Definition isProp m := mode_eqb m mProp.
Definition isGhost m := mode_eqb m mGhost.

Definition mode_inb := inb mode_eqb.

Notation relm m :=
  (mode_inb m [ mType ; mKind ]).

Notation "A ⇒[ i | j / mx | m ] B" :=
  (Pi i j m mx A (shift ⋅ B))
  (at level 20, i, j, mx, m at next level, right associativity).

Notation top := (bot ⇒[ 0 | 0 / mProp | mProp ] bot).

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢  t  :  A").

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Inductive conversion (Γ : context) : term → term → Prop :=

(** Computation rules **)

| conv_beta :
    ∀ m mx A B t u,
      cscoping Γ A mKind →
      scoping (mx :: sc Γ) B mKind →
      scoping (mx :: sc Γ) t m →
      cscoping Γ u mx →
      Γ ⊢ app (lam mx A B t) u ≡ t <[ u .. ]

| reveal_hide :
    ∀ mp t P p,
      cscoping Γ t mType →
      cscoping Γ P mKind →
      cscoping Γ p mp →
      In mp [ mProp ; mGhost ] →
      Γ ⊢ reveal (hide t) P p ≡ app p t

| revealP_hide :
    ∀ t p,
      cscoping Γ p mKind →
      cscoping Γ t mType →
      Γ ⊢ revealP (hide t) p ≡ top ⇒[ 0 | 0 / mProp | mProp ] app p t

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| cong_Prop :
    ∀ i j,
      Γ ⊢ Sort mProp i ≡ Sort mProp j

(** We use something non-standard here:
  Since the levels are stuck in the syntax, we allow them to be modulo
  conversion somehow by referring to conversion of universes.
  This lets us account for our impredicativity rule above.
**)
| cong_Pi :
    ∀ i i' j j' m mx A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      Γ ⊢ Sort mx i ≡ Sort mx i' →
      Γ ,, (mx, A) ⊢ Sort m j ≡ Sort m j' →
      Γ ⊢ Pi i j m mx A B ≡ Pi i' j' m mx A' B'

| cong_lam :
    ∀ mx A A' B B' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      Γ ,, (mx, A) ⊢ t ≡ t' →
      Γ ⊢ lam mx A B t ≡ lam mx A' B' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

| cong_Erased :
    ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ Erased A ≡ Erased A'

| cong_hide :
    ∀ u u',
      Γ ⊢ u ≡ u' →
      Γ ⊢ hide u ≡ hide u'

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

(* Maybe not needed? *)
| cong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ p ≡ p' →
      Γ ⊢ bot_elim m A p ≡ bot_elim m A' p'

(** Structural rules **)

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

(** Proof irrelevance **)

| conv_irr :
    ∀ p q,
      cscoping Γ p mProp →
      cscoping Γ q mProp →
      Γ ⊢ p ≡ q

where "Γ ⊢ u ≡ v" := (conversion Γ u v).

(** Successor of a universe **)
Definition usup m i :=
  if isProp m then 0 else S i.

(** Maximum of a universe **)
Definition umax m i j :=
  if isProp m then 0 else max i j.

Inductive typing (Γ : context) : term → term → Prop :=

| type_var :
    ∀ x m A,
      nth_error Γ x = Some (m, A) →
      Γ ⊢ var x : (plus (S x)) ⋅ A

| type_sort :
    ∀ m i,
      Γ ⊢ Sort m i : Sort mKind (usup m i)

| type_pi :
    ∀ i j mx m A B,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ Pi i j m mx A B : Sort m (umax m i j)

| type_lam :
    ∀ mx m i j A B t,
      cscoping Γ A mKind →
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping (Γ ,, (mx, A)) t m →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ,, (mx, A) ⊢ t : B →
      Γ ⊢ lam mx A B t : Pi i j m mx A B

| type_app :
    ∀ i j mx m A B t u,
      cscoping (Γ ,, (mx, A)) B mKind →
      cscoping Γ t m →
      cscoping Γ u mx →
      cscoping Γ A mKind →
      Γ ⊢ t : Pi i j m mx A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ app t u : B <[ u .. ]

| type_erased :
    ∀ i A,
      cscoping Γ A mKind →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ Erased A : Sort mGhost i

| type_hide :
    ∀ i A t,
      cscoping Γ A mKind →
      cscoping Γ t mType →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ t : A →
      Γ ⊢ hide t : Erased A

| type_reveal :
    ∀ i m A t P p,
      cscoping Γ p m →
      cscoping Γ t mGhost →
      cscoping Γ P mKind →
      cscoping Γ A mKind →
      In m [ mProp ; mGhost ] →
      Γ ⊢ t : Erased A →
      Γ ⊢ P : Erased A ⇒[ i | S i / mGhost | mKind ] Sort m i →
      Γ ⊢ p : Pi i (S i) m mType A (app (S ⋅ P) (hide (var 0))) →
      Γ ⊢ A : Sort mType i →
      Γ ⊢ reveal t P p : app P t

| type_revealP :
    ∀ i A t p,
      cscoping Γ t mGhost →
      cscoping Γ p mKind →
      Γ ⊢ t : Erased A →
      Γ ⊢ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ revealP t p : Sort mProp 0

| type_gheq :
    ∀ i A u v,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ gheq A u v : Sort mProp 0

| type_ghrefl :
    ∀ i A u,
      cscoping Γ A mKind →
      cscoping Γ u mGhost →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ ghrefl A u : gheq A u u

| type_ghcast :
    ∀ i m A u v e P t,
      cscoping Γ A mKind →
      cscoping Γ P mKind →
      cscoping Γ u mGhost →
      cscoping Γ v mGhost →
      cscoping Γ t m →
      cscoping Γ e mProp →
      m ≠ mKind →
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ e : gheq A u v →
      Γ ⊢ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i →
      Γ ⊢ t : app P u →
      Γ ⊢ ghcast e P t : app P v

| type_bot :
    Γ ⊢ bot : Sort mProp 0

| type_bot_elim :
    ∀ i m A p,
      cscoping Γ A mKind →
      cscoping Γ p mProp →
      Γ ⊢ A : Sort m i →
      Γ ⊢ p : bot →
      Γ ⊢ bot_elim m A p : A

| type_conv :
    ∀ i m A B t,
      cscoping Γ B mKind →
      cscoping Γ t m →
      Γ ⊢ t : A →
      Γ ⊢ ε|A| ≡ ε|B| →
      Γ ⊢ B : Sort m i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A).

(** Context formation **)

Inductive wf : context → Prop :=
| wf_nil : wf nil
| wf_cons :
    ∀ Γ m i A,
      wf Γ →
      Γ ⊢ A : Sort m i →
      wf (Γ ,, (m, A)).

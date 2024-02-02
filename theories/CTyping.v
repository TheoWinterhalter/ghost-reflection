From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Notation "A ⇒[ mx ] B" :=
  (cPi mx A (shift ⋅ B))
  (at level 20, mx at next level, right associativity).

Reserved Notation "Γ ⊢ᶜ t : A"
  (at level 80, t, A at next level, format "Γ  ⊢ᶜ  t  :  A").

Reserved Notation "Γ ⊢ᶜ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢ᶜ  u  ≡  v").

Inductive conversion (Γ : ccontext) : cterm → cterm → Prop :=

(** Computation rules **)

| cconv_beta :
    ∀ mx A t u,
      Γ ⊢ᶜ capp (clam mx A t) u ≡ t <[ u .. ]

| cconv_El_val :
    ∀ A a,
      Γ ⊢ᶜ cEl (ctyval A a) ≡ A

| cconv_Err_val :
    ∀ A a,
      Γ ⊢ᶜ cErr (ctyval A a) ≡ a

| cconv_El_err :
    Γ ⊢ᶜ cEl ctyerr ≡ cunit

| cconv_Err_err :
    Γ ⊢ᶜ cErr ctyerr ≡ ctt

| cconv_J_refl :
    ∀ A u P t,
      Γ ⊢ᶜ tJ (trefl A u) P t ≡ t

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| ccong_Prop :
    ∀ i j,
      Γ ⊢ᶜ cSort cProp i ≡ cSort cProp j

| ccong_Pi :
    ∀ mx A A' B B',
      Γ ⊢ᶜ A ≡ A' →
      Some (mx, A) :: Γ ⊢ᶜ B ≡ B' →
      Γ ⊢ᶜ cPi mx A B ≡ cPi mx A' B'

| ccong_clam :
    ∀ mx A A' t t',
      Γ ⊢ᶜ A ≡ A' →
      Some (mx, A) :: Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ clam mx A t ≡ clam mx A' t'

| ccong_app :
    ∀ u u' v v',
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ capp u v ≡ capp u' v'

(* Maybe not needed? *)
| ccong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ᶜ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ᶜ p ≡ p' →
      Γ ⊢ᶜ cbot_elim m A p ≡ cbot_elim m A' p'

| ccong_tyval :
    ∀ A A' a a',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ ctyval A a ≡ ctyval A' a'

| ccong_El :
    ∀ T T',
      Γ ⊢ᶜ T ≡ T' →
      Γ ⊢ᶜ cEl T ≡ cEl T'

| ccong_Err :
    ∀ T T',
      Γ ⊢ᶜ T ≡ T' →
      Γ ⊢ᶜ cErr T ≡ cErr T'

| ccong_squash :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ squash A ≡ squash A'

| ccong_teq :
    ∀ A A' u u' v v',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ teq A u v ≡ teq A' u' v'

| ccong_trefl :
    ∀ A A' u u',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ trefl A u ≡ trefl A' u'

| ccong_tJ :
    ∀ e e' P P' t t',
      Γ ⊢ᶜ e ≡ e' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ tJ e P t ≡ tJ e' P' t'

(** Structural rules **)

| cconv_refl :
    ∀ u,
      Γ ⊢ᶜ u ≡ u

| cconv_sym :
    ∀ u v,
      Γ ⊢ᶜ u ≡ v →
      Γ ⊢ᶜ v ≡ u

| cconv_trans :
    ∀ u v w,
      Γ ⊢ᶜ u ≡ v →
      Γ ⊢ᶜ v ≡ w →
      Γ ⊢ᶜ u ≡ w

(** Proof irrelevance **)

| cconv_irr :
    ∀ p q,
      ccxscoping Γ p cProp →
      ccxscoping Γ q cProp →
      Γ ⊢ᶜ p ≡ q

where "Γ ⊢ᶜ u ≡ v" := (conversion Γ u v).

Inductive ctyping (Γ : ccontext) : cterm → cterm → Prop :=

| ctype_var :
    ∀ x m A,
      nth_error Γ x = Some (Some (m, A)) →
      Γ ⊢ᶜ cvar x : (plus (S x)) ⋅ A

| ctype_sort :
    ∀ m i,
      Γ ⊢ᶜ cSort m i : cSort cType (S i)

| ctype_pi :
    ∀ i j m mx A B,
      Γ ⊢ᶜ A : cSort mx i →
      Some (mx, A) :: Γ ⊢ᶜ B : cSort m j →
      Γ ⊢ᶜ cPi mx A B : cSort m (max i j)

| ctype_lam :
    ∀ mx m i j A B t,
      Γ ⊢ᶜ A : cSort mx i →
      Some (mx, A) :: Γ ⊢ᶜ t : B →
      Some (mx, A) :: Γ ⊢ᶜ B : cSort m j →
      Γ ⊢ᶜ clam mx A t : cPi mx A B

| ctype_app :
    ∀ mx A B t u,
      Γ ⊢ᶜ t : cPi mx A B →
      Γ ⊢ᶜ u : A →
      Γ ⊢ᶜ capp t u : B <[ u .. ]

| ctype_unit :
    Γ ⊢ᶜ cunit : cSort cType 0

| ctype_tt :
    Γ ⊢ᶜ ctt : cunit

| ctype_top :
    Γ ⊢ᶜ ctop : cSort cProp 0

| ctype_star :
    Γ ⊢ᶜ cstar : ctop

| ctype_bot :
    Γ ⊢ᶜ cbot : cSort cProp 0

| ctype_bot_elim :
    ∀ i m A p,
      Γ ⊢ᶜ A : cSort m i →
      Γ ⊢ᶜ p : cbot →
      Γ ⊢ᶜ cbot_elim m A p : A

| ctype_ty :
    ∀ i,
      Γ ⊢ᶜ cty i : cSort cType (S i)

| ctype_tyval :
    ∀ i A a,
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ a : A →
      Γ ⊢ᶜ ctyval A a : cty i

| ctype_tyerr :
    ∀ i,
      Γ ⊢ᶜ ctyerr : cty i

| ctype_El :
    ∀ i T,
      Γ ⊢ᶜ T : cty i →
      Γ ⊢ᶜ cEl T : cSort cType i

| ctype_Err :
    ∀ i T,
      Γ ⊢ᶜ T : cty i →
      Γ ⊢ᶜ cErr T : cEl T

| ctype_squash :
    ∀ i A,
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ squash A : cSort cProp 0

| ctype_sq :
    ∀ i A a,
      Γ ⊢ᶜ a : A →
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ sq a : squash A

| ctype_sq_elim :
    ∀ A e P t,
      Γ ⊢ᶜ e : squash A →
      Γ ⊢ᶜ P : squash A ⇒[ cProp ] cSort cProp 0 →
      Γ ⊢ᶜ t : cPi cType A (capp (S ⋅ P) (sq (cvar 0))) →
      Γ ⊢ᶜ sq_elim e P t : capp P e

| ctype_teq :
    ∀ i A u v,
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ u : A →
      Γ ⊢ᶜ v : A →
      Γ ⊢ᶜ teq A u v : cSort cType i

| type_trefl :
    ∀ i A u,
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ u : A →
      Γ ⊢ᶜ trefl A u : teq A u u

| ctype_tJ :
    ∀ m i A u v e P t,
      Γ ⊢ᶜ e : teq A u v →
      Γ ⊢ᶜ P : cPi cType A (cPi cType (teq (S ⋅ A) (S ⋅ u) (cvar 0)) (cSort m i)) →
      Γ ⊢ᶜ t : capp (capp P u) (trefl A u) →
      Γ ⊢ᶜ tJ e P t : capp (capp P v) e

| ctype_conv :
    ∀ i m A B t,
      Γ ⊢ᶜ t : A →
      Γ ⊢ᶜ A ≡ B →
      Γ ⊢ᶜ B : cSort m i →
      Γ ⊢ᶜ t : B

(** Cumulativity

  We assume a weak form of cumulativity in the target to make our lives easier.
  This does not propagate under products or anything, simply because we don't
  need it. Of course, Coq still remains a model of such a theory.

**)
| ctype_cumul :
    ∀ i j A,
      Γ ⊢ᶜ A : cSort cType i →
      i ≤ j →
      Γ ⊢ᶜ A : cSort cType j

where "Γ ⊢ᶜ t : A" := (ctyping Γ t A).

(** Context formation **)

Definition isType Γ A m :=
  ∃ i, Γ ⊢ᶜ A : cSort m i.

Inductive cwf : ccontext → Prop :=
| cwf_nil : cwf nil
| cwf_cons :
    ∀ Γ d,
      cwf Γ →
      whenSome (λ '(m, A), isType Γ A m) d →
      cwf (d :: Γ).

Create HintDb cc_conv discriminated.
Create HintDb cc_type discriminated.

Hint Resolve cconv_beta cconv_El_val cconv_Err_val cconv_El_err cconv_Err_err
  cconv_J_refl ccong_Prop ccong_Pi ccong_clam ccong_app ccong_bot_elim
  ccong_tyval ccong_El ccong_Err ccong_squash ccong_teq ccong_trefl ccong_tJ
: cc_conv.

Hint Resolve ctype_var ctype_sort ctype_pi ctype_lam ctype_app ctype_unit
  ctype_tt ctype_top ctype_star ctype_bot ctype_bot_elim ctype_ty ctype_tyval
  ctype_tyerr ctype_El ctype_Err
: cc_type.

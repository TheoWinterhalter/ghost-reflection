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
    ∀ mk A a,
      Γ ⊢ᶜ cEl (ctyval mk A a) ≡ A

| cconv_Err_val :
    ∀ mk A a,
      Γ ⊢ᶜ cErr (ctyval mk A a) ≡ a

| cconv_El_err :
    Γ ⊢ᶜ cEl ctyerr ≡ cunit

| cconv_Err_err :
    Γ ⊢ᶜ cErr ctyerr ≡ ctt

| cconv_J_refl :
    ∀ A u P t,
      Γ ⊢ᶜ tJ (trefl A u) P t ≡ t

| cconv_if_true :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m etrue P t f e ≡ t

| cconv_if_false :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m efalse P t f e ≡ f

| cconv_if_err :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m bool_err P t f e ≡ e

| cconv_pif_true :
    ∀ P t f,
      Γ ⊢ᶜ pif ptrue P t f ≡ t

| cconv_pif_false :
    ∀ P t f,
      Γ ⊢ᶜ pif pfalse P t f ≡ f

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
    ∀ mk A A' a a',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ ctyval mk A a ≡ ctyval mk A' a'

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

| ccong_eif :
    ∀ m b P t f e b' P' t' f' e',
      Γ ⊢ᶜ b ≡ b' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ f ≡ f' →
      Γ ⊢ᶜ e ≡ e' →
      Γ ⊢ᶜ eif m b P t f e ≡ eif m b' P' t' f' e'

| ccong_pif :
    ∀ bP P t f bP' P' t' f',
      Γ ⊢ᶜ bP ≡ bP' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ f ≡ f' →
      Γ ⊢ᶜ pif bP P t f ≡ pif bP' P' t' f'

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

Definition iscProp m :=
  match m with cProp => true | cType => false end.

(** Successor of a universe **)
Definition cusup m i :=
  if iscProp m then 0 else S i.

(** Maximum of a universe **)
Definition cumax mx m i j :=
  if iscProp m then 0
  else if iscProp mx then j
  else max i j.

Inductive ctyping (Γ : ccontext) : cterm → cterm → Prop :=

| ctype_var :
    ∀ x m A,
      nth_error Γ x = Some (Some (m, A)) →
      Γ ⊢ᶜ cvar x : (plus (S x)) ⋅ A

| ctype_sort :
    ∀ m i,
      Γ ⊢ᶜ cSort m i : cSort cType (cusup m i)

| ctype_pi :
    ∀ i j m mx A B,
      Γ ⊢ᶜ A : cSort mx i →
      Some (mx, A) :: Γ ⊢ᶜ B : cSort m j →
      Γ ⊢ᶜ cPi mx A B : cSort m (cumax mx m i j)

| ctype_lam :
    ∀ mx i A B t,
      Γ ⊢ᶜ A : cSort mx i →
      Some (mx, A) :: Γ ⊢ᶜ t : B →
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
    ∀ i mk A a,
      Γ ⊢ᶜ A : cSort cType i →
      Γ ⊢ᶜ a : A →
      Γ ⊢ᶜ ctyval mk A a : cty i

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

| ctype_trefl :
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

| ctype_ebool :
    Γ ⊢ᶜ ebool : cSort cType 0

| ctype_etrue :
    Γ ⊢ᶜ etrue : ebool

| ctype_efalse :
    Γ ⊢ᶜ efalse : ebool

| ctype_bool_err :
    Γ ⊢ᶜ bool_err : ebool

| ctype_eif :
    ∀ i m b P t f e,
      Γ ⊢ᶜ b : ebool →
      Γ ⊢ᶜ P : ebool ⇒[ cType ] cSort m i →
      Γ ⊢ᶜ t : capp P etrue →
      Γ ⊢ᶜ f : capp P efalse →
      Γ ⊢ᶜ e : capp P bool_err →
      Γ ⊢ᶜ eif m b P t f e : capp P b

| ctype_pbool :
    Γ ⊢ᶜ pbool : ebool ⇒[ cType ] cSort cProp 0

| ctype_ptrue :
    Γ ⊢ᶜ ptrue : capp pbool etrue

| ctype_pfalse :
    Γ ⊢ᶜ pfalse : capp pbool efalse

| ctype_pif :
    ∀ b bP P t f,
      Γ ⊢ᶜ b : ebool →
      Γ ⊢ᶜ bP : capp pbool b →
      Γ ⊢ᶜ P : cPi cType ebool (capp pbool (cvar 0) ⇒[ cProp ] cSort cProp 0) →
      Γ ⊢ᶜ t : capp (capp P etrue) ptrue →
      Γ ⊢ᶜ f : capp (capp P efalse) pfalse →
      Γ ⊢ᶜ pif bP P t f : capp (capp P b) bP

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
  cconv_if_true cconv_if_false cconv_if_err ccong_eif cconv_pif_true
  cconv_pif_false ccong_pif
  cconv_refl
: cc_conv.

Hint Resolve ctype_var ctype_sort ctype_pi ctype_lam ctype_app ctype_unit
  ctype_tt ctype_top ctype_star ctype_bot ctype_bot_elim ctype_ty ctype_tyval
  ctype_tyerr ctype_El ctype_Err ctype_squash ctype_sq ctype_sq_elim
  ctype_teq ctype_trefl ctype_tJ ctype_ebool ctype_etrue ctype_efalse
  ctype_bool_err ctype_eif ctype_pbool ctype_ptrue ctype_pfalse ctype_pif
: cc_type.

Ltac econv :=
  unshelve typeclasses eauto with cc_conv shelvedb ; shelve_unifiable.

Ltac etype :=
  unshelve typeclasses eauto with cc_scope cc_type shelvedb ; shelve_unifiable.

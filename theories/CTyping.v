From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Notation "A ⇒[ mx ] B" :=
  (cPi mx A (shift ⋅ B))
  (at level 20, mx at next level, right associativity).

(** n-ary application **)
Fixpoint capps t us :=
  match us with
  | u :: us => capps (capp t u) us
  | [] => t
  end.

(** Length of an evec **)

Definition elength A v :=
  evec_elim v (clam cType (cEl (evec A)) enat)
    (* vnil => *) ezero
    (* vcons => *) (clam cType (cEl A) (
      clam cType (cEl (evec (S ⋅ A))) (
        clam cType (cEl enat) (
          esucc (cvar 0)
        )
      )
    )).

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

| cconv_enat_elim_zero :
    ∀ P z s,
      Γ ⊢ᶜ enat_elim ezero P z s ≡ z

| cconv_enat_elim_succ :
    ∀ P z s n,
      Γ ⊢ᶜ enat_elim (esucc n) P z s ≡ capp (capp s n) (enat_elim n P z s)

| cconv_evec_elim_nil :
    ∀ A P z s,
      Γ ⊢ᶜ evec_elim (evnil A) P z s ≡ z

| cconv_evec_elim_cons :
    ∀ a v P z s,
      Γ ⊢ᶜ evec_elim (evcons a v) P z s ≡
      capp (capp (capp s a) v) (evec_elim v P z s)

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

| ccong_esucc :
    ∀ n n',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ esucc n ≡ esucc n'

| ccong_enat_elim :
    ∀ n P z s n' P' z' s',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ z ≡ z' →
      Γ ⊢ᶜ s ≡ s' →
      Γ ⊢ᶜ enat_elim n P z s ≡ enat_elim n' P' z' s'

(* Morally unnecessary because of proof irrelevance, but we would need scoping *)
| ccong_psucc :
    ∀ n n',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ psucc n ≡ psucc n'

(* Same *)
| ccong_pnat_elim :
    ∀ ne nP Pe PP ze zP se sP ne' nP' Pe' PP' ze' zP' se' sP',
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ ze ≡ ze' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ se ≡ se' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pnat_elim ne nP Pe PP ze zP se sP ≡ pnat_elim ne' nP' Pe' PP' ze' zP' se' sP'

(* Same *)
| ccong_pnat_elimP :
    ∀ ne nP Pe PP zP sP ne' nP' Pe' PP' zP' sP',
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pnat_elimP ne nP Pe PP zP sP ≡ pnat_elimP ne' nP' Pe' PP' zP' sP'

| ccong_evec :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ evec A ≡ evec A'

| ccong_evnil :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ evnil A ≡ evnil A'

| ccong_evcons :
    ∀ a v a' v',
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ evcons a v ≡ evcons a' v'

| ccong_evec_elim :
    ∀ v P z s v' P' z' s',
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ z ≡ z' →
      Γ ⊢ᶜ s ≡ s' →
      Γ ⊢ᶜ evec_elim v P z s ≡ evec_elim v' P' z' s'

(* Also unnecessary *)
| ccong_pvec :
    ∀ A AP n nP A' AP' n' nP',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ pvec A AP n nP ≡ pvec A' AP' n' nP'

(* Same *)
| ccong_pvnil :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ pvnil A ≡ pvnil A'

(* Same *)
| ccong_pvcons :
    ∀ a n v a' n' v',
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ pvcons a n v ≡ pvcons a' n' v'

(* Same *)
| ccong_pvec_elim :
    ∀ Ae AP ne nP ve vP Pe PP ze zP se sP Ae' AP' ne' ve' vP' nP' Pe' PP' ze' zP' se' sP',
      Γ ⊢ᶜ Ae ≡ Ae' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ ve ≡ ve' →
      Γ ⊢ᶜ vP ≡ vP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ ze ≡ ze' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ se ≡ se' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pvec_elim Ae AP ne nP ve vP Pe PP ze zP se sP ≡ pvec_elim Ae' AP' ne' nP' ve' vP' Pe' PP' ze' zP' se' sP'

(* Same *)
| ccong_pvec_elimP :
    ∀ Ae AP ne nP ve vP Pe PP zP sP Ae' AP' ne' nP' ve' vP' Pe' PP' zP' sP',
      Γ ⊢ᶜ Ae ≡ Ae' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ ve ≡ ve' →
      Γ ⊢ᶜ vP ≡ vP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pvec_elimP Ae AP ne nP ve vP Pe PP zP sP ≡ pvec_elimP Ae' AP' ne' nP' ve' vP' Pe' PP' zP' sP'

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

| ctype_enat :
    Γ ⊢ᶜ enat : cty 0

| ctype_ezero :
    Γ ⊢ᶜ ezero : cEl enat

| ctype_esucc :
    ∀ n,
      Γ ⊢ᶜ n : cEl enat →
      Γ ⊢ᶜ esucc n : cEl enat

| ctype_enat_elim :
    ∀ n P z s i,
      Γ ⊢ᶜ n : cEl enat →
      Γ ⊢ᶜ P : cPi cType (cEl enat) (cty i) →
      Γ ⊢ᶜ z : cEl (capp P ezero) →
      Γ ⊢ᶜ s :
      cPi cType (cEl enat) (
        cPi cType (cEl (capp (S ⋅ P) (cvar 0))) (
          cEl (capp (S ⋅ S ⋅ P) (esucc (cvar 1)))
        )
      ) →
      Γ ⊢ᶜ enat_elim n P z s : cEl (capp P n)

| ctype_pnat :
    Γ ⊢ᶜ pnat : cPi cType (cEl enat) (cSort cProp 0)

| ctype_pzero :
    Γ ⊢ᶜ pzero : capp pnat ezero

| ctype_psucc :
    ∀ n nP,
      Γ ⊢ᶜ nP : capp pnat n →
      Γ ⊢ᶜ psucc nP : capp pnat (esucc n)

| ctype_pnat_elim :
    ∀ i ne nP Pe PP ze zP se sP,
      Γ ⊢ᶜ ne : cEl enat →
      Γ ⊢ᶜ nP : capp pnat ne →
      Γ ⊢ᶜ Pe : cPi cType (cEl enat) (cty i) →
      Γ ⊢ᶜ PP : cPi cType (cEl enat) (
        cPi cProp (capp pnat (cvar 0)) (
          cPi cType (cEl (capp ((S >> S) ⋅ Pe) (cvar 1))) (
            cSort cProp 0
          )
        )
      ) →
      Γ ⊢ᶜ ze : cEl (capp Pe ezero) →
      Γ ⊢ᶜ zP : capp (capp (capp PP ezero) pzero) ze →
      Γ ⊢ᶜ se : cPi cType (cEl enat) (
        cPi cType (cEl (capp (S ⋅ Pe) (cvar 0))) (
          cEl (capp ((S >> S) ⋅ Pe) (esucc (cvar 1)))
        )
      ) →
      Γ ⊢ᶜ sP : cPi cType (cEl enat) (
        cPi cProp (capp pnat (cvar 0)) (
          cPi cType (cEl (capp ((S >> S) ⋅ Pe) (cvar 1))) (
            cPi cProp (capp (capp (capp ((S >> S >> S) ⋅ PP) (cvar 2)) (cvar 1)) (cvar 0)) (
              capp (capp (capp ((S >> S >> S >> S) ⋅ PP) (esucc (cvar 3))) (psucc (cvar 2))) (capp (capp ((S >> S >> S >> S) ⋅ se) (cvar 3)) (cvar 1))
            )
          )
        )
      ) →
      Γ ⊢ᶜ pnat_elim ne nP Pe PP ze zP se sP :
      capp (capp (capp PP ne) nP) (enat_elim ne Pe ze se)

| ctype_pnat_elimP :
    ∀ ne nP Pe PP zP sP,
      Γ ⊢ᶜ ne : cEl enat →
      Γ ⊢ᶜ nP : capp pnat ne →
      Γ ⊢ᶜ Pe : cPi cType (cEl enat) cunit → (* Could be removed *)
      Γ ⊢ᶜ PP : cPi cType (cEl enat) (cPi cProp (capp pnat (cvar 0)) (cSort cProp 0)) →
      Γ ⊢ᶜ zP : capp (capp PP ezero) pzero →
      Γ ⊢ᶜ sP : cPi cType (cEl enat) (
        cPi cProp (capp pnat (cvar 0)) (
          cPi cProp (capp (capp ((S >> S) ⋅ PP) (cvar 1)) (cvar 0)) (
            capp (capp ((S >> S >> S) ⋅ PP) (esucc (cvar 2))) (psucc (cvar 1))
          )
        )
      ) →
      Γ ⊢ᶜ pnat_elimP ne nP Pe PP zP sP : capp (capp PP ne) nP

| ctype_evec :
    ∀ A i,
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ evec A : cty i

| ctype_evnil :
    ∀ A i,
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ evnil A : cEl (evec A)

| ctype_evcons :
    ∀ i A a v,
      Γ ⊢ᶜ a : cEl A →
      Γ ⊢ᶜ v : cEl (evec A) →
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ evcons a v : cEl (evec A)

| ctype_evec_elim :
    ∀ v P z s A i j,
      Γ ⊢ᶜ v : cEl (evec A) →
      Γ ⊢ᶜ P : cPi cType (cEl (evec A)) (cty j) →
      Γ ⊢ᶜ z : cEl (capp P (evnil A)) →
      Γ ⊢ᶜ s : cPi cType (cEl A) (
        cPi cType (cEl (evec (S ⋅ A))) (
          cPi cType (cEl (capp ((S >> S) ⋅ P) (cvar 0))) (
            cEl (capp ((S >> S >> S) ⋅ P) (evcons (cvar 2) (cvar 1)))
          )
        )
      ) →
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ evec_elim v P z s : cEl (capp P v)

| ctype_pvec :
    ∀ i A AP n nP,
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ AP : cEl A ⇒[ cType ] cSort cProp 0 →
      Γ ⊢ᶜ n : cEl enat →
      Γ ⊢ᶜ nP : capp pnat n →
      Γ ⊢ᶜ pvec A AP n nP : cEl (evec A) ⇒[ cType ] cSort cProp 0

| ctype_pvnil :
    ∀ i A AP,
      Γ ⊢ᶜ AP : cEl A ⇒[ cType ] cSort cProp 0 →
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ pvnil AP : capp (pvec A AP ezero pzero) (evnil A)

| ctype_pvcons :
    ∀ i A AP a aP n nP v vP,
    Γ ⊢ᶜ aP : capp AP a →
    Γ ⊢ᶜ a : cEl A →
    Γ ⊢ᶜ nP : capp pnat n →
    Γ ⊢ᶜ n : cEl enat →
    Γ ⊢ᶜ vP : capp (pvec A AP n nP) v →
    Γ ⊢ᶜ v : cEl (evec A) →
    Γ ⊢ᶜ AP : cEl A ⇒[ cType ] cSort cProp 0 →
    Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ pvcons aP nP vP : capp (pvec A AP (esucc n) (psucc nP)) (evcons a v)

| ctype_pvec_elim :
    ∀ i j A AP n nP v vP P PP z zP s sP,
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ AP : cEl A ⇒[ cType ] cSort cProp 0 →
      Γ ⊢ᶜ n : cEl enat →
      Γ ⊢ᶜ nP : capp pnat n →
      Γ ⊢ᶜ v : cEl (evec A) →
      Γ ⊢ᶜ vP : capp (pvec A AP n nP) v →
      Γ ⊢ᶜ P : cPi cType (cEl (evec A)) (cty j) →
      Γ ⊢ᶜ PP : cPi cType (cEl enat) (
        cPi cProp (capp pnat (cvar 0)) (
          cPi cType (cEl (evec ((S >> S) ⋅ A))) (
            cPi cProp
              (capp (pvec ((S >> S >> S) ⋅ A) ((S >> S >> S) ⋅ AP) (cvar 2) (cvar 1)) (cvar 0))
              (cPi cType (cEl (capp ((S >> S >> S >> S) ⋅ P) (cvar 1))) (cSort cProp 0))
          )
        )
      ) →
      Γ ⊢ᶜ z : cEl (capp P (evnil A)) →
      Γ ⊢ᶜ zP : capps PP [ ezero ; pzero ; evnil A ; pvnil AP ; z ] →
      Γ ⊢ᶜ s : cPi cType (cEl A) (
        cPi cType (cEl (evec (S ⋅ A))) (
          cPi cType (cEl (capp ((S >> S) ⋅ P) (cvar 0))) (
            cEl (capp ((S >> S >> S) ⋅ P) (evcons (cvar 2) (cvar 1)))
          )
        )
      ) →
      Γ ⊢ᶜ sP : cPi cType (cEl A) (
        cPi cProp (capp (S ⋅ AP) (cvar 0)) (
          cPi cType (cEl enat) (
            cPi cProp (capp pnat (cvar 0)) (
              cPi cType (cEl (evec ((S >> S >> S >> S) ⋅ A))) (
                cPi cProp (capp (pvec ((S >> S >> S >> S >> S) ⋅ A) ((S >> S >> S >> S >> S) ⋅ AP) (cvar 2) (cvar 1)) (cvar 0)) (
                  cPi cType (cEl (capp ((S >> S >> S >> S >> S >> S) ⋅ P) (cvar 1))) (
                    cPi cProp (capps ((S >> S >> S >> S >> S >> S >> S) ⋅ PP) [ cvar 4 ; cvar 3 ; cvar 2 ; cvar 1 ; cvar 0 ]) (
                      capps ((S >> S >> S >> S >> S >> S >> S >> S) ⋅ PP) [
                        esucc (cvar 5) ;
                        psucc (cvar 4) ;
                        evcons (cvar 7) (cvar 3) ;
                        pvcons (cvar 6) (cvar 4) (cvar 2) ;
                        capps ((S >> S >> S >> S >> S >> S >> S >> S) ⋅ s) [
                          cvar 7 ;
                          cvar 3 ;
                          cvar 1
                        ]
                      ]
                    )
                  )
                )
              )
            )
          )
        )
      ) →
      Γ ⊢ᶜ pvec_elim A AP n nP v vP P PP z zP s sP :
      capps PP [ n ; nP ; v ; vP ; evec_elim v P z s ]

| ctype_pvec_elimG :
    ∀ i j A AP n nP v vP P PP z zP s sP,
      Γ ⊢ᶜ A : cty i →
      Γ ⊢ᶜ AP : cEl A ⇒[ cType ] cSort cProp 0 →
      Γ ⊢ᶜ n : cEl enat →
      Γ ⊢ᶜ nP : capp pnat n →
      Γ ⊢ᶜ v : cEl (evec A) →
      Γ ⊢ᶜ vP : capp (pvec A AP n nP) v →
      Γ ⊢ᶜ P : cPi cType (cEl (evec A)) (cty j) →
      Γ ⊢ᶜ PP : cPi cType (cEl enat) (
        cPi cProp (capp pnat (cvar 0)) (
          cPi cType (cEl (evec ((S >> S) ⋅ A))) (
            cPi cProp
              (capp (pvec ((S >> S >> S) ⋅ A) ((S >> S >> S) ⋅ AP) (cvar 2) (cvar 1)) (cvar 0))
              (cPi cType (cEl (capp ((S >> S >> S >> S) ⋅ P) (cvar 1))) (cSort cProp 0))
          )
        )
      ) →
      Γ ⊢ᶜ z : cEl (capp P (evnil A)) →
      Γ ⊢ᶜ zP : capps PP [ ezero ; pzero ; evnil A ; pvnil AP ; z ] →
      Γ ⊢ᶜ s : cPi cType (cEl A) (
        cPi cType (cEl enat) (
          cPi cType (cEl (evec ((S >> S) ⋅ A))) (
            cPi cType (cEl (capp ((S >> S >> S) ⋅ P) (cvar 0))) (
              cEl (capp ((S >> S >> S >> S) ⋅ P) (evcons (cvar 3) (cvar 1)))
            )
          )
        )
      ) →
      Γ ⊢ᶜ sP : cPi cType (cEl A) (
        cPi cProp (capp (S ⋅ AP) (cvar 0)) (
          cPi cType (cEl enat) (
            cPi cProp (capp pnat (cvar 0)) (
              cPi cType (cEl (evec ((S >> S >> S >> S) ⋅ A))) (
                cPi cProp (capp (pvec ((S >> S >> S >> S >> S) ⋅ A) ((S >> S >> S >> S >> S) ⋅ AP) (cvar 2) (cvar 1)) (cvar 0)) (
                  cPi cType (cEl (capp ((S >> S >> S >> S >> S >> S) ⋅ P) (cvar 1))) (
                    cPi cProp (capps ((S >> S >> S >> S >> S >> S >> S) ⋅ PP) [ cvar 4 ; cvar 3 ; cvar 2 ; cvar 1 ; cvar 0 ]) (
                      capps ((S >> S >> S >> S >> S >> S >> S >> S) ⋅ PP) [
                        esucc (cvar 5) ;
                        psucc (cvar 4) ;
                        evcons (cvar 7) (cvar 3) ;
                        pvcons (cvar 6) (cvar 4) (cvar 2) ;
                        capps ((S >> S >> S >> S >> S >> S >> S >> S) ⋅ s) [
                          cvar 7 ;
                          cvar 5 ;
                          cvar 3 ;
                          cvar 1
                        ]
                      ]
                    )
                  )
                )
              )
            )
          )
        )
      ) →
      Γ ⊢ᶜ pvec_elimG A AP n nP v vP P PP z zP s sP :
      capps PP [
        n ;
        nP ;
        v ;
        vP ;
        evec_elim v P z (
          clam cType (cEl A) (
            clam cType (cEl (evec (S ⋅ A))) (
              capps s [
                cvar 1 ;
                elength ((S >> S) ⋅ A) (cvar 0) ;
                cvar 0
              ]
            )
          )
        )
      ]

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
  cconv_pif_false ccong_pif cconv_enat_elim_zero cconv_enat_elim_succ
  ccong_esucc ccong_enat_elim ccong_psucc ccong_pnat_elim ccong_pnat_elimP
  cconv_evec_elim_nil cconv_evec_elim_cons ccong_evec ccong_evnil ccong_evcons
  ccong_evec_elim ccong_pvec ccong_pvnil ccong_pvcons ccong_pvec_elim
  ccong_pvec_elimP
  cconv_refl
: cc_conv.

Hint Resolve ctype_var ctype_sort ctype_pi ctype_lam ctype_app ctype_unit
  ctype_tt ctype_top ctype_star ctype_bot ctype_bot_elim ctype_ty ctype_tyval
  ctype_tyerr ctype_El ctype_Err ctype_squash ctype_sq ctype_sq_elim
  ctype_teq ctype_trefl ctype_tJ ctype_ebool ctype_etrue ctype_efalse
  ctype_bool_err ctype_eif ctype_pbool ctype_ptrue ctype_pfalse ctype_pif
  ctype_enat ctype_ezero ctype_esucc ctype_enat_elim ctype_pnat ctype_pzero
  ctype_psucc ctype_pnat_elim ctype_pnat_elimP ctype_evec ctype_evnil
  ctype_evcons ctype_evec_elim ctype_pvec ctype_pvnil ctype_pvcons
  ctype_pvec_elim ctype_pvec_elimG
: cc_type.

Ltac econv :=
  unshelve typeclasses eauto with cc_conv shelvedb ; shelve_unifiable.

Ltac etype :=
  unshelve typeclasses eauto with cc_scope cc_type shelvedb ; shelve_unifiable.

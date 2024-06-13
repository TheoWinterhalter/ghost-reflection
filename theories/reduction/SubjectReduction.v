From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Import ReductionProperties Injectivity.
From GhostTT.reduction Require Export Reduction ReductionAndTransitivity.

Import ListNotations.

Set Default Goal Selector "!".

Lemma scoping_type {Γ: context} {A t: term}:
  wf Γ → Γ ⊢ t:A → sc Γ⊢ A∷𝕂.
Proof.
  intros wfΓ type_t.
  specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i type_A]].
  specialize (validity Γ _ _ wfΓ type_A) as [scope_A [j type_scope]].
  ttinv type_scope type_scope.
  apply injectivity_Sort in type_scope.
  rewrite type_scope in *.
  assumption.
Qed.



Theorem subjet_reduction (Γ: context) (A t t': term):
  wf Γ → (sc Γ) ⊨ t ↣ t' → Γ ⊢ t:A → mdc Γ t ≠ ℙ → Γ⊢ t':A.
Proof.
  intros wfΓ red_t type_t not_Prop.
  remember (sc Γ) as Γ0 eqn:e0.
  induction red_t in Γ, Γ0, e0, wfΓ, A, red_t, type_t, not_Prop.
  all: gtype.
  - admit.
  - specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i type_A]].
    ttinv type_t type_t'.
    destruct_exists type_t'.
    repeat destruct type_t' as [H0 [ H1 [ H2 [H3 [H4 [H5 [H6[]]]]]]]].

    eapply type_app.
    * admit.
    * exact (scoping_type wfΓ type_t).
    * eapply red_scope.
      2: exact (proj1 (validity Γ _ _ wfΓ type_t)).
      subst; gred.
    * 


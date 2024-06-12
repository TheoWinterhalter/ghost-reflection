From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Import ReductionToCongruence.
From GhostTT.reduction Require Export Reduction ReductionAndTransitivity.

Import ListNotations.

Set Default Goal Selector "!".

Lemma glength_castrm {A n v: term} : 
  ε|glength A n v| = glength ε|A| ε|n| ε|v| .
Proof.
  cbn. unfold glength. repeat f_equal.
    + eauto using castrm_ren.
    + eapply eq_trans; eauto using castrm_ren.
      f_equal. eauto using castrm_ren.
Qed.

Lemma red_castrm {Γ : scope} {t t' : term} : 
  Γ ⊨t ↣ t' → Γ ⊨ t ε↣ t'.
Proof.
  intro red_t.
  induction red_t.
  1: erewrite castrm_subst; asimpl.
  all: gred.
  all: try (erewrite <- md_castrm; assumption).
  remember (glength _ _ _) as t eqn:e.
  apply (f_equal castrm) in e.
  rewrite glength_castrm in e.
  cbn; subst.
  rewrite e.
  gred.
  erewrite <- md_castrm.
  reflexivity.
Qed.

Theorem injectivity_lam {Γ : context} {m md_t md_t': mode} {A A' t t': term} :
  md_t ≠ ℙ →
  (sc Γ) ⊢ A∷𝕂 → m::(sc Γ)⊢t∷md_t →
  (sc Γ) ⊢ A'∷𝕂 → m::(sc Γ)⊢t'∷md_t →
  Γ ⊢ lam m A t ≡ lam m A' t' →
  Γ ⊢ A ε≡ A' ∧ (m,A)::Γ ⊢ t ε≡ t'.
Proof.
  intros not_Prop scope_A scope_t scope_A' scope_t' H.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. split; gconv.
    * apply reds_lam_inv in red2 as [* [* [e []]]].
      2: cbn; erewrite scoping_md; eauto.
      inversion e.
      split; apply conv_sym; subst.
      all: eapply reductions_to_conversion; cbn; eauto.
  - inversion red2; subst.
    * apply reds_lam_inv in red1 as [* [* [e []]]].
      2: cbn; erewrite scoping_md; eauto.
      inversion e.
      split; eapply reductions_to_conversion; cbn; eauto.
    * apply reds_lam_inv in red1 as [* [* [e [ ]]]].
      2: cbn; erewrite scoping_md; eauto.
      apply reds_lam_inv in red2 as [* [* [e'[ ]]]].
      2: cbn; erewrite scoping_md; eauto.
      subst; inversion e'; subst.
      split; eapply conv_trans.
      2,4: apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
Qed.

Theorem injectivity_Pi {Γ : context} {i i' j j': level} {m m' mx mx': mode} {A A' B B': term} :
  (sc Γ) ⊢ A∷𝕂 → mx::(sc Γ)⊢B∷𝕂 →
  (sc Γ) ⊢ A'∷𝕂 → mx'::(sc Γ)⊢B'∷𝕂 →
  Γ ⊢ Pi i j m mx A B ≡ Pi i' j' m' mx' A' B' →
  Γ ⊢ A ε≡ A' ∧ (mx,A)::Γ ⊢ B ε≡ B'.
Proof.
  intros scope_A scope_B scope_A' scope_B' H.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. split; gconv.
    * apply reds_Pi_inv in red2 as [* [* [* [* [e [ ]]]]]].
      inversion e.
      split; apply conv_sym; subst.
      all: eapply reductions_to_conversion; cbn; eauto.
  - inversion red2; subst.
    * apply reds_Pi_inv in red1 as [* [* [* [* [e [ ]]]]]].
      inversion e.
      eauto using reductions_to_conversion.
    * apply reds_Pi_inv in red1 as [* [* [* [* [e [ ]]]]]].
      apply reds_Pi_inv in red2 as [* [* [* [* [e'[ ]]]]]].
      subst; inversion e'; subst.
      split; eapply conv_trans. 
      2,4: apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
Qed.

Theorem injectivity_Sort {Γ : context} {i i': level} {m m' : mode} :
  Γ ⊢ Sort m i ≡ Sort m' i' → m' = m.
Proof.
  intros H.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. reflexivity.
    * apply reds_Sort_inv in red2 as [* e].
      inversion e. reflexivity.
  - inversion red2; subst.
    * apply reds_Sort_inv in red1 as [* e].
      inversion e. reflexivity.
    * apply reds_Sort_inv in red1 as [* e].
      apply reds_Sort_inv in red2 as [* e'].
      subst; inversion e'.
      reflexivity.
Qed.

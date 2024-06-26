From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.multisteps Require Import ReductionToCongruence.

Import ListNotations.

Set Default Goal Selector "!".

Lemma castrm_castrm {t : term} :
  ε| ε|t| | = ε|t| .
Proof.
  induction t.
  all: cbn; congruence.
Qed.

Lemma castrm_castrm_conv {Γ : context} {t t': term} :
  Γ ⊢ ε|t| ε≡ ε|t'| → Γ ⊢ t ε≡ t'.
Proof.
  intro conv.
  do 2 rewrite castrm_castrm in conv.
  exact conv.
Qed.

Lemma glength_castrm {A n v: term} : 
  ε|glength A n v| = glength ε|A| ε|n| ε|v| .
Proof.
  cbn. unfold glength. repeat f_equal.
    + eauto using castrm_ren.
    + eapply eq_trans; eauto using castrm_ren.
      f_equal. eauto using castrm_ren.
Qed.

Lemma red_castrm {Γ : scope} {t t' : term} : 
  Γ ⊨t ⇶ t' → Γ ⊨ t ε⇶ t'.
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
  Γ ⊢ lam m A t∷md_t →
  Γ ⊢ lam m A' t'∷md_t →
  Γ ⊢ lam m A t ≡ lam m A' t' →
  Γ ⊢ A ε≡ A' ∧ (m,A)::Γ ⊢ t ε≡ t'.
Proof.
  intros not_Prop scope_lam scope_lam' H.
  inversion scope_lam; inversion scope_lam'; subst.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. split; gconv.
    * apply reds_lam_inv in red2 as [* [* [e []]]].
      2: cbn; erewrite scoping_md; eauto.
      inversion e.
      split; apply conv_sym.
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
  Γ ⊢ Pi i j m mx A B ∷ 𝕂 →
  Γ ⊢ Pi i' j' m' mx' A' B'∷ 𝕂 →
  Γ ⊢ Pi i j m mx A B ≡ Pi i' j' m' mx' A' B' →
  m= m' ∧ mx = mx' ∧ Γ ⊢ A ε≡ A' ∧ (mx,A)::Γ ⊢ B ε≡ B'.
Proof.
  intros scope_Pi scope_Pi' H.
  inversion scope_Pi; inversion scope_Pi'; subst.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. repeat split; gconv.
    * apply reds_Pi_inv in red2 as [* [* [* [* [e [ ]]]]]].
      inversion e.
      repeat split; auto; apply conv_sym; subst.
      all: eapply reductions_to_conversion; cbn; eauto.
  - inversion red2; subst.
    * apply reds_Pi_inv in red1 as [* [* [* [* [e [ ]]]]]].
      inversion e.
      repeat split;
      eauto using reductions_to_conversion.
    * apply reds_Pi_inv in red1 as [* [* [* [* [e [ ]]]]]].
      apply reds_Pi_inv in red2 as [* [* [* [* [e'[ ]]]]]].
      subst; inversion e'; subst.
      repeat split; auto.
      all: eapply conv_trans. 
      2,4: apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
Qed.

(* true but uses conv_upto so needs models => create another file
Corollary injectivity_Pi_castrm {Γ : context} {i i' j j': level} {m m' mx mx': mode} {A A' B B': term} :
  sc Γ ⊢ Pi i j m mx A B ∷ 𝕂 →
  sc Γ ⊢ Pi i' j' m' mx' A' B'∷ 𝕂 →
  Γ ⊢ Pi i j m mx A B ε≡ Pi i' j' m' mx' A' B' →
  Γ ⊢ A ε≡ A' ∧ (mx,A)::Γ ⊢ B ε≡ B'.
Proof.
  intros scope_Pi scope_Pi' H.
  cbn in H.
  apply injectivity_Pi in H as [conv_A conv_B].
  - apply castrm_castrm_conv in conv_A.
    apply castrm_castrm_conv in conv_B.
    split.
    * assumption.
    * eapply conv_upto; eauto.
  - inversion scope_Pi.
    gconv; eauto using scoping_castrm.
  - inversion scope_Pi'.
    gconv; eauto using scoping_castrm.
   Qed. *)

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

Theorem injectivity_Erased {Γ : context} {t t': term} :
  Γ ⊢ Erased t ∷ 𝕂 → Γ ⊢ Erased t' ∷ 𝕂 → 
  Γ ⊢ Erased t ≡ Erased t' → Γ ⊢ t ε≡ t'.
Proof.
  intros scope_Erased scope_Erased' H.
  inversion scope_Erased; inversion scope_Erased'; subst.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. exact (conv_refl Γ ε|t|).
    * apply reds_Erased_inv in red2 as [* [e red_t']].
      inversion e. apply conv_sym.
      eapply reductions_to_conversion; eauto.
  - inversion red2; subst.
    * apply reds_Erased_inv in red1 as [* [e red_t']].
      inversion e.
      eapply reductions_to_conversion; eauto.
    * apply reds_Erased_inv in red2 as [* [e red_t']].
      apply reds_Erased_inv in red1 as [* [e' red_t'']].
      subst; inversion e; subst.
      eapply conv_trans.
      2: apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
Qed.


Theorem injectivity_vec {Γ : context} {A A' n n': term} :
  Γ ⊢ tvec A n ∷ 𝕂 → Γ ⊢ tvec A' n' ∷ 𝕂 → 
  Γ ⊢ tvec A n ≡ tvec A' n' → Γ ⊢ A ε≡ A' ∧ Γ ⊢ n ε≡ n'.
Proof.
  intros scope_vec scope_vec' H.
  inversion scope_vec; inversion scope_vec'; subst.
  apply conversion_to_reduction in H.
  destruct H as [w [red1 red2]].
  inversion red1.
  - inversion red2 as [e|]; subst.
    * inversion e. split; apply (conv_refl Γ).
    * apply reds_vec_inv in red2 as [A0 [ n0 [e [red_A' red_n']]]].
      inversion e. split; apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
  - inversion red2; subst.
    * apply reds_vec_inv in red1 as [A0 [ n0 [e [red_A' red_n']]]].
      inversion e.
      split; eapply reductions_to_conversion; eauto.
    * apply reds_vec_inv in red2 as [A0 [ n0 [e [red_A' red_n']]]].
      apply reds_vec_inv in red1 as [A1 [ n1 [e' [red_A'' red_n'']]]].
      subst; inversion e; subst.
      split; eapply conv_trans.
      2,4: apply conv_sym.
      all: eapply reductions_to_conversion; eauto.
Qed.

(* Definition of the main properties and and inversion lemmas of the multistep reduction*)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Import Notations.
From GhostTT.reduction.multisteps Require Export Reduction.

Import ListNotations.
Set Default Goal Selector "!".

Lemma red_md {Γ : scope} {t t' : term} :
  Γ ⊨ t ⇶ t' → md Γ t = md Γ t'.
Proof.
  intro red_t.
  induction red_t in red_t |- *.
  all: try solve [cbn; congruence].
  - cbn in *. eapply eq_trans; eauto.
    erewrite md_subst'; eauto.
    intro n. destruct n; eauto.
    cbn. subst. auto.
  - cbn. match goal with H: In _ _ |- _ =>
    destruct H as [ H0 | [ H0 |]] end.
    3: contradiction.
    all: rewrite <- H0.
    all: congruence.
  - match goal with H: md ?Γ ?p = _ |- md ?Γ (reveal _ _ ?p) = _ =>
    cbn; rewrite H; reflexivity end.
Qed.

Lemma red_scope {Γ : scope} {m : mode} {t t' : term} :
  Γ ⊨ t ⇶ t' → Γ ⊨ t∷m → Γ ⊨ t'∷m.
Proof.
  intros red_t scope_t.
  induction red_t in Γ, m, t, t', red_t, scope_t |- *.
  all: try solve [inversion scope_t; gscope].
  - inversion scope_t.
    match goal with H : _ ⊨ lam _ _ _∷_ |- _ =>
        inversion H; subst end.
    eapply scoping_subst; eauto.
    eapply sscoping_one.
    erewrite scoping_md; eauto.
  - inversion scope_t.
    match goal with H : _ ⊨ hide _∷_ |- _ =>
        inversion H; subst end.
    gscope.
  - inversion scope_t.
    match goal with H : _ ⊨ tsucc _∷_ |- _ =>
        inversion H; subst end.
    gscope.
  - inversion scope_t. 
    match goal with H : _ ⊨ tvcons _ _ _∷_ |- _ =>
        inversion H; subst end.
    gscope; eauto.
    * intro H; inversion H.
    * eapply scoping_ren; eauto using rscoping_S.
    * eapply scoping_ren; eauto using rscoping_S.
      eapply scoping_ren; eauto using rscoping_S.
    * right; left. reflexivity.
  - erewrite scoping_md in *; eauto.
    subst. apply scope_star.
Qed.


Lemma red_lam_inv {Γ : scope} {mx : mode} {A t u: term} :
  (Γ⊨lam mx A t⇶ u ) → md Γ (lam mx A t) ≠ ℙ →
  ( ∃ A' t', u = lam mx A' t' ∧ Γ⊨A⇶A' ∧ mx :: Γ⊨t⇶t').
Proof.
  intros red_lam not_Prop. 
  remember (lam mx A t) as lam_t eqn:e0.
  remember u as u0 eqn:e1.
  induction red_lam.
  all: try solve [inversion e0].
  - inversion e0.
    inversion e1; subst.
    eauto.
  - exists A, t; auto using red_refl.
  - subst. contradiction.
Qed.


Lemma red_Pi_inv {Γ : scope} {i j: level} {m mx : mode} {A B t: term} :
  Γ⊨Pi i j m mx A B⇶ t → 
  (∃ A' B' i' j', t = Pi i' j' m mx A' B' ∧ Γ ⊨ A ⇶ A' ∧ mx::Γ ⊨ B ⇶ B').
Proof.
  intro red_Pi. 
  inversion red_Pi; subst.
  - do 4 eexists; eauto.
  - do 4 eexists; eauto using red_refl.
  - do 4 eexists; eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕂 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_Sort_inv {Γ: scope} {i: level} {m: mode} {t: term} :
  Γ ⊨ Sort m i ⇶ t → ∃ i', t = Sort m i'.
Proof.
  intro red_sort.
  inversion red_sort.
  - eauto.
  - eauto.
  - cbn in *.
    match goal with | HC : 𝕂 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_Erased_inv {Γ: scope} {t0 t': term} :
  Γ ⊨ Erased t0 ⇶ t' → ∃ t0', t' = Erased t0' ∧ Γ ⊨ t0 ⇶ t0'.
Proof.
  intro red1.
  inversion red1.
  - eauto.
  - eexists; split; [reflexivity | gred].
  - cbn in *.
    match goal with | HC : 𝕂 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_vec_inv {Γ: scope} {A0 n0 t': term} :
  Γ ⊨ tvec A0 n0 ⇶ t' → ∃ A1 n1, t' = tvec A1 n1 ∧ Γ ⊨ A0 ⇶ A1 ∧ Γ ⊨ n0 ⇶ n1.
Proof.
  intro red1.
  inversion red1.
  - eauto.
  - repeat eexists; gred.
  - cbn in *.
    match goal with | HC : 𝕂 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_hide_inv {Γ : scope} {t0 t' : term} :
  Γ⊨hide t0 ⇶t' → ∃ t0', t' = hide t0' ∧ Γ ⊨ t0 ⇶ t0'.
Proof.
  intro red_hide.
  inversion red_hide; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝔾 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_succ_inv (Γ : scope) (n t' : term) (red_succ : Γ⊨tsucc n ⇶t' ) : ∃ n', t' = tsucc n' ∧ Γ ⊨ n ⇶ n'.
Proof.
  inversion red_succ; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_nil_inv (Γ : scope) (A t' : term) (red_nil : Γ ⊨ tvnil A ⇶ t' ) : 
  ∃ A', t' = tvnil A' ∧ Γ ⊨ A ⇶ A'.
Proof.
  inversion red_nil; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_cons_inv (Γ : scope) (a n v t' : term) (red_cons : Γ ⊨ tvcons a n v ⇶ t' ) : 
  ∃ a' n' v', t' = tvcons a' n' v' ∧ Γ ⊨ a ⇶ a' ∧ Γ ⊨ n ⇶ n' ∧ Γ ⊨ v ⇶ v'.
Proof.
  inversion red_cons; subst.
  - do 3 eexists; eauto.
  - do 3 eexists; eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_ren (Γ Δ : scope) (ρ: nat → nat) (t t': term) :
  (∀ n, nth (ρ n) Γ 𝕋 = nth n Δ 𝕋) →
  Δ ⊨ t ⇶ t' → Γ ⊨ ρ ⋅ t ⇶ ρ ⋅ t'.
Proof.
  intros Hscope red_t.
  induction red_t in Γ, Δ, ρ, Hscope, t, t', red_t |- *.
  all: try solve [gred; erewrite <- md_ren'; eauto].
  - assert (∀ (t' u' : term), ((up_ren ρ) ⋅ t') <[ (ρ ⋅ u')··] = ρ ⋅ t' <[ u'··]) as er.
    { intros. ssimpl. reflexivity. }
    rewrite <- er. 
    gred; eauto.
    + intro n; destruct n; cbn; auto.
    + erewrite <- md_ren'; eauto.
  - asimpl.
    repeat rewrite (rinstInst'_term ρ).
    rewrite glenght_red_subst.
    repeat rewrite <- (rinstInst'_term ρ).
    gred; erewrite <- md_ren'; eauto.
  - gred. intro n; destruct n; cbn; auto.
  - gred. intro n; destruct n; cbn; auto.
  - gred. intro n; destruct n; cbn; auto.
Qed.

Lemma up_subst_red (Γ : scope) (m : mode) (σ σ' : nat → term) : 
  (∀ n, Γ ⊨ σ n ⇶ σ' n) →
  (∀ n, m::Γ ⊨ up_term σ n ⇶ up_term σ' n).
Proof.
  intros Hyp n.
  destruct n.
  - ssimpl; gred.
  - asimpl; ssimpl. 
    eapply (red_ren); eauto.
    intro n0; destruct n0; cbn; auto.
Qed.

Lemma red_subst_r (Γ : scope) (t : term) (σ σ' : nat → term) :
  (∀ n, Γ ⊨ σ n ⇶ σ' n) → 
  Γ ⊨ t <[σ] ⇶ t <[σ'].
Proof.
  intro red_σ.
  induction t in Γ, σ, σ', red_σ |- *.
  all: gred.
  all: eauto using up_subst_red.
Qed.

Lemma red_subst (Γ Δ : scope) (t t' : term) (σ σ' : nat → term) :
  (∀ n, md Γ (σ n) = nth n Δ 𝕋) →
  (∀ n, Γ ⊨ σ n ⇶ σ' n) → 
  Δ ⊨ t ⇶ t' →
  Γ ⊨ t <[σ] ⇶ t' <[σ'].
Proof.
  intros Hscope red_σ red_t.
  remember Δ as Δ0 eqn:e.
  induction red_t in Γ, Δ, e, Hscope, σ, σ', red_σ, t, t', red_t |- *.
  all: try solve [ gred; erewrite <- md_subst'; eauto using up_subst_red].
  - assert (∀ t' u', (t' <[ up_term σ']) <[ (u' <[ σ'])··] = (t' <[ u'··]) <[ σ']) as er.
    { intros. ssimpl; apply ext_term. intro n; destruct n.
      all: asimpl; reflexivity. }
    rewrite <- er.
    gred; eauto using up_subst_red.
    * intro n; destruct n; auto. 
      rewrite md_up_term. cbn; auto.
    * erewrite <- md_subst'; eauto.
  - asimpl. erewrite glenght_red_subst.
    gred; erewrite <- md_subst'; eauto using scoping_subst.
  - gred; eauto using up_subst_red. 
    intro n; destruct n; [ |rewrite md_up_term]; auto.
  - gred; eauto using up_subst_red. 
    intro n; destruct n; [ |rewrite md_up_term]; auto.
  - gred; eauto using up_subst_red. 
    intro n; destruct n; [ |rewrite md_up_term]; auto.
  - apply red_subst_r. assumption.
Qed.

Ltac red_lam_inv_auto A' t' e red_A' red_t':=
  match goal with 
  | red_lam : ?Γ⊨lam ?m ?A ?t ⇶?u |- _ =>
      eapply red_lam_inv in red_lam; eauto;
      destruct red_lam as [A' [t' [e [red_A' red_t']]]];
      try subst u
  end.

Ltac red_Pi_inv_auto A' B' i' j' e red_A' red_B':=
  match goal with 
  | red_Pi : ?Γ⊨Pi ?i ?j ?m ?mx ?A ?B ⇶?u |- _ =>
      eapply red_Pi_inv in red_Pi; eauto;
      destruct red_lam as [A' [B' [i' [j' [e [red_A' red_B']]]]]];
      try subst u
  end.

Ltac red_hide_inv_auto t0' e:=
  match goal with 
  | red_hide : ?Γ⊨hide ?t0 ⇶?t' |- _ =>
      apply red_hide_inv in red_hide;
      destruct red_hide as [t0' [e red_hide]];
      try subst t'
  end.

Ltac red_succ_inv_auto n' e:=
  match goal with 
  | red_succ : ?Γ⊨tsucc ?t0 ⇶?t' |- _ =>
      apply red_succ_inv in red_succ;
      destruct red_succ as [n' [e red_succ]];
      try subst t'
  end.

Ltac red_nil_inv_auto A' e:=
  match goal with 
  | red_nil : ?Γ⊨tvnil ?A ⇶?t' |- _ =>
      apply red_nil_inv in red_nil;
      destruct red_nil as [A' [e red_nil]];
      try subst t'
  end.

Ltac red_conv_inv_auto a' n' v' e red_a' red_n' red_v':=
  match goal with 
  | red_cons : ?Γ⊨tvcons ?a ?n ?v ⇶?t' |- _ =>
      apply red_cons_inv in red_cons;
      destruct red_cons as [a' [n' [v' [e [red_a' [red_n' red_v']]]]]];
      try subst t'
  end.

Ltac red_basic_inv :=
  let e := fresh "e" in
  match goal with
  | H : ?Γ ⊨ tzero ⇶ ?t |- _ => 
      inversion H
  | H : ?Γ ⊨ ttrue ⇶ ?t |- _ => 
      inversion H
  | H : ?Γ ⊨ tfalse ⇶ ?t |- _ => 
      inversion H
  end; subst.


(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Export Reduction.

Import ListNotations.

Set Default Goal Selector "!".

Lemma md_ren' {Γ Δ :scope} {t: term} {ρ: nat → nat} (e : ∀ n, nth (ρ n) Γ 𝕋 = nth n Δ 𝕋) : 
  md Δ t = md Γ (ρ ⋅ t).
Proof.
  induction t in Γ, Δ, t, ρ, e|- *.
  all: cbn; eauto.
  - cbn. match goal with H: ∀ _ _, _ → _ |- _ =>
    eapply H; eauto end.
    intro n; destruct n; cbn; auto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
Qed.

Lemma md_up_term {Γ : scope} {m: mode} {σ : nat → term} {n : nat} :
  md (m::Γ) (up_term σ (S n)) = md Γ (σ n).
Proof.
  asimpl; ssimpl.
  unfold shift.
  symmetry.
  apply md_ren'.
  induction n; eauto.
Qed.

Lemma md_subst' {Γ Δ :scope} {t: term} {σ: nat → term} (e : ∀ n, md Γ (σ n) = nth n Δ 𝕋) : 
  md Δ t = md Γ (t<[σ]).
Proof.
  induction t in Γ, Δ, t, σ, e|- *.
  all: cbn; eauto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
    intro n; destruct n; eauto.
    erewrite md_up_term. auto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
Qed.

Lemma red_md : 
  ∀ Γ t t', Γ ⊨ t ↣ t' → md Γ t = md Γ t'.
Proof.
  intros Γ t t' red_t.
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

Lemma glenght_red_subst (A n v : term) (σ : nat → term) :
  (glength A n v)<[σ] = glength (A<[σ]) (n<[σ]) (v<[σ]).
Proof.
  change (tvec_elim 𝔾 (A <[ σ]) (n <[ σ]) (v <[ σ])
  (lam 𝔾 (Erased tnat) 
  (lam 𝕋 ((tvec (S ⋅ A) (var 0))<[up_term σ]) (Erased tnat))
  )
  (hide tzero)
  (lam 𝕋 (A<[σ])
  (lam 𝔾 (Erased tnat)
  (lam 𝕋 (tvec (S ⋅ S ⋅ A) (var 0) <[up_term (up_term σ)]) 
  (lam 𝔾 (Erased tnat) 
  (gS (var 0)) 
  <[(up_term (up_term (up_term σ)))])
  )
  )
  )
  = glength (A<[σ]) (n<[σ]) (v<[σ])).
  unfold glength.
  repeat f_equal.
  all: asimpl; reflexivity.
Qed.

Lemma red_lam_inv {Γ : scope} {mx md_t : mode} {A t u: term} :
  (Γ⊨lam mx A t↣ u ) → md Γ (lam mx A t) = md_t → (md_t ≠ ℙ) →
  ( ∃ A' t', u = lam mx A' t' ∧ Γ⊨A↣A' ∧ mx :: Γ⊨t↣t').
Proof.
  intros prf_red scope_t not_Prop. 
  remember (lam mx A t) as lam_t eqn:e0.
  remember u as u0 eqn:e1.
  induction prf_red.
  all: try solve [inversion e0].
  - inversion e0.
    inversion e1; subst.
    eauto.
  - exists A, t; auto using red_refl.
  - subst. contradiction.
Qed.

Lemma red_hide_inv (Γ : scope) (t0 t' : term) (red_hide : Γ⊨hide t0 ↣t' ) : ∃ t0', t' = hide t0' ∧ Γ ⊨ t0 ↣ t0'.
Proof.
  inversion red_hide; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝔾 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_succ_inv (Γ : scope) (n t' : term) (red_succ : Γ⊨tsucc n ↣t' ) : ∃ n', t' = tsucc n' ∧ Γ ⊨ n ↣ n'.
Proof.
  inversion red_succ; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_nil_inv (Γ : scope) (A t' : term) (red_nil : Γ ⊨ tvnil A ↣ t' ) : 
  ∃ A', t' = tvnil A' ∧ Γ ⊨ A ↣ A'.
Proof.
  inversion red_nil; subst.
  - eauto.
  - eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_cons_inv (Γ : scope) (a n v t' : term) (red_cons : Γ ⊨ tvcons a n v ↣ t' ) : 
  ∃ a' n' v', t' = tvcons a' n' v' ∧ Γ ⊨ a ↣ a' ∧ Γ ⊨ n ↣ n' ∧ Γ ⊨ v ↣ v'.
Proof.
  inversion red_cons; subst.
  - do 3 eexists; eauto.
  - do 3 eexists; eauto using red_refl.
  - cbn in *.
    match goal with | HC : 𝕋 = ℙ |- _ => inversion HC end.
Qed.

Lemma red_ren (Γ Δ : scope) (ρ: nat → nat) (t t': term) :
  (∀ n, nth (ρ n) Γ 𝕋 = nth n Δ 𝕋) →
  Δ ⊨ t ↣ t' → Γ ⊨ ρ ⋅ t ↣ ρ ⋅ t'.
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
  (∀ n, Γ ⊨ σ n ↣ σ' n) →
  (∀ n, m::Γ ⊨ up_term σ n ↣ up_term σ' n).
Proof.
  intros Hyp n.
  destruct n.
  - ssimpl; gred.
  - asimpl; ssimpl. 
    eapply (red_ren); eauto.
    intro n0; destruct n0; cbn; auto.
Qed.

Lemma red_subst_r (Γ : scope) (t : term) (σ σ' : nat → term) :
  (∀ n, Γ ⊨ σ n ↣ σ' n) → 
  Γ ⊨ t <[σ] ↣ t <[σ'].
Proof.
  intro red_σ.
  induction t in Γ, σ, σ', red_σ |- *.
  all: gred.
  all: eauto using up_subst_red.
Qed.

Lemma red_subst (Γ Δ : scope) (t t' : term) (σ σ' : nat → term) :
  (∀ n, md Γ (σ n) = nth n Δ 𝕋) →
  (∀ n, Γ ⊨ σ n ↣ σ' n) → 
  Δ ⊨ t ↣ t' →
  Γ ⊨ t <[σ] ↣ t' <[σ'].
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
  | red_lam : ?Γ⊨lam ?m ?A ?t ↣?u |- _ =>
      eapply red_lam_inv in red_lam; eauto;
      destruct red_lam as [A' [t' [e [red_A' red_t']]]];
      try subst u
  end.

Ltac red_hide_inv_auto t0' e:=
  match goal with 
  | red_hide : ?Γ⊨hide ?t0 ↣?t' |- _ =>
      apply red_hide_inv in red_hide;
      destruct red_hide as [t0' [e red_hide]];
      try subst t'
  end.

Ltac red_succ_inv_auto n' e:=
  match goal with 
  | red_succ : ?Γ⊨tsucc ?t0 ↣?t' |- _ =>
      apply red_succ_inv in red_succ;
      destruct red_succ as [n' [e red_succ]];
      try subst t'
  end.

Ltac red_nil_inv_auto A' e:=
  match goal with 
  | red_nil : ?Γ⊨tvnil ?A ↣?t' |- _ =>
      apply red_nil_inv in red_nil;
      destruct red_nil as [A' [e red_nil]];
      try subst t'
  end.

Ltac red_conv_inv_auto a' n' v' e red_a' red_n' red_v':=
  match goal with 
  | red_cons : ?Γ⊨tvcons ?a ?n ?v ↣?t' |- _ =>
      apply red_cons_inv in red_cons;
      destruct red_cons as [a' [n' [v' [e [red_a' [red_n' red_v']]]]]];
      try subst t'
  end.

Ltac red_basic_inv :=
  let e := fresh "e" in
  match goal with
  | H : ?Γ ⊨ tzero ↣ ?t |- _ => 
      inversion H
  | H : ?Γ ⊨ ttrue ↣ ?t |- _ => 
      inversion H
  | H : ?Γ ⊨ tfalse ↣ ?t |- _ => 
      inversion H
  end; subst.


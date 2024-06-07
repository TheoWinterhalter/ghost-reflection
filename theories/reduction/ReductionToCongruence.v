From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Export ReductionProperties ReductionConfluence.
From GhostTT.reduction Require Export Reduction ReductionAndTransitivity.

Import ListNotations.

Set Default Goal Selector "!".

Lemma conv_subst_r (Γ : context) (Δ : scope) (m : mode) (σ σ' : nat → term) (t : term) :
  sscoping (sc Γ) σ Δ →
  Δ ⊢ t∷m → (∀ n, Γ ⊢ σ n ≡ σ' n) → Γ ⊢ t <[ σ] ≡ t <[ σ'].
Proof.
  intros Hscope scope_t conv_σ.
  induction t in Γ, Δ, Hscope, m, scope_t, σ, σ', conv_σ |- *.
  all: inversion scope_t; subst.
  all: try solve [gconv].
  - asimpl; gconv; unfold ueq; eauto using sscoping_shift.
    admit. (*lemma 1*)
  - asimpl; gconv; eauto using sscoping_shift.
    admit. (*lemma 1*)
  - asimpl; gconv. eapply conv_irr.
    * gscope; eauto using scoping_subst.
    * gscope; eauto using scoping_subst.
      all:admit. (*lemma 2*)
  - asimpl; gconv. eapply conv_irr.
    * gscope; eauto using scoping_subst.
    * gscope; eauto using scoping_subst.
      all:admit. (*lemma 2*)
  - asimpl; gconv. eapply conv_irr.
    * gscope; eauto using scoping_subst.
    * gscope; eauto using scoping_subst.
      all:admit. (*lemma 2*)
  - admit. (*real issue to be discussed*)
Admitted.



Theorem reduction_to_conversion :
  ∀ Γ m t t', (sc Γ) ⊢ t∷m → (sc Γ) ⊨ t ↣ t' → Γ ⊢ t ≡ t'.
Proof. (*
  intros Γ m t t' scope_t red_t.
  remember (sc Γ) as Γ0 eqn:e.
  induction red_t in Γ, Γ0, e, m, scope_t, t', red_t |- *.
  all: try solve [inversion scope_t; gconv].
  - scope_sub_inv. eapply conv_trans.
    * eapply conv_beta; eauto.
    * eapply conv_trans. 
      1: eapply conv_subst_r; eauto using sscoping_one.
      2: eapply conv_subst; eauto.
      + intro n; destruct n; gconv; reflexivity.
      + Unshelve.
        2: exact ((mx, u')::Γ).
        cbn; eapply sscoping_one; eauto using red_md.
      + eauto.
  - scope_sub_inv.
    eapply conv_trans.
    * eapply reveal_hide; eauto.
    * gconv; auto.
  - inversion scope_t; subst. 
    eapply conv_trans; solve [gconv | eauto].
  - inversion scope_t; subst. 
    eapply conv_trans; solve [gconv | eauto].
  - inversion scope_t; subst.
    eapply conv_trans; solve [gconv | eauto].
  - inversion scope_t; subst.
    eapply conv_trans.
    * eapply conv_nat_elim_succ; auto.
    * gconv; auto.
  - inversion scope_t; subst.
    eapply conv_trans.
    * admit.
    * eauto.
  - inversion scope_t; subst.
    eapply conv_trans.
    * eapply conv_vec_elim_cons; auto.
    * gconv; auto.
      + eapply conv_ren; eauto using rtyping_S.
      + do 2 (eapply conv_ren; eauto using rtyping_S).
  - inversion scope_t; subst; gconv; auto.
      + destruct mx; unfold ueq; eauto.
      + destruct m0; unfold ueq; eauto.
  - inversion scope_t; subst; gconv; auto.
      + destruct mx; unfold ueq; eauto.
      + destruct m0; unfold ueq; eauto.
  - inversion scope_t; subst; gconv; auto.
  - subst; apply conv_irr; auto using scope_star.
  - subst; apply conv_irr; auto using scope_star.
  - case m in *; inversion scope_t; subst.
    apply conv_irr; auto using scope_star.
    gscope; eauto using red_md.
  - case m in *; inversion scope_t; subst.
    apply conv_irr; auto using scope_star.
    gscope; eauto using red_md.
  - case m in *; inversion scope_t; subst.
    apply conv_irr; auto using scope_star.
    gscope; eauto using red_md.
     - admit.*)
Admitted.


Local Ltac conversion_to_reduction_exists :=
  match goal with 
  | H : ∃ _, _ ∧ _ |- 
      ∃ w, ?Γ ⊨ ?c _ ↣* w ∧ ?Γ ⊨ ?c _ ↣* w => 
    let w := fresh "w" in
    destruct H as [ w [ ]];
    exists (c w)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _ |-
          ∃ w, ?Γ ⊨ ?c _ _ ↣* w ∧ ?Γ ⊨ ?c _ _↣* w => 
    let w0 := fresh "w0" in let w1 := fresh "w1" in
    destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
    exists (c w0 w1)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _ |-
          ∃ w, ?Γ ⊨ ?c _ _ _ ↣* w ∧ ?Γ ⊨ ?c _ _ _ ↣* w => 
    let w0 := fresh "w0" in let w1 := fresh "w1" in
    let w2 := fresh "w2" in
    destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
    destruct H2 as [ w2 [ ]];
    exists (c w0 w1 w2)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _, H3 : ∃ _, _ ∧ _ |-
          ∃ w, ?Γ ⊨ ?c _ _ _ _ ↣* w ∧ ?Γ ⊨ ?c _ _ _ _ ↣* w => 
    let w0 := fresh "w0" in let w1 := fresh "w1" in
    let w2 := fresh "w2" in let w3 := fresh "w3" in
    destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
    destruct H2 as [ w2 [ ]]; destruct H3 as [ w3 [ ]];
    exists (c w0 w1 w2 w3)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _, 
      H3 : ∃ _, _ ∧ _ , H4 : ∃ _, _ ∧ _, H5 : ∃ _, _ ∧ _ |-
          ∃ w, ?Γ ⊨ tvec_elim ?m _ _ _ _ _ _ ↣* w ∧ ?Γ ⊨ tvec_elim ?m _ _ _ _ _ _↣* w => 
    let w0 := fresh "w0" in let w1 := fresh "w1" in
    let w2 := fresh "w2" in let w3 := fresh "w3" in
    let w4 := fresh "w4" in let w5 := fresh "w5" in
    destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
    destruct H2 as [ w2 [ ]]; destruct H3 as [ w3 [ ]];
    destruct H4 as [ w4 [ ]]; destruct H5 as [ w5 [ ]];
    exists (tvec_elim m w0 w1 w2 w3 w4 w5)
  end. 

Theorem conversion_to_reduction :
  ∀ Γ t t', Γ ⊢ t ≡ t' → ∃ u, (sc Γ) ⊨ t ↣* u ∧ (sc Γ) ⊨ t' ↣* u.
Proof.
  intros Γ t t' conv_t.
  induction conv_t in conv_t |- *.
  all: try solve [match goal with | |- ∃ _, _ ∧ (_ ⊨ ?c ↣* _) => exists c end; split; apply red_trans_direct; gred; eauto using scoping_md].
  all: try solve [conversion_to_reduction_exists; split; greds].
  - match goal with | |- ∃ _, _ ∧ (_ ⊨ ?c ↣* _) => exists c end; split; greds.
    all: try (apply red_trans_direct; gred).
    erewrite scoping_md; eauto.
  - exists (Sort ℙ 0); split; greds.
  - match goal with 
    | H0: ∃ _, _ ∧ _, H1 : ∃ _, _∧ _, 
        Hi : ueq ?m ?i ?i', Hj : ueq ?m' ?j ?j' |- _ =>
            destruct H0 as [ w0 [ ]]; 
            destruct H1 as [ w1 [ ]];
            exists (Pi (red_lvl m i) (red_lvl m' j) m' m w0 w1); 
            destruct Hi, Hj
    end.
    all: split; subst; unfold red_lvl; cbn; greds.
  - match goal with 
    | H: ∃ _, _ ∧ _ |- _ => destruct H as [w []] end.
    eauto.
  - match goal with 
    | H0: ∃ _, _ ∧ _, H1 : ∃ _, _∧ _ |- _ =>
            destruct H0 as [ w0 [ ]]; 
            destruct H1 as [ w1 [ ]]
    end.
    assert (∃ w: term, (sc Γ⊨w0↣*w) ∧ sc Γ⊨w1↣*w) as Hw.
    { eauto using reduction_confluence. }
    destruct Hw as [wf []].
    exists wf.
    split; eauto using red_trans_trans.
  - exists ⋆; split; apply red_trans_direct; gred.
    all: eauto using scoping_md.
Qed.

Print Assumptions conversion_to_reduction.

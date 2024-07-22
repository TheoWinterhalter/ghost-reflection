(* Proof that the conversion is the symetric ans transitive closure
   of the multistep reduction *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.multisteps Require Export Properties Confluence.
From GhostTT.reduction.multisteps Require Export Reduction Transitivity.

Import ListNotations.

Notation "Γ ⊨ u ε⇶ v" := (Γ ⊨ ε|u| ⇶ ε|v|).

Set Default Goal Selector "!".

Lemma conv_subst_r (Γ : context) (Δ : scope) (m : mode) (σ σ' : nat → term) (t : term) :
  sscoping (sc Γ) σ Δ → sscoping (sc Γ) σ' Δ →
  Δ ⊨ ε|t|∷m → (∀ n, Γ ⊢ σ n ≡ σ' n) → Γ ⊢ ε|t| <[σ] ≡ ε|t| <[σ'].
Proof.
  intros Hscope Hscope' scope_t conv_σ.
  induction t in Γ, Δ, Hscope, Hscope', m, scope_t, σ, σ', conv_σ |- *.
  all: inversion scope_t; subst.
  all: try solve [gconv].
  3-5 : eauto using conv_irr, scoping_subst.
  all: cbn; gconv; unfold ueq; eauto using sscoping_shift.
  all: intro n; destruct n; gconv.
  all: cbn; ssimpl; eauto using conv_ren, rtyping_S.
Qed.


Theorem reduction_to_conversion :
  ∀ Γ m t t', Γ ⊢ t∷m → (sc Γ) ⊨ t ⇶ t' → Γ ⊢ t ε≡ t'.
Proof.
  intros Γ m t t' scope_t red_t.
  remember (sc Γ) as Γ0 eqn:e.
  induction red_t in Γ, Γ0, e, t, m, scope_t, t', red_t |- *.
  32:{ apply conv_irr; [| apply scope_star].
    apply scoping_castrm.
    erewrite scoping_md in *; eauto. congruence. }
  9, 31: solve [gconv]. 
  all: inversion scope_t; subst.
  26-28: solve [apply conv_irr; apply scoping_castrm; subst; gscope; eauto using red_scope]. 
  11-26: solve [gconv; cbn; f_equal; assumption].
  3-5: solve [subst; eapply conv_trans; [| eauto]; gconv; eauto using scoping_castrm].
  6-7: solve [unfold red_lvl; repeat case (mode_eq _ ℙ) as [ | ]; subst; gconv; unfold ueq; eauto].
  - cbn in *; inversion H2; subst.
    erewrite scoping_md in *; eauto.
    eapply conv_trans.
    * eauto using conv_beta, scoping_castrm.
    * eapply conv_trans.
      + eapply (conv_subst _ (_,,(_, ε|var 0|))).
        ++ eauto using sscoping_one, scoping_castrm.
        ++ eauto.
      + erewrite castrm_subst. asimpl.
        eapply conv_subst_r.
        ++ eauto using sscoping_one, scoping_castrm.
        ++ eauto using sscoping_one, scoping_castrm, red_scope.
        ++ apply scoping_castrm.
           eapply red_scope; eauto.
        ++ intro n; destruct n; cbn; gconv. reflexivity.
  - cbn in *; inversion H4; subst.
    eapply conv_trans.
    * eapply reveal_hide; eauto using scoping_castrm.
    * eauto using cong_app.
  - cbn in *; inversion H7; subst.
    eapply conv_trans.
    * eapply conv_nat_elim_succ; eauto using scoping_castrm.
    * gconv; eauto.
  - cbn in *; inversion H11; subst.
    eapply conv_trans; [ | eauto].
    gconv; eauto using scoping_castrm.
  - cbn in *; inversion H11; subst.
    eapply conv_trans.
    * eapply conv_vec_elim_cons; eauto using scoping_castrm.
    * gconv; eauto.
      + erewrite castrm_ren. eauto using conv_ren, rtyping_S.
      + do 2 erewrite castrm_ren. eauto using conv_ren, rtyping_S.
Qed.

Corollary reductions_to_conversion :
  ∀ Γ m t t', Γ ⊢ t∷m → (sc Γ) ⊨ t ⇶* t' → Γ ⊢ t ε≡ t'.
Proof.
  intros Γ m t t' scope_t red_t.
  induction red_t.
  - subst; gconv.
  - eapply conv_trans.
    * eauto using reduction_to_conversion.
    * eauto using red_scope.
Qed.


Local Ltac conversion_to_reduction_exists :=
  match goal with 
  | H : ∃ _, _ ∧ _ |- 
      ∃ w, ?Γ ⊨ ?c _ ⇶* w ∧ ?Γ ⊨ ?c _ ⇶* w => 
      let w := fresh "w" in
      destruct H as [ w [ ]];
      exists (c w)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _ |-
      ∃ w, ?Γ ⊨ ?c _ _ ⇶* w ∧ ?Γ ⊨ ?c _ _⇶* w => 
      let w0 := fresh "w0" in let w1 := fresh "w1" in
      destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
      exists (c w0 w1)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _ |-
      ∃ w, ?Γ ⊨ ?c _ _ _ ⇶* w ∧ ?Γ ⊨ ?c _ _ _ ⇶* w => 
      let w0 := fresh "w0" in let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
      destruct H2 as [ w2 [ ]];
      exists (c w0 w1 w2)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _, H3 : ∃ _, _ ∧ _ |-
      ∃ w, ?Γ ⊨ ?c _ _ _ _ ⇶* w ∧ ?Γ ⊨ ?c _ _ _ _ ⇶* w => 
      let w0 := fresh "w0" in let w1 := fresh "w1" in
      let w2 := fresh "w2" in let w3 := fresh "w3" in
      destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
      destruct H2 as [ w2 [ ]]; destruct H3 as [ w3 [ ]];
      exists (c w0 w1 w2 w3)
  | H0 : ∃ _, _ ∧ _, H1 : ∃ _, _ ∧ _, H2 : ∃ _, _ ∧ _, 
      H3 : ∃ _, _ ∧ _ , H4 : ∃ _, _ ∧ _, H5 : ∃ _, _ ∧ _ |-
          ∃ w, ?Γ ⊨ tvec_elim ?m _ _ _ _ _ _ ⇶* w ∧ ?Γ ⊨ tvec_elim ?m _ _ _ _ _ _⇶* w =>
          let w0 := fresh "w0" in let w1 := fresh "w1" in
          let w2 := fresh "w2" in let w3 := fresh "w3" in
          let w4 := fresh "w4" in let w5 := fresh "w5" in
          destruct H0 as [ w0 [ ]]; destruct H1 as [ w1 [ ]];
          destruct H2 as [ w2 [ ]]; destruct H3 as [ w3 [ ]];
          destruct H4 as [ w4 [ ]]; destruct H5 as [ w5 [ ]];
          exists (tvec_elim m w0 w1 w2 w3 w4 w5)
  end. 

Theorem conversion_to_reduction :
  ∀ Γ t t', Γ ⊢ t ≡ t' → ∃ u, (sc Γ) ⊨ t ⇶* u ∧ (sc Γ) ⊨ t' ⇶* u.
Proof.
  intros Γ t t' conv_t.
  induction conv_t in conv_t |- *.
  all: try solve [match goal with | |- ∃ _, _ ∧ (_ ⊨ ?c ⇶* _) => exists c end; split; apply red_trans_direct; gred; eauto using scoping_md].
  all: try solve [conversion_to_reduction_exists; split; greds].
  - match goal with | |- ∃ _, _ ∧ (_ ⊨ ?c ⇶* _) => exists c end; split; greds.
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
    assert (∃ w: term, (sc Γ⊨w0⇶*w) ∧ sc Γ⊨w1⇶*w) as Hw.
    { eauto using reduction_confluence. }
    destruct Hw as [wf []].
    exists wf.
    split; eauto using red_trans_trans.
  - exists ⋆; split; apply red_trans_direct; gred.
    all: eauto using scoping_md.
Qed.

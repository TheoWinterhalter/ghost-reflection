(** Basic meta-theory of the target CC **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CScoping
  CTyping.
From Coq Require Import Setoid Morphisms Relation_Definitions.

From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Definition crscoping (Γ : cscope) (ρ : nat → nat) (Δ : cscope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some (Some m) →
    nth_error Γ (ρ x) = Some (Some m).

Inductive csscoping (Γ : cscope) (σ : nat → cterm) : cscope → Prop :=
| cscope_nil : csscoping Γ σ []
| cscope_cons :
    ∀ Δ om,
      csscoping Γ (↑ >> σ) Δ →
      whenSome (ccscoping Γ (σ 0)) om →
      csscoping Γ σ (om :: Δ).

Lemma crscoping_S :
  ∀ Γ o,
    crscoping (o :: Γ) S Γ.
Proof.
  intros Γ o. intros x mx e.
  cbn. assumption.
Qed.

Lemma crscoping_shift :
  ∀ Γ Δ ρ mx,
    crscoping Γ ρ Δ →
    crscoping (mx :: Γ) (0 .: ρ >> S) (mx :: Δ).
Proof.
  intros ? ? ? mx h' y my e.
  destruct y.
  - simpl in *. assumption.
  - simpl in *. apply h'. assumption.
Qed.

Lemma cscoping_ren :
  ∀ Γ Δ ρ t m,
    crscoping Γ ρ Δ →
    ccscoping Δ t m →
    ccscoping Γ (ρ ⋅ t) m.
Proof.
  intros Γ Δ ρ t m hρ ht.
  pose proof crscoping_shift as lem.
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ asimpl ; econstructor ; eauto ].
Qed.

Lemma csscoping_weak :
  ∀ Γ Δ σ m,
    csscoping Γ σ Δ →
    csscoping (m :: Γ) (σ >> ren_cterm ↑) Δ.
Proof.
  intros Γ Δ σ m h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + destruct om. 2: eauto.
      cbn in *. eapply cscoping_ren. 2: eassumption.
      apply crscoping_S.
Qed.

Lemma cscoping_subst :
  ∀ Γ Δ σ t m,
    csscoping Γ σ Δ →
    ccscoping Δ t m →
    ccscoping Γ (t <[ σ ]) m.
Proof.
  intros Γ Δ σ t m hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ].
  - rename H into hx, Γ0 into Δ.
    asimpl. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
    destruct x.
    + simpl in *. inversion hx. subst. assumption.
    + apply IHhσ. simpl in hx. assumption.
  - asimpl. constructor.
    eapply IHht. constructor.
    + asimpl. apply csscoping_weak. assumption.
    + constructor.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply csscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply csscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
Qed.

Lemma csscoping_shift :
  ∀ Γ Δ mx σ,
    csscoping Γ σ Δ →
    csscoping (mx :: Γ) (cvar 0 .: σ >> ren1 S) (mx :: Δ).
Proof.
  intros Γ Δ mx σ h.
  constructor.
  - asimpl. apply csscoping_weak. assumption.
  - destruct mx. 2: constructor.
    cbn. constructor. reflexivity.
Qed.

#[export] Instance crscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) crscoping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m en. rewrite <- e. apply h. assumption.
Qed.

#[export] Instance csscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) csscoping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
Qed.

Lemma csscoping_ids :
  ∀ Γ,
    csscoping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| m Γ ih].
  - constructor.
  - constructor.
    + eapply csscoping_weak with (m := m) in ih. asimpl in ih. assumption.
    + destruct m. 2: constructor.
      constructor. reflexivity.
Qed.

Lemma csscoping_one :
  ∀ Γ u mx,
    ccscoping Γ u mx →
    csscoping Γ u.. (Some mx :: Γ).
Proof.
  intros Γ u mx h.
  constructor.
  - asimpl. apply csscoping_ids.
  - cbn. assumption.
Qed.

(** Renaming preserves typing **)

Definition crtyping (Γ : ccontext) (ρ : nat → nat) (Δ : ccontext) : Prop :=
  ∀ x m A,
    nth_error Δ x = Some (Some (m, A)) →
    ∃ B,
      nth_error Γ (ρ x) = Some (Some (m, B)) ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance crtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) crtyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  asimpl. rewrite <- eB.
  apply ren_cterm_morphism2. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma crtyping_cscoping :
  ∀ Γ Δ ρ,
    crtyping Γ ρ Δ →
    crscoping (csc Γ) ρ (csc Δ).
Proof.
  intros Γ Δ ρ h.
  intros n m e. unfold csc in e. rewrite nth_error_map in e.
  destruct (nth_error Δ n) as [[[] |]|] eqn:en. 2,3: discriminate.
  simpl in e. noconf e.
  eapply h in en. destruct en as [B [en eB]].
  unfold csc. rewrite nth_error_map.
  rewrite en. reflexivity.
Qed.

Lemma crtyping_shift :
  ∀ Γ Δ mx A ρ,
    crtyping Γ ρ Δ →
    crtyping (Some (mx, ρ ⋅ A) :: Γ) (0 .: ρ >> S) (Some (mx, A) :: Δ).
Proof.
  intros Γ Δ mx A ρ hρ.
  intros y my B hy.
  destruct y.
  - cbn in *. noconf hy. eexists.
    split. 1: reflexivity.
    asimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    asimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. asimpl in eC.
    assumption.
Qed.

Lemma crtyping_upren_none :
  ∀ Γ Δ ρ,
    crtyping Γ ρ Δ →
    crtyping (None :: Γ) (0 .: ρ >> S) (None :: Δ).
Proof.
  intros Γ Δ ρ hρ.
  intros y my B hy.
  destruct y.
  - cbn in *. noconf hy.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    asimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. asimpl in eC.
    assumption.
Qed.

Lemma crtyping_S :
  ∀ Γ m A,
    crtyping (Some (m, A) :: Γ) S Γ.
Proof.
  intros Γ m A. intros x mx B e.
  simpl. asimpl.
  eexists. split. 1: eassumption.
  asimpl. reflexivity.
Qed.

Lemma crscoping_sscoping :
  ∀ Γ Δ ρ,
    crscoping Γ ρ Δ →
    csscoping Γ (ρ >> cvar) Δ.
Proof.
  intros Γ Δ ρ h.
  induction Δ as [| m Δ ih] in ρ, h |- *.
  - constructor.
  - constructor.
    + apply ih. asimpl.
      intros x mx e.
      apply h. cbn. assumption.
    + destruct m. 2: constructor.
      constructor. apply h. reflexivity.
Qed.

Lemma cmeta_conv :
  ∀ Γ t A B,
    Γ ⊢ᶜ t : A →
    A = B →
    Γ ⊢ᶜ t : B.
Proof.
  intros Γ t A B h ->. assumption.
Qed.

Lemma cmeta_conv_trans_l :
  ∀ Γ u v w,
    u = v →
    Γ ⊢ᶜ v ≡ w →
    Γ ⊢ᶜ u ≡ w.
Proof.
  intros Γ ??? <- h. assumption.
Qed.

Lemma cmeta_conv_trans_r :
  ∀ Γ u v w,
    Γ ⊢ᶜ u ≡ v →
    v = w →
    Γ ⊢ᶜ u ≡ w.
Proof.
  intros Γ u v ? h <-. assumption.
Qed.

Ltac cscoping_ren_finish :=
  eapply cscoping_ren ; [| eassumption] ;
  try apply crscoping_shift ;
  apply crtyping_cscoping ; assumption.

Lemma cconv_ren :
  ∀ Γ Δ ρ u v,
    crtyping Γ ρ Δ →
    Δ ⊢ᶜ u ≡ v →
    Γ ⊢ᶜ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros Γ Δ ρ u v hρ h.
  induction h in Γ, ρ, hρ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; cscoping_ren_finish ].
  - asimpl. eapply cmeta_conv_trans_r. 1: econstructor.
    asimpl. reflexivity.
  - asimpl. constructor. eapply IHh. eapply crtyping_upren_none. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply crtyping_shift. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply crtyping_shift. assumption.
Qed.

Lemma ctyping_ren :
  ∀ Γ Δ ρ t A,
    crtyping Γ ρ Δ →
    Δ ⊢ᶜ t : A →
    Γ ⊢ᶜ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht in Γ, ρ, hρ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; cscoping_ren_finish ].
  - asimpl. eapply hρ in H as [B [? eB]].
    asimpl in eB. rewrite eB.
    econstructor. eassumption.
  - asimpl. econstructor.
    eapply IHht. eapply crtyping_upren_none. assumption.
  - asimpl. econstructor. 1: eauto.
    eapply IHht2. eapply crtyping_shift. assumption.
  - asimpl. econstructor. 1: eauto.
    + eapply IHht2. eapply crtyping_shift. assumption.
    + eapply IHht3. eapply crtyping_shift. assumption.
  - asimpl. asimpl in IHht1.
    eapply cmeta_conv. 1: econstructor. all: eauto.
    asimpl. reflexivity.
  - asimpl. asimpl in IHht1. asimpl in IHht2.
    econstructor. all: eauto.
    eapply cconv_ren. all: eassumption.
Qed.

(** Substitution preserves typing **)

Inductive cstyping (Γ : ccontext) (σ : nat → cterm) : ccontext → Prop :=
| ctype_nil : cstyping Γ σ []
| ctype_cons :
    ∀ Δ d,
      cstyping Γ (↑ >> σ) Δ →
      whenSome (λ '(m, A),
        ccscoping (csc Γ) (σ 0) m ∧
        Γ ⊢ᶜ σ 0 : A <[ S >> σ ]
      ) d →
      cstyping Γ σ (d :: Δ).

#[export] Instance styping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) cstyping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ? ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + destruct d as [[]|]. 2: constructor.
      cbn in *. split.
      * rewrite <- e. intuition assumption.
      * rewrite <- e. eapply cmeta_conv. 1: intuition eassumption.
        asimpl. apply subst_cterm_morphism2.
        intro. apply e.
Qed.

Lemma cstyping_cscoping :
  ∀ Γ Δ σ,
    cstyping Γ σ Δ →
    csscoping (csc Γ) σ (csc Δ).
Proof.
  intros Γ Δ σ h. induction h.
  - constructor.
  - cbn. constructor. 1: assumption.
    destruct d as [[]|]. 2: constructor.
    cbn in *. intuition assumption.
Qed.

Lemma cstyping_weak :
  ∀ Γ Δ σ mx A,
    cstyping Γ σ Δ →
    cstyping (Some (mx, A) :: Γ) (σ >> ren_cterm ↑) Δ.
Proof.
  intros Γ Δ σ mx A h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + destruct d as [[]|]. 2: constructor.
      cbn in *. split.
      * eapply cscoping_ren. 2: intuition eassumption.
        apply crscoping_S.
      * asimpl. eapply cmeta_conv.
        -- eapply ctyping_ren. 2: intuition eassumption.
          intros n ? ? e. asimpl. cbn.
          eexists. split. 1: eassumption.
          reflexivity.
        -- asimpl. reflexivity.
Qed.

Lemma cstyping_weak_none :
  ∀ Γ Δ σ,
    cstyping Γ σ Δ →
    cstyping (None :: Γ) (σ >> ren_cterm ↑) Δ.
Proof.
  intros Γ Δ σ h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + destruct d as [[]|]. 2: constructor.
      cbn in *. split.
      * eapply cscoping_ren. 2: intuition eassumption.
        apply crscoping_S.
      * asimpl. eapply cmeta_conv.
        -- eapply ctyping_ren. 2: intuition eassumption.
          intros n ? ? e. asimpl. cbn.
          eexists. split. 1: eassumption.
          reflexivity.
        -- asimpl. reflexivity.
Qed.

Lemma cstyping_shift :
  ∀ Γ Δ mx A σ,
    cstyping Γ σ Δ →
    cstyping (Some (mx, A <[ σ ]) :: Γ) (cvar 0 .: σ >> ren1 S) (Some (mx, A) :: Δ).
Proof.
  intros Γ Δ mx A σ h.
  constructor.
  - asimpl. apply cstyping_weak. assumption.
  - asimpl. cbn. split.
    + constructor. reflexivity.
    + eapply cmeta_conv.
      * econstructor. cbn. reflexivity.
      * asimpl. reflexivity.
Qed.

Lemma cstyping_shift_none :
  ∀ Γ Δ σ,
    cstyping Γ σ Δ →
    cstyping (None :: Γ) (cvar 0 .: σ >> ren1 S) (None :: Δ).
Proof.
  intros Γ Δ σ h.
  constructor.
  - asimpl. apply cstyping_weak_none. assumption.
  - asimpl. cbn. constructor.
Qed.

Lemma cstyping_ids :
  ∀ Γ,
    cstyping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| [[m A]|] Γ ih].
  - constructor.
  - constructor. 2: split.
    + eapply cstyping_weak with (mx := m) (A := A) in ih.
      asimpl in ih. assumption.
    + constructor. reflexivity.
    + eapply cmeta_conv. 1: econstructor.
      * cbn. reflexivity.
      * asimpl. substify. reflexivity.
  - constructor. 2: constructor.
    eapply cstyping_weak_none in ih. asimpl in ih. assumption.
Qed.

Lemma cstyping_one :
  ∀ Γ mx A u,
    ccscoping (csc Γ) u mx →
    Γ ⊢ᶜ u : A →
    cstyping Γ u.. (Some (mx, A) :: Γ).
Proof.
  intros Γ mx A u h hm.
  constructor. all: asimpl.
  - apply cstyping_ids.
  - cbn. intuition auto. asimpl. assumption.
Qed.

Ltac cscoping_subst_finish :=
  eapply cscoping_subst ; [| eassumption] ;
  try apply csscoping_shift ;
  apply cstyping_cscoping ; assumption.

Lemma cconv_subst :
  ∀ Γ Δ σ u v,
    cstyping Γ σ Δ →
    Δ ⊢ᶜ u ≡ v →
    Γ ⊢ᶜ u <[ σ ] ≡ v <[ σ ].
Proof.
  intros Γ Δ σ u v hσ h.
  induction h in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; cscoping_subst_finish ].
  - asimpl. eapply cmeta_conv_trans_r. 1: econstructor.
    asimpl. apply subst_cterm_morphism2.
    intros [].
    + asimpl. reflexivity.
    + asimpl. reflexivity.
  - asimpl. constructor.
    apply IHh. apply cstyping_shift_none. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply cstyping_shift. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply cstyping_shift. assumption.
Qed.

Lemma ctyping_subst :
  ∀ Γ Δ σ t A,
    cstyping Γ σ Δ →
    Δ ⊢ᶜ t : A →
    Γ ⊢ᶜ t <[ σ ] : A <[ σ ].
Proof.
  intros Γ Δ σ t A hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; cscoping_subst_finish ].
  - asimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. noconf H. cbn in *. intuition assumption.
    + apply IHhσ. assumption.
  - asimpl. econstructor.
    eapply IHht. eapply cstyping_shift_none. assumption.
  - asimpl. econstructor. 1: eauto.
    eapply IHht2. eapply cstyping_shift. assumption.
  - asimpl. econstructor. 1: eauto.
    + eapply IHht2. eapply cstyping_shift. assumption.
    + eapply IHht3. eapply cstyping_shift. assumption.
  - asimpl. asimpl in IHht1.
    eapply cmeta_conv. 1: econstructor. all: eauto.
    asimpl. apply subst_cterm_morphism2. intros [].
    + asimpl. reflexivity.
    + asimpl. reflexivity.
  - asimpl. asimpl in IHht1. asimpl in IHht2.
    econstructor. all: eauto.
    eapply cconv_subst. all: eassumption.
Qed.

(** Basic meta-theory before building the model **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Definition rscoping (Γ : scope) (ρ : nat → nat) (Δ : scope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some m →
    nth_error Γ (ρ x) = Some m.

Inductive sscoping (Γ : scope) (σ : nat → term) : scope → Prop :=
| scope_nil : sscoping Γ σ []
| scope_cons :
    ∀ Δ m,
      sscoping Γ (↑ >> σ) Δ →
      scoping Γ (σ var_zero) m →
      sscoping Γ σ (m :: Δ).

Lemma rscoping_shift :
  ∀ Γ Δ ρ mx,
    rscoping Γ ρ Δ →
    rscoping (mx :: Γ) (0 .: ρ >> S) (mx :: Δ).
Proof.
  intros ? ? ? mx h' y my e.
  destruct y.
  - simpl in *. assumption.
  - simpl in *. apply h'. assumption.
Qed.

Lemma scoping_ren :
  ∀ Γ Δ ρ t m,
    rscoping Γ ρ Δ →
    scoping Δ t m →
    scoping Γ (ren_term ρ t) m.
Proof.
  intros Γ Δ ρ t m hρ ht.
  pose proof rscoping_shift as lem.
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ asimpl ; econstructor ; eauto ].
Qed.

Lemma sscoping_weak :
  ∀ Γ Δ σ m,
    sscoping Γ σ Δ →
    sscoping (m :: Γ) (σ >> ren_term ↑) Δ.
Proof.
  intros Γ Δ σ m h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + asimpl. eapply scoping_ren. 2: eassumption.
      intros x mx e. simpl. assumption.
Qed.

Lemma scoping_subst :
  ∀ Γ Δ σ t m,
    sscoping Γ σ Δ →
    scoping Δ t m →
    scoping Γ (t <[ σ ]) m.
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
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply sscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply sscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
Qed.

Ltac forall_iff_impl T :=
  lazymatch eval cbn beta in T with
  | forall x : ?A, @?T' x =>
    let y := fresh x in
    refine (forall y, _) ;
    forall_iff_impl (@T' x)
  | ?P ↔ ?Q => exact (P → Q)
  | _ => fail "not a quantified ↔"
  end.

Ltac wlog_iff_using tac :=
  lazymatch goal with
  | |- ?G =>
    let G' := fresh in
    unshelve refine (let G' : Prop := _ in _) ; [ forall_iff_impl G |] ;
    let h := fresh in
    assert (h : G') ; [
      subst G'
    | subst G' ; intros ; split ; eauto ; apply h ; clear h ; tac
    ]
  end.

Ltac wlog_iff :=
  wlog_iff_using firstorder.

#[export] Instance rscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rscoping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m en. rewrite <- e. apply h. assumption.
Qed.

#[export] Instance sscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) sscoping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
Qed.

Lemma sscoping_ids :
  ∀ Γ,
    sscoping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| m Γ ih].
  - constructor.
  - constructor.
    + eapply sscoping_weak with (m := m) in ih. asimpl in ih. assumption.
    + constructor. reflexivity.
Qed.

(** Cast removal preserves modes **)

Lemma md_castrm :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (castrm t) m.
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ simpl ; econstructor ; eauto ].
  cbn. assumption.
Qed.

(** Cast removal commutes with renamings **)

Lemma castrm_ren :
  ∀ t ρ,
    ε| ρ ⋅ t | = ρ ⋅ ε| t |.
Proof.
  intros t ρ.
  induction t in ρ |- *.
  all: try reflexivity.
  all: solve [ simpl ; asimpl ; repeat core.unfold_funcomp ; f_equal ; auto ].
Qed.

(** Cast removal commutes with substitution **)

Lemma castrm_subst :
  ∀ t σ,
    ε| t <[ σ ] | = ε| t | <[ σ >> castrm ].
Proof.
  intros t σ.
  assert (∀ σ t,
    t <[ (var 0 .: σ >> ren1 ↑) >> castrm] =
    t <[ var 0 .: σ >> (castrm >> ren1 ↑) ]
  ).
  { intros θ u.
    apply subst_term_morphism2. intros n.
    destruct n.
    - asimpl. repeat core.unfold_funcomp. simpl. reflexivity.
    - asimpl. repeat core.unfold_funcomp. simpl.
      apply castrm_ren.
  }
  induction t in σ |- *. all: try reflexivity.
  all: try solve [ asimpl ; repeat core.unfold_funcomp ; simpl ; f_equal ; auto ].
  - asimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    asimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
  - asimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    asimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
Qed.

(** Inversion for scoping **)

(** Conversion entails mode equality **)

Lemma scope_app_inv :
  ∀ Γ u v m,
    scoping Γ (app u v) m →
    ∃ mx,
      scoping Γ u m ∧
      scoping Γ v mx.
Proof.
  intros Γ u v m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_lam_inv :
  ∀ Γ mx A t m,
    scoping Γ (lam mx A t) m →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) t m.
Proof.
  intros Γ mx A t m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_reveal_inv :
  ∀ Γ t P p m,
    scoping Γ (reveal t P p) m →
    In m [ mProp ; mGhost ] ∧
    scoping Γ t mGhost ∧
    scoping Γ P mKind ∧
    scoping Γ p m.
Proof.
  intros Γ t P p m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_revealP_inv :
  ∀ Γ t p m,
    scoping Γ (revealP t p) m →
    scoping Γ t mGhost ∧
    scoping Γ p mKind ∧
    m = mKind.
Proof.
  intros Γ t p m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_sort_inv :
  ∀ Γ ms i m,
    scoping Γ (Sort ms i) m →
    m = mKind.
Proof.
  intros Γ ms i m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_pi_inv :
  ∀ Γ mx m A B m',
    scoping Γ (Pi m mx A B) m' →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) B mKind ∧
    m' = mKind.
Proof.
  intros Γ mx m A B m' h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_erased_inv :
  ∀ Γ A m,
    scoping Γ (Erased A) m →
    scoping Γ A mKind ∧
    m = mKind.
Proof.
  intros Γ A m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_erase_inv :
  ∀ Γ t m,
    scoping Γ (erase t) m →
    scoping Γ t mType ∧
    m = mGhost.
Proof.
  intros Γ t m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_gheq_inv :
  ∀ Γ A u v m,
    scoping Γ (gheq A u v) m →
    scoping Γ A mKind ∧
    scoping Γ u mGhost ∧
    scoping Γ v mGhost ∧
    m = mKind.
Proof.
  intros Γ A u v m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_bot_elim_inv :
  ∀ Γ m A p m',
    scoping Γ (bot_elim m A p) m' →
    scoping Γ A mKind ∧
    scoping Γ p mProp ∧
    m' = m.
Proof.
  intros Γ m A p m' h.
  inversion h. subst.
  intuition eauto.
Qed.

Ltac scoping_fun :=
  match goal with
  | h : cscoping ?Γ ?t ?m, h' : cscoping ?Γ ?t ?m' |- _ =>
    assert (m = m') ; [
      eapply scoping_functional ; eassumption
    | first [ subst m' ; clear h' | subst m ; clear h ]
    ]
  end.

Lemma conv_scoping :
  ∀ Γ u v m,
    Γ ⊢ u ≡ v →
    cscoping Γ u m ↔ cscoping Γ v m.
Proof.
  intros Γ u v m h.
  induction h in m |- *.
  - split.
    + intro hu.
      eapply scope_app_inv in hu. destruct hu as [mx' [hl hu]].
      eapply scope_lam_inv in hl. destruct hl as [hA ht].
      eapply scoping_subst. 2: eassumption.
      constructor.
      * asimpl. apply sscoping_ids.
      * asimpl. assumption.
    + intro hu. econstructor.
      * constructor. 1: assumption.
        eapply scoping_subst with (Γ := sc Γ) (σ := u ..) in H0 as h.
        2:{
          constructor.
          - asimpl. apply sscoping_ids.
          - asimpl. assumption.
         }
         scoping_fun. assumption.
      * eassumption.
  - split.
    + intro hu. apply scope_reveal_inv in hu. intuition idtac.
      econstructor. all: eauto.
    + intro hu. apply scope_app_inv in hu. destruct hu. intuition idtac.
      scoping_fun. scoping_fun.
      constructor. all: auto.
      constructor. assumption.
  - split.
    + intro hu. apply scope_revealP_inv in hu. intuition subst.
      econstructor. all: eauto.
    + intro hu. apply scope_app_inv in hu. destruct hu. intuition idtac.
      scoping_fun. scoping_fun.
      constructor.
      * constructor. assumption.
      * assumption.
  - revert i j. wlog_iff. intros i j hu.
    apply scope_sort_inv in hu. subst. constructor.
  - clear h1 h2. revert A A' B B' IHh1 IHh2. wlog_iff.
    intros A A' B B' ihA ihB hu.
    apply scope_pi_inv in hu. intuition subst.
    constructor. all: firstorder.
  - clear h1 h2. revert A A' t t' IHh1 IHh2. wlog_iff.
    intros A A' t t' IHh1 IHh2 hu.
    apply scope_lam_inv in hu. intuition idtac.
    constructor. all: firstorder.
  - clear h1 h2. revert u u' v v' IHh1 IHh2. wlog_iff.
    intros u u' v v' ihu ihv h.
    apply scope_app_inv in h. destruct h. intuition idtac.
    econstructor. 1: firstorder.
    eapply ihv. eassumption.
  - clear h. revert A A' IHh. wlog_iff.
    intros A A' ih h.
    apply scope_erased_inv in h. intuition subst.
    constructor. firstorder.
  - clear h. revert u u' IHh. wlog_iff.
    intros u u' ih h.
    apply scope_erase_inv in h. intuition subst.
    constructor. firstorder.
  - clear h1 h2 h3. revert t t' P P' p p' IHh1 IHh2 IHh3. wlog_iff.
    intros t t' P P' p p' iht ihP ihp h.
    apply scope_reveal_inv in h. intuition idtac.
    constructor. all: firstorder.
  - clear h1 h2. revert t t' p p' IHh1 IHh2. wlog_iff.
    intros t t' p p' iht ihp h.
    apply scope_revealP_inv in h. intuition subst.
    constructor. all: firstorder.
  - clear h1 h2 h3. revert A A' u u' v v' IHh1 IHh2 IHh3. wlog_iff.
    intros A A' u u' v v' ihA ihu ihv h.
    apply scope_gheq_inv in h. intuition subst.
    constructor. all: firstorder.
  - clear h1 h2. revert A A' p p' IHh1 IHh2. wlog_iff.
    intros A A' p p' ihA ihp h.
    apply scope_bot_elim_inv in h. intuition subst.
    constructor. all: firstorder.
  - reflexivity.
  - symmetry. auto.
  - etransitivity. all: eauto.
  - split. all: intro. all: scoping_fun. all: assumption.
Qed.

(** Renaming preserves typing **)

Definition rtyping (Γ : context) (ρ : nat → nat) (Δ : context) : Prop :=
  ∀ x m A,
    nth_error Δ x = Some (m, A) →
    ∃ B,
      nth_error Γ (ρ x) = Some (m, B) ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

Lemma rtyping_scoping :
  ∀ Γ Δ ρ,
    rtyping Γ ρ Δ →
    rscoping (sc Γ) ρ (sc Δ).
Proof.
  intros Γ Δ ρ h.
  intros n m e. unfold sc in e. rewrite nth_error_map in e.
  destruct (nth_error (A := mode * term) Δ n) as [[]|] eqn:en. 2: discriminate.
  simpl in e. inversion e. subst. clear e.
  eapply h in en. destruct en as [B [en eB]].
  unfold sc. rewrite nth_error_map.
  unfold decl in en. rewrite en. reflexivity.
Qed.

Lemma rtyping_shift :
  ∀ Γ Δ mx A ρ,
    rtyping Γ ρ Δ →
    rtyping (Γ ,, (mx, ρ ⋅ A)) (0 .: ρ >> S) (Δ,, (mx, A)).
Proof.
  intros Γ Δ mx A ρ hρ.
  intros y my B hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    asimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    asimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. asimpl in eC.
    assumption.
Qed.

Lemma rscoping_sscoping :
  ∀ Γ Δ ρ,
    rscoping Γ ρ Δ →
    sscoping Γ (ρ >> var) Δ.
Proof.
  intros Γ Δ ρ h.
  induction Δ as [| m Δ ih] in ρ, h |- *.
  - constructor.
  - constructor.
    + apply ih. asimpl.
      intros x mx e.
      apply h. cbn. assumption.
    + constructor. apply h. reflexivity.
Qed.

Lemma meta_conv :
  ∀ Γ t A B,
    Γ ⊢ t : A →
    A = B →
    Γ ⊢ t : B.
Proof.
  intros Γ t A B h ->. assumption.
Qed.

Lemma meta_conv_trans_r :
  ∀ Γ u v w,
    Γ ⊢ u ≡ v →
    v = w →
    Γ ⊢ u ≡ w.
Proof.
  intros Γ u v ? h <-. assumption.
Qed.

Ltac scoping_ren_finish :=
  eapply scoping_ren ; [| eassumption] ;
  try apply rscoping_shift ;
  apply rtyping_scoping ; assumption.

Lemma conv_ren :
  ∀ Γ Δ ρ u v,
    rtyping Γ ρ Δ →
    Δ ⊢ u ≡ v →
    Γ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros Γ Δ ρ u v hρ h.
  induction h in Γ, ρ, hρ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; scoping_ren_finish ].
  - asimpl. eapply meta_conv_trans_r. 1: econstructor.
    all: try scoping_ren_finish.
    asimpl. reflexivity.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply rtyping_shift. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply rtyping_shift. assumption.
Qed.

Lemma typing_ren :
  ∀ Γ Δ ρ t A,
    rtyping Γ ρ Δ →
    Δ ⊢ t : A →
    Γ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht in Γ, ρ, hρ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; scoping_ren_finish ].
  - asimpl. eapply hρ in H as [B [? eB]].
    asimpl in eB. rewrite eB.
    econstructor. eassumption.
  - asimpl. econstructor. all: eauto. all: try scoping_ren_finish.
    eapply IHht2. eapply rtyping_shift. assumption.
  - asimpl. econstructor. all: eauto. all: try scoping_ren_finish.
    + eapply IHht2. eapply rtyping_shift. assumption.
    + eapply IHht3. eapply rtyping_shift. assumption.
  - asimpl. asimpl in IHht1.
    eapply meta_conv. 1: econstructor. all: eauto. all: try scoping_ren_finish.
    asimpl. reflexivity.
  - asimpl. asimpl in IHht1. asimpl in IHht2. asimpl in IHht3.
    econstructor. all: eauto. all: try scoping_ren_finish.
    eapply meta_conv. 1: apply IHht3. 1: auto.
    f_equal. f_equal. asimpl. reflexivity.
  - asimpl. asimpl in IHht2.
    econstructor. all: eauto.
    + eapply scoping_ren. 2: eassumption.
      apply rtyping_scoping. assumption.
    + eapply scoping_ren. 2: eassumption.
      apply rtyping_scoping. assumption.
    + eapply conv_ren. all: eassumption.
Qed.

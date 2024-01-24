(** Basic meta-theory before building the model **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.

From Equations Require Import Equations.

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

Lemma rscoping_S :
  ∀ Γ m,
    rscoping (m :: Γ) S Γ.
Proof.
  intros Γ m. intros x mx e.
  cbn. assumption.
Qed.

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
      apply rscoping_S.
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
    + apply IHht3. constructor.
      * asimpl. apply sscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
Qed.

Lemma sscoping_shift :
  ∀ Γ Δ mx σ,
    sscoping Γ σ Δ →
    sscoping (mx :: Γ) (var 0 .: σ >> ren1 S) (mx :: Δ).
Proof.
  intros Γ Δ mx σ h.
  constructor.
  - asimpl. apply sscoping_weak. assumption.
  - asimpl. constructor. reflexivity.
Qed.

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

Lemma sscoping_one :
  ∀ Γ u mx,
    scoping Γ u mx →
    sscoping Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx h.
  constructor.
  - asimpl. apply sscoping_ids.
  - asimpl. assumption.
Qed.

(** Cast removal preserves modes **)

Lemma scoping_castrm :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (castrm t) m.
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ simpl ; econstructor ; eauto ].
  cbn. assumption.
Qed.

Lemma md_castrm :
  ∀ Γ t,
    md Γ t = md Γ (castrm t).
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  cbn. rewrite <- IHt3. destruct md. all: reflexivity.
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
    apply ext_term. intros n.
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
    + asimpl. repeat core.unfold_funcomp. rewrite IHt2.
      auto.
    + asimpl. repeat core.unfold_funcomp. rewrite IHt3.
      auto.
Qed.

(** Inversion for scoping **)

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
  ∀ Γ mx A B t m,
    scoping Γ (lam mx A B t) m →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) B mKind ∧
    scoping (mx :: Γ) t m.
Proof.
  intros Γ mx A B t m h.
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
  ∀ Γ i j mx m A B m',
    scoping Γ (Pi i j m mx A B) m' →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) B mKind ∧
    m' = mKind.
Proof.
  intros Γ i j mx m A B m' h.
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

Lemma scope_hide_inv :
  ∀ Γ t m,
    scoping Γ (hide t) m →
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
  | h : scoping ?Γ ?t ?m, h' : scoping ?Γ ?t ?m' |- _ =>
    assert (m = m') ; [
      eapply scoping_functional ; eassumption
    | first [ subst m' ; clear h' | subst m ; clear h ]
    ]
  end.

(** Scoping of top **)

Lemma scope_top :
  ∀ Γ,
    scoping Γ top mKind.
Proof.
  intros Γ. constructor. all: constructor.
Qed.

(** Conversion entails mode equality **)

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
      eapply scope_lam_inv in hl. destruct hl as [hA [hB ht]].
      eapply scoping_subst. 2: eassumption.
      apply sscoping_one. assumption.
    + intro hu. econstructor.
      * constructor. 1,2: assumption.
        eapply scoping_subst with (Γ := sc Γ) (σ := u ..) in H1 as h.
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
      econstructor.
      * apply scope_top.
      * eapply scoping_ren. 2: econstructor ; eauto.
        apply rscoping_S.
    + intro hu. apply scope_pi_inv in hu. destruct hu as [? [happ ->]].
      cbn in happ. apply scope_app_inv in happ. destruct happ as [mx [hp ht]].
      eapply scoping_ren in H0 as ht'. 2: eapply rscoping_S with (m := mProp).
      asimpl in ht'. unfold shift in ht'.
      scoping_fun.
      constructor.
      * constructor. assumption.
      * assumption.
  - revert i j. wlog_iff. intros i j hu.
    apply scope_sort_inv in hu. subst. constructor.
  - clear h1 h2 h3 h4. revert i i' j j' A A' B B' IHh1 IHh2 IHh3 IHh4. wlog_iff.
    intros i i' j j' A A' B B' ihA ihB ihi ihj hu.
    apply scope_pi_inv in hu. intuition subst.
    constructor. all: firstorder.
  - clear h1 h2 h3. revert A A' B B' t t' IHh1 IHh2 IHh3. wlog_iff.
    intros A A' B B' t t' ihA ihB iht hu.
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
    apply scope_hide_inv in h. intuition subst.
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

(** Alternate lemma but using md **)

Definition rscoping_comp (Γ : scope) ρ (Δ : scope) :=
  ∀ x,
    nth_error Δ x = None →
    nth_error Γ (ρ x) = None.

Definition sscoping_comp (Γ : scope) σ (Δ : scope) :=
  ∀ n,
    nth_error Δ n = None →
    ∃ m,
      σ n = var m ∧
      nth_error Γ m = None.

Lemma sscoping_comp_shift :
  ∀ Γ Δ σ mx,
    sscoping_comp Γ σ Δ →
    sscoping_comp (mx :: Γ) (up_term σ) (mx :: Δ).
Proof.
  intros Γ Δ σ mx h. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn.
    eapply h in e as e'. destruct e' as [m [e1 e2]].
    ssimpl. exists (S m). intuition eauto.
    rewrite e1. ssimpl. reflexivity.
Qed.

Lemma rscoping_comp_S :
  ∀ Γ m,
    rscoping_comp (m :: Γ) S Γ.
Proof.
  intros Γ m. intros n e. cbn. assumption.
Qed.

Lemma nth_nth_error :
  ∀ A (l : list A) (d : A) n,
    nth n l d = match nth_error l n with Some x => x | None => d end.
Proof.
  intros A l d n.
  induction l in n |- *.
  - cbn. destruct n. all: reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Qed.

Lemma rscoping_comp_upren :
  ∀ Γ Δ m ρ,
    rscoping_comp Γ ρ Δ →
    rscoping_comp (m :: Γ) (up_ren ρ) (m :: Δ).
Proof.
  intros Γ Δ m ρ h. intros x e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

Lemma md_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    md Γ (ρ ⋅ t) = md Δ t.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite 2!nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e. reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn. eapply IHt3.
    + eapply rscoping_shift. assumption.
    + eapply rscoping_comp_upren. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma md_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    md Γ (t <[ σ ]) = md Δ t.
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + clear hcσ. induction hσ as [| σ Δ mx hσ ih hm] in n, m, e |- *.
      1: destruct n ; discriminate.
      destruct n.
      * cbn in *. noconf e.
        erewrite scoping_md. 2: eassumption. reflexivity.
      * cbn in e. eapply ih. assumption.
    + eapply hcσ in e. destruct e as [m [e1 e2]].
      rewrite e1. cbn. rewrite nth_nth_error. rewrite e2. reflexivity.
  - cbn. eapply IHt3.
    + eapply sscoping_shift. assumption.
    + eapply sscoping_comp_shift. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma sscoping_comp_one :
  ∀ Γ u mx,
    sscoping_comp Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn. eexists. intuition eauto.
Qed.

Lemma conv_md :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    mdc Γ u = mdc Γ v.
Proof.
  intros Γ u v h.
  induction h.
  all: try solve [ cbn ; reflexivity ].
  all: try solve [ cbn ; eauto ].
  - cbn. erewrite md_subst.
    2: eapply sscoping_one ; eassumption.
    2: eapply sscoping_comp_one.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    cbn in H2. destruct H2 as [| []]. 3: contradiction.
    all: subst. all: reflexivity.
  - cbn. rewrite IHh3. reflexivity.
  - etransitivity. all: eassumption.
  - erewrite 2!scoping_md. 2,3: eassumption.
    reflexivity.
Qed.

(** Renaming preserves typing **)

Definition rtyping (Γ : context) (ρ : nat → nat) (Δ : context) : Prop :=
  ∀ x m A,
    nth_error Δ x = Some (m, A) →
    ∃ B,
      nth_error Γ (ρ x) = Some (m, B) ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rtyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  asimpl. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma rtyping_scoping :
  ∀ Γ Δ ρ,
    rtyping Γ ρ Δ →
    rscoping (sc Γ) ρ (sc Δ).
Proof.
  intros Γ Δ ρ h.
  intros n m e. unfold sc in e. rewrite nth_error_map in e.
  destruct (nth_error Δ n) as [[]|] eqn:en. 2: discriminate.
  simpl in e. inversion e. subst. clear e.
  eapply h in en. destruct en as [B [en eB]].
  unfold sc. rewrite nth_error_map.
  rewrite en. reflexivity.
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

Lemma rtyping_S :
  ∀ Γ m A,
    rtyping (Γ ,, (m, A)) S Γ.
Proof.
  intros Γ m A. intros x mx B e.
  simpl. asimpl.
  eexists. split. 1: eassumption.
  asimpl. reflexivity.
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

Lemma meta_conv_trans_l :
  ∀ Γ u v w,
    u = v →
    Γ ⊢ v ≡ w →
    Γ ⊢ u ≡ w.
Proof.
  intros Γ ??? <- h. assumption.
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
  - asimpl. eapply conv_trans. 1: constructor.
    + eapply scoping_ren. 2: eassumption.
      eapply rtyping_scoping. assumption.
    + eapply scoping_ren. 2: eassumption.
      eapply rtyping_scoping. assumption.
    + cbn. ssimpl. apply conv_refl.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply rtyping_shift. assumption.
    + eapply IHh3. eassumption.
    + eapply IHh4. apply rtyping_shift. assumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. apply rtyping_shift. assumption.
    + eapply IHh3. apply rtyping_shift. assumption.
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
  - asimpl. asimpl in IHht1. asimpl in IHht4.
    eapply meta_conv. 1: econstructor. all: eauto. all: try scoping_ren_finish.
    1:{ eapply IHht4. eapply rtyping_shift. assumption. }
    asimpl. reflexivity.
  - asimpl. asimpl in IHht1. asimpl in IHht2. asimpl in IHht3.
    econstructor. all: eauto. all: try scoping_ren_finish.
    eapply meta_conv. 1: apply IHht3. 1: auto.
    f_equal. f_equal. asimpl. reflexivity.
  - asimpl. asimpl in IHht2.
    econstructor. all: eauto. all: try scoping_ren_finish.
    rewrite 2!castrm_ren.
    eapply conv_ren. all: eassumption.
Qed.

(** Substitution preserves typing **)

Inductive styping (Γ : context) (σ : nat → term) : context → Prop :=
| type_nil : styping Γ σ []
| type_cons :
    ∀ Δ m A,
      styping Γ (↑ >> σ) Δ →
      cscoping Γ (σ 0) m →
      Γ ⊢ σ var_zero : A <[ S >> σ ] →
      styping Γ σ (Δ,, (m, A)).

#[export] Instance styping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) styping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
    + rewrite <- e. eapply meta_conv. 1: eassumption.
      asimpl. apply ext_term.
      intro. apply e.
Qed.

Lemma styping_scoping :
  ∀ Γ Δ σ,
    styping Γ σ Δ →
    sscoping (sc Γ) σ (sc Δ).
Proof.
  intros Γ Δ σ h. induction h.
  - constructor.
  - cbn. constructor. all: assumption.
Qed.

Lemma styping_weak :
  ∀ Γ Δ σ mx A,
    styping Γ σ Δ →
    styping (Γ,, (mx, A)) (σ >> ren_term ↑) Δ.
Proof.
  intros Γ Δ σ mx A h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + eapply scoping_ren. 2: eassumption.
      apply rscoping_S.
    + asimpl. eapply meta_conv.
      * eapply typing_ren. 2: eassumption.
        intros n ? ? e. asimpl. cbn.
        eexists. split. 1: eassumption.
        reflexivity.
      * asimpl. reflexivity.
Qed.

Lemma styping_shift :
  ∀ Γ Δ mx A σ,
    styping Γ σ Δ →
    styping (Γ ,, (mx, A <[ σ ])) (var 0 .: σ >> ren1 S) (Δ,, (mx, A)).
Proof.
  intros Γ Δ mx A σ h.
  constructor.
  - asimpl. apply styping_weak. assumption.
  - asimpl. constructor. reflexivity.
  - asimpl. eapply meta_conv.
    + econstructor. cbn. reflexivity.
    + asimpl. reflexivity.
Qed.

Lemma styping_ids :
  ∀ Γ,
    styping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| [m A] Γ ih].
  - constructor.
  - constructor.
    + eapply styping_weak with (mx := m) (A := A) in ih.
      asimpl in ih. assumption.
    + constructor. reflexivity.
    + eapply meta_conv. 1: econstructor.
      * cbn. reflexivity.
      * asimpl. substify. reflexivity.
Qed.

Lemma styping_one :
  ∀ Γ mx A u,
    cscoping Γ u mx →
    Γ ⊢ u : A →
    styping Γ u.. (Γ ,, (mx, A)).
Proof.
  intros Γ mx A u h hm.
  constructor. all: asimpl. all: auto.
  apply styping_ids.
Qed.

Ltac scoping_subst_finish :=
  eapply scoping_subst ; [| eassumption] ;
  try apply sscoping_shift ;
  apply styping_scoping ; assumption.

Ltac conv_subst_finish :=
  eapply scoping_subst ; [| eassumption] ;
  try apply sscoping_shift ;
  assumption.

Lemma conv_subst :
  ∀ Γ Δ σ u v,
    sscoping (sc Γ) σ (sc Δ) →
    Δ ⊢ u ≡ v →
    Γ ⊢ u <[ σ ] ≡ v <[ σ ].
Proof.
  intros Γ Δ σ u v hσ h.
  induction h in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; conv_subst_finish ].
  - asimpl. eapply meta_conv_trans_r. 1: econstructor.
    all: try conv_subst_finish.
    ssimpl. apply ext_term.
    intros [].
    + asimpl. reflexivity.
    + asimpl. reflexivity.
  - ssimpl. cbn. eapply conv_trans. 1: constructor. 1,2: conv_subst_finish.
    cbn. ssimpl. apply conv_refl.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. cbn. apply sscoping_shift. assumption.
    + asimpl in IHh3. firstorder.
    + asimpl in IHh4. eapply IHh4. cbn. apply sscoping_shift. eassumption.
  - asimpl. constructor.
    + auto.
    + eapply IHh2. cbn. apply sscoping_shift. assumption.
    + eapply IHh3. cbn. apply sscoping_shift. assumption.
Qed.

Lemma sscoping_castrm :
  ∀ Γ σ Δ,
    sscoping Γ σ Δ →
    sscoping Γ (σ >> castrm) Δ.
Proof.
  intros Γ σ Δ h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + ssimpl. eapply scoping_castrm. assumption.
Qed.

Lemma typing_subst :
  ∀ Γ Δ σ t A,
    styping Γ σ Δ →
    Δ ⊢ t : A →
    Γ ⊢ t <[ σ ] : A <[ σ ].
Proof.
  intros Γ Δ σ t A hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ; scoping_subst_finish ].
  - asimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - asimpl. econstructor. all: eauto. all: try scoping_subst_finish.
    eapply IHht2. eapply styping_shift. assumption.
  - asimpl. econstructor. all: eauto. all: try scoping_subst_finish.
    + eapply IHht2. eapply styping_shift. assumption.
    + eapply IHht3. eapply styping_shift. assumption.
  - asimpl. asimpl in IHht1.
    eapply meta_conv. 1: econstructor.
    all: eauto. all: try scoping_subst_finish.
    1:{ eapply IHht4. eapply styping_shift. assumption. }
    asimpl. apply ext_term. intros [].
    + asimpl. reflexivity.
    + asimpl. reflexivity.
  - asimpl. asimpl in IHht1. asimpl in IHht2. asimpl in IHht3.
    econstructor. all: eauto. all: try scoping_subst_finish.
    eapply meta_conv. 1: apply IHht3. 1: auto.
    f_equal. f_equal. asimpl. reflexivity.
  - asimpl. asimpl in IHht2.
    econstructor. all: eauto. all: try scoping_subst_finish.
    rewrite 2!castrm_subst.
    eapply conv_subst. 2: eassumption.
    apply sscoping_castrm. eapply styping_scoping. assumption.
Qed.

(** Inversion of typing **)

Set Equations With UIP.
Derive NoConfusion EqDec for mode.
Derive NoConfusion NoConfusionHom EqDec for term.
Derive Signature for typing.

Require Import Equations.Prop.DepElim.

Ltac destruct_exists h :=
  match type of h with
  | ∃ _, _ => destruct h as [? h] ; destruct_exists h
  | _ => idtac
  end.

Notation "Γ ⊢ u ε≡ v" :=
  (Γ ⊢ ε|u| ≡ ε|v|)
  (at level 80, u, v at next level, format "Γ  ⊢  u  ε≡  v").

Lemma type_var_inv :
  ∀ Γ x A,
    Γ ⊢ var x : A →
    ∃ m B,
      nth_error Γ x = Some (m, B) ∧
      Γ ⊢ (plus (S x)) ⋅ B ε≡ A.
Proof.
  intros Γ x A h.
  dependent induction h.
  - eexists _, _. split. 1: eassumption.
    constructor.
  - destruct_exists IHh1. intuition subst.
    eexists _, _. split. 1: eassumption.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_sort_inv :
  ∀ Γ m i A,
    Γ ⊢ Sort m i : A →
    Γ ⊢ Sort mKind (usup m i) ε≡ A.
Proof.
  intros ???? h.
  dependent induction h.
  - constructor.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_pi_inv :
  ∀ Γ i j mx m A B C,
    Γ ⊢ Pi i j m mx A B : C →
    cscoping Γ A mKind ∧
    cscoping (Γ ,, (mx, A)) B mKind ∧
    Γ ⊢ A : Sort mx i ∧
    Γ ,, (mx, A) ⊢ B : Sort m j ∧
    Γ ⊢ Sort m (umax m i j) ε≡ C.
Proof.
  intros ???????? h.
  dependent induction h.
  - intuition eauto. constructor.
  - intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_lam_inv :
  ∀ Γ mx A B t C,
    Γ ⊢ lam mx A B t : C →
    ∃ i j m,
      cscoping Γ A mKind ∧
      cscoping (Γ ,, (mx, A)) B mKind ∧
      cscoping (Γ ,, (mx, A)) t m ∧
      Γ ⊢ A : Sort mx i ∧
      Γ ,, (mx, A) ⊢ B : Sort m j ∧
      Γ ,, (mx, A) ⊢ t : B ∧
      Γ ⊢ Pi i j m mx A B ε≡ C.
Proof.
  intros Γ mx A B t C h.
  dependent induction h.
  - eexists _,_,_. intuition eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_app_inv :
  ∀ Γ t u C,
    Γ ⊢ app t u : C →
    ∃ mx m i j A B,
      cscoping (Γ ,, (mx, A)) B mKind ∧
      cscoping Γ t m ∧
      cscoping Γ u mx ∧
      cscoping Γ A mKind ∧
      Γ ⊢ t : Pi i j m mx A B ∧
      Γ ⊢ u : A ∧
      Γ ⊢ A : Sort mx i ∧
      Γ ,, (mx, A) ⊢ B : Sort m j ∧
      Γ ⊢ B <[ u .. ] ε≡ C.
Proof.
  intros Γ t u C h.
  dependent induction h.
  - eexists _,_,_,_,_,_. intuition eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_,_,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_erased_inv :
  ∀ Γ A C,
    Γ ⊢ Erased A : C →
    ∃ i,
      cscoping Γ A mKind ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ Sort mGhost i ε≡ C.
Proof.
  intros Γ A C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_hide_inv :
  ∀ Γ t C,
    Γ ⊢ hide t : C →
    ∃ i A,
      cscoping Γ A mKind ∧
      cscoping Γ t mType ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ t : A ∧
      Γ ⊢ Erased A ε≡ C.
Proof.
  intros Γ t C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_reveal_inv :
  ∀ Γ t P p C,
    Γ ⊢ reveal t P p : C →
    ∃ i m A,
      cscoping Γ p m ∧
      cscoping Γ t mGhost ∧
      cscoping Γ P mKind ∧
      cscoping Γ A mKind ∧
      In m [ mProp ; mGhost ] ∧
      Γ ⊢ t : Erased A ∧
      Γ ⊢ P : Erased A ⇒[ i | S i / mGhost | mKind ] Sort m i ∧
      Γ ⊢ p : Pi i (S i) m mType A (app (S ⋅ P) (hide (var 0))) ∧
      Γ ⊢ app P t ε≡ C.
Proof.
  intros Γ t P p C h.
  dependent induction h.
  - eexists _,_,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_revealP_inv :
  ∀ Γ t p C,
    Γ ⊢ revealP t p : C →
    ∃ i A,
      cscoping Γ t mGhost ∧
      cscoping Γ p mKind ∧
      Γ ⊢ t : Erased A ∧
      Γ ⊢ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 ∧
      Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ t p C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_gheq_inv :
  ∀ Γ A u v C,
    Γ ⊢ gheq A u v : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ u mGhost ∧
      cscoping Γ v mGhost ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ v : A ∧
      Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ A u v C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_ghrefl_inv :
  ∀ Γ A u C,
    Γ ⊢ ghrefl A u : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ u mGhost ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ gheq A u u ε≡ C.
Proof.
  intros Γ A u C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_ghcast_inv :
  ∀ Γ e P t C,
    Γ ⊢ ghcast e P t : C →
    ∃ i m A u v,
      cscoping Γ A mKind ∧
      cscoping Γ P mKind ∧
      cscoping Γ u mGhost ∧
      cscoping Γ v mGhost ∧
      cscoping Γ t m ∧
      cscoping Γ e mProp ∧
      m ≠ mKind ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ v : A ∧
      Γ ⊢ e : gheq A u v ∧
      Γ ⊢ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i ∧
      Γ ⊢ t : app P u ∧
      Γ ⊢ app P v ε≡ C.
Proof.
  intros Γ e P t C h.
  dependent induction h.
  - eexists _,_,_,_,_. intuition idtac. 4,9,10: eauto. all: eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_,_,_.
    intuition idtac. 4,9,10: eauto. all: eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_bot_inv :
  ∀ Γ C,
    Γ ⊢ bot : C →
    Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_bot_elim_inv :
  ∀ Γ m A p C,
    Γ ⊢ bot_elim m A p : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ p mProp ∧
      Γ ⊢ A : Sort m i ∧
      Γ ⊢ p : bot ∧
      Γ ⊢ A ε≡ C.
Proof.
  intros Γ m A p C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Ltac ttinv h h' :=
  lazymatch type of h with
  | _ ⊢ ?t : _ =>
    lazymatch t with
    | var _ => eapply type_var_inv in h as h'
    | Sort _ _ => eapply type_sort_inv in h as h'
    | Pi _ _ _ _ _ _ => eapply type_pi_inv in h as h'
    | lam _ _ _ _ => eapply type_lam_inv in h as h'
    | app _ _ => eapply type_app_inv in h as h'
    | Erased _ => eapply type_erased_inv in h as h'
    | hide _ => eapply type_hide_inv in h as h'
    | reveal _ _ _ => eapply type_reveal_inv in h as h'
    | revealP _ _ => eapply type_revealP_inv in h as h'
    | gheq _ _ _ => eapply type_gheq_inv in h as h'
    | ghrefl _ _ => eapply type_ghrefl_inv in h as h'
    | ghcast _ _ _ => eapply type_ghcast_inv in h as h'
    | bot => eapply type_bot_inv in h as h'
    | bot_elim _ _ _ => eapply type_bot_elim_inv in h as h'
    end
  end.

(** Uniqueness of type **)

Ltac unitac h1 h2 :=
  let h1' := fresh h1 in
  let h2' := fresh h2 in
  ttinv h1 h1' ; ttinv h2 h2' ;
  destruct_exists h1' ;
  destruct_exists h2' ;
  intuition subst ;
  eapply conv_trans ; [
    eapply conv_sym ; eassumption
  | idtac
  ].

Lemma type_unique :
  ∀ Γ t A B,
    Γ ⊢ t : A →
    Γ ⊢ t : B →
    Γ ⊢ A ε≡ B.
Proof.
  intros Γ t A B hA hB.
  induction t in Γ, A, B, hA, hB |- *.
  all: try unitac hA hB. all: try assumption.
  - eapply meta_conv_trans_l. 2: eassumption.
    f_equal. congruence.
  - repeat scoping_fun.
    eapply IHt2 in H7. 2: eassumption.
    eapply conv_trans. 2: eassumption.
    cbn.
    constructor.
    + apply conv_refl.
    + apply conv_refl.
    + eapply IHt1 in H6. 2: exact H5. assumption.
    + (* eapply conv_sym. assumption.
  - repeat scoping_fun.
    eapply conv_trans. 2: eassumption.
    eapply conv_subst.
    + apply styping_one. all: eauto.
    + (* Without injectivity of Π I'm kinda stuck here. *)
      (* Another solution is of course to also annotate application but come on
        it sounds really bad and I'm not sure I can recover from this.
      *)
      admit.
  - eapply conv_trans. 2: eassumption.
    (* eapply IHt. all: auto. *)
    (* Another problem arises here with respect to sorts! *)
    (* I know Type_i ≡ Type_j but not Ghost_i ≡ Ghost_j *)
    (* What would be a reasonable option? *)
    (* Once again, it seems uniqueness may be out of reach, let's postpone *)
    admit.
  - eapply conv_trans. 2: eassumption.
    constructor. eapply IHt. all: auto.
  - eapply conv_trans. 2: eassumption.
    constructor. 1: apply conv_refl.
    eapply IHt1 in H19. 2: eassumption.
    (* Missing injectivity of gheq too. Once again, we could add arguements *)
    admit. *)
Abort.

(** Validity (or presupposition) **)

Lemma validity :
  ∀ Γ t A,
    wf Γ →
    Γ ⊢ t : A →
    cscoping Γ t (mdc Γ t) ∧
    (∃ i, Γ ⊢ A : Sort (mdc Γ t) i).
Proof.
  intros Γ t A hΓ h.
  induction h in hΓ |- *.
  all: try solve [
    split ; [
      cbn ; econstructor ; eauto
    | eexists ; econstructor ; eauto
    ]
  ].
  - split.
    + constructor. unfold sc. rewrite nth_error_map.
      rewrite H. cbn.
      change mType with (fst (mType, A)).
      rewrite map_nth. erewrite nth_error_nth. 2: eassumption.
      reflexivity.
    + induction hΓ as [| Γ my j B hΓ ih hB] in x, H |- *. 1: destruct x ; discriminate.
      destruct x.
      * cbn in *. inversion H. subst.
        exists j. asimpl.
        eapply meta_conv. 1: eapply typing_ren.
        -- apply rtyping_S.
        -- eassumption.
        -- reflexivity.
      * cbn in H. eapply ih in H as [i h].
        eapply typing_ren in h. 2: eapply rtyping_S with (m := my) (A := B).
        asimpl in h.
        exists i. assumption.
  - split.
    + cbn. constructor. 1,2: auto.
      apply IHh3. econstructor. all: eauto.
    + eexists. cbn. eapply meta_conv. 1: econstructor. all: auto.
      erewrite scoping_md. 2: eassumption.
      reflexivity.
  - split.
    + cbn. econstructor. 2: eauto.
      eapply scoping_md in H0 as e. subst.
      assumption.
    + forward IHh1 by auto. destruct IHh1 as [hst [l hP]].
      ttinv hP hP'.
      eexists. eapply meta_conv. 1: eapply typing_subst. 2: intuition eauto.
      * eapply styping_one. all: auto.
      * cbn. erewrite scoping_md. 1: reflexivity.
        assumption.
  - split.
    + cbn. erewrite scoping_md. 2: eassumption.
      cbn in H3. destruct H3 as [<- | [<- |]].
      * constructor. all: auto with datatypes.
      * constructor. all: auto with datatypes.
      * contradiction.
    + eexists. eapply meta_conv. 1: econstructor. 4: shelve. all: eauto.
      * asimpl. constructor.
      * pose proof IHh2 as hP.
        forward hP by auto. destruct hP as [hsP [l hP]].
        eapply type_pi_inv in hP. intuition assumption.
      * pose proof IHh2 as hP.
        forward hP by auto. destruct hP as [hsP [l hP]].
        eapply type_pi_inv in hP. intuition assumption.
      * cbn - [mdc]. f_equal.
        cbn. erewrite scoping_md. 2: eassumption.
        destruct H3 as [<- | [<- |]]. 3: contradiction.
        all: reflexivity.
      Unshelve. constructor. assumption.
  - split.
    + cbn. econstructor. all: eauto.
      * erewrite scoping_md. 2: eassumption. assumption.
      * erewrite scoping_md. 2: eassumption. assumption.
    + eexists. eapply meta_conv. 1: econstructor. 4: shelve.
      all: try eassumption.
      * cbn. constructor.
      * cbn. econstructor.
      * cbn - [mdc]. f_equal.
        cbn. erewrite scoping_md. 2: eassumption. reflexivity.
      Unshelve. assumption.
  - split.
    + cbn. constructor. all: auto.
    + eexists. cbn. eassumption.
  - split.
    + erewrite scoping_md. 2: eassumption. assumption.
    + eexists. erewrite scoping_md. 2: eassumption. eassumption.
Qed.

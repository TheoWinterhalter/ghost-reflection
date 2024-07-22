(*** Consequences of the model ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  Scoping TermMode Typing BasicMetaTheory.
From Coq Require Import Setoid Morphisms Relation_Definitions.
From GhostTT.reduction Require Import Notations Injectivity.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Uniqueness of typing

  We show a restricted form of uniqueness ignoring universe levels.
  This way we do not rely on the absence of cumulativity.

  In order to do this, we build a function which puts all universes to 0.

**)

Fixpoint urm (t : term) : term :=
  match t with
  | var x => var x
  | Sort m i => Sort m 0
  | Pi i j m mx A B => Pi 0 0 m mx (urm A) (urm B)
  | lam mx A t => lam mx (urm A) (urm t)
  | app u v => app (urm u) (urm v)
  | Erased A => Erased (urm A)
  | hide t => hide (urm t)
  | reveal t P p => reveal (urm t) (urm P) (urm p)
  | Reveal t P => Reveal (urm t) (urm P)
  | toRev t p u => toRev (urm t) (urm p) (urm u)
  | fromRev t p u => fromRev (urm t) (urm p) (urm u)
  | gheq A u v => gheq (urm A) (urm u) (urm v)
  | ghrefl A u => ghrefl (urm A) (urm u)
  | ghcast A u v e P t => ghcast (urm A) (urm u) (urm v) (urm e) (urm P) (urm t)
  | tbool => tbool
  | ttrue => ttrue
  | tfalse => tfalse
  | tif m b P t f => tif m (urm b) (urm P) (urm t) (urm f)
  | tnat => tnat
  | tzero => tzero
  | tsucc n => tsucc (urm n)
  | tnat_elim m n P z s => tnat_elim m (urm n) (urm P) (urm z) (urm s)
  | tvec A n => tvec (urm A) (urm n)
  | tvnil A => tvnil (urm A)
  | tvcons a n v => tvcons (urm a) (urm n) (urm v)
  | tvec_elim m A n v P z s => tvec_elim m (urm A) (urm n) (urm v) (urm P) (urm z) (urm s)
  | bot => bot
  | bot_elim m A p => bot_elim m (urm A) (urm p)
  end.

Lemma urm_ren :
  ∀ t ρ,
    urm (ρ ⋅ t) = ρ ⋅ (urm t).
Proof.
  intros t ρ.
  induction t in ρ |- *.
  all: solve [ cbn ; f_equal ; eauto ].
Qed.

Lemma urm_subst :
  ∀ t σ,
    urm (t <[ σ ]) = (urm t) <[ σ >> urm ].
Proof.
  intros t σ.
  induction t in σ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. apply ext_term.
    intros []. 1: reflexivity.
    cbn. ssimpl. rewrite urm_ren. reflexivity.
  - cbn. f_equal. 1:eauto.
    rewrite IHt2. apply ext_term.
    intros []. 1: reflexivity.
    cbn. ssimpl. rewrite urm_ren. reflexivity.
Qed.

Lemma urm_scoping :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (urm t) m.
Proof.
  intros Γ t m h.
  induction h. all: solve [ econstructor ; eauto ].
Qed.

Definition urm_ctx (Γ : context) :=
  map (λ '(m, A), (m, urm A)) Γ.

Lemma sc_urm_ctx :
  ∀ Γ,
    sc (urm_ctx Γ) = sc Γ.
Proof.
  intros Γ.
  unfold sc, urm_ctx. rewrite map_map.
  apply map_ext. intros [m A]. reflexivity.
Qed.

Lemma urm_cscoping :
  ∀ Γ t m,
    cscoping Γ t m →
    cscoping (urm_ctx Γ) (urm t) m.
Proof.
  intros Γ t m h. rewrite sc_urm_ctx.
  apply urm_scoping. assumption.
Qed.

Lemma conv_urm :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    urm_ctx Γ ⊢ urm u ≡ urm v.
Proof.
  intros Γ u v h.
  induction h.
  all: try solve [ cbn ; econstructor ; eauto using urm_cscoping ].
  - cbn. rewrite urm_subst. eapply conv_trans.
    1:{
      eapply conv_beta.
      all: try eapply urm_cscoping ; eauto.
      all: eapply urm_scoping. all: rewrite sc_urm_ctx. all: eassumption.
    }
    ssimpl. apply conv_refl.
  - cbn. rewrite !urm_ren. constructor.
    all: try eapply urm_cscoping ; eauto.
  - cbn. constructor. all: eauto.
    all: unfold ueq. all: eauto.
Qed.

Notation "Γ ⊢ u ≈ v" :=
  (urm_ctx Γ ⊢ urm ε| u | ≡ urm ε| v |)
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≈  v").

Lemma urm_conv_aux :
  ∀ Γ A A' B B',
    Γ ⊢ A' ε≡ A →
    Γ ⊢ B' ε≡ B →
    Γ ⊢ A' ≈ B' →
    Γ ⊢ A ≈ B.
Proof.
  intros Γ A A' B B' hA hB h.
  eapply conv_trans.
  - apply conv_sym. eapply conv_urm. eassumption.
  - eapply conv_trans.
    2:{ eapply conv_urm. eassumption. }
    assumption.
Qed.

Lemma conv_meta_refl :
  ∀ Γ u v,
    u = v →
    Γ ⊢ u ≡ v.
Proof.
  intros Γ u ? ->.
  apply conv_refl.
Qed.

Ltac unitac h1 h2 :=
  let h1' := fresh h1 in
  let h2' := fresh h2 in
  ttinv h1 h1' ; ttinv h2 h2' ;
  destruct_exists h1' ;
  destruct_exists h2' ;
  intuition subst ;
  eapply urm_conv_aux ; [
    eassumption ..
  | idtac
  ].

Lemma sscoping_urm :
  ∀ Γ σ Δ,
    sscoping Γ σ Δ →
    sscoping Γ (σ >> urm) Δ.
Proof.
  intros Γ σ Δ h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + ssimpl. eapply urm_scoping. assumption.
Qed.

(* Conversion only requires the scope not the full context *)
Lemma conv_upto :
  ∀ Γ Δ u v,
    Γ ⊢ u ≡ v →
    sc Γ = sc Δ →
    Δ ⊢ u ≡ v.
Proof.
  intros Γ Δ u v h e.
  induction h in Δ, e |- *.
  all: try solve [ cbn ; econstructor ; rewrite <- ?e ; eauto ].
  - constructor. all: eauto.
    eapply IHh2. cbn. f_equal. assumption.
  - constructor. all: eauto.
    eapply IHh2. cbn. f_equal. assumption.
Qed.

Lemma castrm_urm (t : term): 
  ε|urm t| = urm ε|t|. 
Proof.
  induction t; cbn; auto.
  all: f_equal; auto.
Qed.

Lemma type_unique {Γ : context} {t A B : term} :
    Γ ⊢ t : A →
    Γ ⊢ t : B →
    Γ ⊢ A ≈ B.
Proof.
  intros hA hB.
  induction t in Γ, A, B, hA, hB |- *.
  all: try unitac hA hB. all: try apply conv_refl.
  - apply conv_meta_refl. congruence.
  - cbn. repeat scoping_fun.
    eapply IHt2 in H10. 2: exact H9.
    cbn in H10.
    constructor. 1: apply conv_refl. 2,3: compute ; auto.
    eapply conv_upto. 1: eassumption.
    cbn. reflexivity.
  - repeat scoping_fun.
    eapply IHt1 in H8. 2: exact H7.
    cbn in H8. eapply injectivity_Pi in H8 as [_ [_ [_ H8]]].
    * rewrite !castrm_urm in H8.
      rewrite !castrm_castrm in H8.
      rewrite !castrm_subst.
      rewrite !urm_subst.
      eapply conv_subst.
      2: eassumption.
      apply sscoping_urm. apply sscoping_castrm. cbn. eapply sscoping_one.
    rewrite sc_urm_ctx. eassumption.
    * gscope.
      + apply urm_cscoping.
        apply scoping_castrm.
        assumption.
      + rewrite sc_urm_ctx.
        change ((Γ,, (x, x3)) ⊢ urm ε| x4 |∷𝕂).
        rewrite <- sc_urm_ctx.
        apply urm_cscoping.
        apply scoping_castrm.
        assumption.
    * gscope.
      + apply urm_cscoping.
        apply scoping_castrm.
        assumption.
      + rewrite sc_urm_ctx.
        change ((Γ,, (x, x9)) ⊢ urm ε| x10 |∷𝕂).
        rewrite <- sc_urm_ctx.
        apply urm_cscoping.
        apply scoping_castrm.
        assumption.
  - cbn. econstructor. eauto.
  - cbn. constructor. 1: eauto.
    gconv.
Qed.

(** Modes are coherent with sorts **)

Lemma mode_coherence :
  ∀ Γ t A m i,
    wf Γ →
    Γ ⊢ A : Sort m i →
    Γ ⊢ t : A →
    Γ ⊢ t ∷ m.
Proof.
  intros Γ t A m i hΓ hA h.
  eapply validity in h. 2: assumption.
  destruct h as [hs [j hA']].
  eapply type_unique in hA'. 2: eapply hA.
  cbn in hA'. eapply injectivity_Sort in hA'. subst.
  assumption.
Qed.

Lemma scoping_type {Γ: context} {A t: term}:
  wf Γ → Γ ⊢ t:A → Γ ⊢ A∷𝕂.
Proof.
  intros wfΓ type_t.
  specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i type_A]].
  specialize (validity Γ _ _ wfΓ type_A) as [scope_A [j type_scope]].
  ttinv type_scope type_scope.
  apply injectivity_Sort in type_scope.
  rewrite type_scope in *.
  assumption.
Qed.

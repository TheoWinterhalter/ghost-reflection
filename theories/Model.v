(*** Consequences of the model ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival Param.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Injectivity of type formers and constructors in CC

  We assume that the target enjoys injectivity of constructors of inductive
  types and of type formers. We will only state what we need though.
  We take them as axioms to avoid having to develop the full meta-theory of
  CC, which would defeat the purpose of using it as a model.

**)

Axiom ctyval_inj :
  ∀ Γ mk mk' A A' a a',
    Γ ⊢ᶜ ctyval mk A a ≡ ctyval mk' A' a' →
    mk = mk' ∧
    Γ ⊢ᶜ A ≡ A' ∧
    Γ ⊢ᶜ a ≡ a'.

(** Deduced injectivity in GTT **)

(** Injectivity of sort modes **)

Lemma sort_mode_inj :
  ∀ Γ m m' i i',
    Γ ⊢ Sort m i ≡ Sort m' i' →
    m = m'.
Proof.
  intros Γ m m' i i' h.
  eapply erase_conv in h as he. cbn in he.
  destruct m, m'. all: try reflexivity. all: exfalso. all: cbn in he.
  all: solve [ eapply ctyval_inj in he ; intuition discriminate ].
Qed.

(** Relative consistency **)

Definition cc_consistency :=
  ¬ (∃ t, [] ⊢ᶜ t : cbot).

Definition gtt_consistency :=
  ¬ (∃ t, [] ⊢ t : bot).

Theorem relative_consistency :
  cc_consistency →
  gtt_consistency.
Proof.
  intros hcons. intros [t ht].
  eapply hcons.
  apply param_typing in ht as htp.
  cbn in htp. unfold ptype in htp. cbn - [mode_inb] in htp.
  eapply validity in ht as h. 2: constructor.
  destruct h as [hs [i h]].
  ttinv h h'. cbn in h'.
  eapply sort_mode_inj in h'.
  remember (md [] t) as m eqn:em in *. clear em. subst.
  cbn in htp.
  eexists. eassumption.
Qed.

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
  | lam mx A B t => lam mx (urm A) (urm B) (urm t)
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
    + rewrite IHt2. apply ext_term.
      intros []. 1: reflexivity.
      cbn. ssimpl. rewrite urm_ren. reflexivity.
    + rewrite IHt3. apply ext_term.
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

(** Injectivity of Π types in the source

  We assume injectivity in the source for ε-conversion (ε≡).
  We argue that this should hold given it is essentially CC conversion.
  Sadly our model doesn't allow us to obtain it for free and we would need to
  resort to other methods to obtain it, typically the same used to get it for
  CC (such as confluence of an underlying rewriting system).

  We only state it for the codomain

**)

Axiom pi_inj :
  ∀ Γ i j m mx A B A' B',
    Γ ⊢ Pi i j m mx A B ≡ Pi i j m mx A' B' →
    Γ ,, (mx, A) ⊢ B ≡ B'.

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

Lemma type_unique :
  ∀ Γ t A B,
    Γ ⊢ t : A →
    Γ ⊢ t : B →
    Γ ⊢ A ≈ B.
Proof.
  intros Γ t A B hA hB.
  induction t in Γ, A, B, hA, hB |- *.
  all: try unitac hA hB. all: try apply conv_refl.
  - apply conv_meta_refl. congruence.
  - repeat scoping_fun.
    cbn. apply conv_refl.
  - repeat scoping_fun.
    eapply IHt1 in H8. 2: exact H7.
    cbn in H8. eapply pi_inj in H8.
    rewrite !castrm_subst.
    rewrite !urm_subst.
    eapply conv_subst. 2: eassumption.
    apply sscoping_urm. apply sscoping_castrm. cbn. eapply sscoping_one.
    rewrite sc_urm_ctx. eassumption.
  - cbn. econstructor. eauto.
Qed.

(** Modes are coherent with sorts **)

Lemma mode_coherence :
  ∀ Γ t A m i,
    wf Γ →
    Γ ⊢ A : Sort m i →
    Γ ⊢ t : A →
    cscoping Γ t m.
Proof.
  intros Γ t A m i hΓ hA h.
  eapply validity in h. 2: assumption.
  destruct h as [hs [j hA']].
  eapply type_unique in hA'. 2: eapply hA.
  cbn in hA'. eapply sort_mode_inj in hA'. subst.
  assumption.
Qed.

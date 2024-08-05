(*** Admissible simpler typing rules

  We replace some of the rules from the Typing module by ones that typically
  do not require scoping information.
  We use the same names in order to shadow them on purpose.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations RAsimpl ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival Param Model.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Section Admissible.

  Context Γ (hΓ : wf Γ).

  Lemma wf_cons :
    ∀ m i A,
      Γ ⊢ A : Sort m i →
      wf (Γ ,, (m, A)).
  Proof.
    intros m i A h.
    econstructor. all: eauto.
    eapply mode_coherence. all: eauto.
    constructor.
  Qed.

  Ltac adm :=
    econstructor ; eauto ; try eapply mode_coherence ; eauto using wf_cons ;
    try solve [ constructor ].

  Lemma type_pi :
    ∀ i j mx m A B,
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ Pi i j m mx A B : Sort m (umax mx m i j).
  Proof.
    intros. adm.
  Qed.

  Lemma type_lam :
    ∀ mx m i j A B t,
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ,, (mx, A) ⊢ t : B →
      Γ ⊢ lam mx A t : Pi i j m mx A B.
  Proof.
    intros. adm.
  Qed.

  Lemma type_app :
    ∀ i j mx m A B t u,
      Γ ⊢ t : Pi i j m mx A B →
      Γ ⊢ u : A →
      Γ ⊢ app t u : B <[ u .. ].
  Proof.
    intros i j mx m A B t u ht hu.
    eapply validity in ht as hP. 2: assumption.
    destruct hP as [_ [k hP]]. ttinv hP hP'.
    intuition subst.
    adm. eapply type_pi. all: eauto.
  Qed.

  Lemma type_erased :
    ∀ i A,
      Γ ⊢ A : Sort mType i →
      Γ ⊢ Erased A : Sort mGhost i.
  Proof.
    intros. adm.
  Qed.

  Lemma type_hide :
    ∀ i A t,
      Γ ⊢ A : Sort mType i →
      Γ ⊢ t : A →
      Γ ⊢ hide t : Erased A.
  Proof.
    intros. adm.
  Qed.

  Lemma type_reveal :
    ∀ i j m A t P p,
      In m [ mProp ; mGhost ] →
      Γ ⊢ t : Erased A →
      Γ ⊢ P : Erased A ⇒[ i | usup m j / mGhost | mKind ] Sort m j →
      Γ ⊢ p : Pi i j m mType A (app (S ⋅ P) (hide (var 0))) →
      Γ ⊢ reveal t P p : app P t.
  Proof.
    intros i j m A t P p hm ht hP hp.
    eapply validity in ht as hE. 2: assumption.
    destruct hE as [_ [l hE]]. ttinv hE hA.
    destruct hA as [k ?]. intuition idtac.
    eapply validity in hP as hT. 2: assumption.
    destruct hT as [_ [q hT]].
    ttinv hT hT'. intuition idtac.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [ll hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    cbn in hc. apply sort_mode_inj in hc. subst.
    adm. adm.
  Qed.

  Lemma type_Reveal :
    ∀ i A t p,
      Γ ⊢ t : Erased A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ Reveal t p : Sort mProp 0.
  Proof.
    intros i A t p ht hp.
    eapply validity in ht as hE. 2: assumption.
    destruct hE as [_ [j hE]]. ttinv hE hA.
    destruct hA as [k [? [? hc]]].
    set (mt := mdc Γ t) in *. clearbody mt. apply sort_mode_inj in hc. subst.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [l hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    set (mp := mdc Γ p) in *. clearbody mp. cbn in hc.
    apply sort_mode_inj in hc. subst.
    adm.
  Qed.

  Lemma type_toRev :
    ∀ i A t p u,
      Γ ⊢ t : A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ u : app p t →
      Γ ⊢ toRev t p u : Reveal (hide t) p.
  Proof.
    intros i A t p u ht hp hu.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [l hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    set (mp := mdc Γ p) in *. clearbody mp. cbn in hc.
    apply sort_mode_inj in hc. subst.
    adm.
    eapply meta_conv.
    - eapply type_app. all: eassumption.
    - cbn. reflexivity.
  Qed.

  Lemma type_fromRev :
    ∀ i A t p u,
      Γ ⊢ t : A →
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ u : Reveal (hide t) p →
      Γ ⊢ fromRev t p u : app p t.
  Proof.
    intros i A t p u ht hp hu.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [l hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    set (mp := mdc Γ p) in *. clearbody mp. cbn in hc.
    apply sort_mode_inj in hc. subst.
    adm. eapply type_Reveal. 2: eassumption.
    eapply type_hide. all: eassumption.
  Qed.

  Lemma type_gheq :
    ∀ i A u v,
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ v : A →
      Γ ⊢ gheq A u v : Sort mProp 0.
  Proof.
    intros. adm.
  Qed.

  Lemma type_ghrefl :
    ∀ i A u,
      Γ ⊢ A : Sort mGhost i →
      Γ ⊢ u : A →
      Γ ⊢ ghrefl A u : gheq A u u.
  Proof.
    intros. adm.
  Qed.

  Lemma type_ghcast :
    ∀ i m A u v e P t,
      m ≠ mKind →
      Γ ⊢ e : gheq A u v →
      Γ ⊢ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i →
      Γ ⊢ t : app P u →
      Γ ⊢ ghcast A u v e P t : app P v.
  Proof.
    intros i m A u v e P t hm he hP ht.
    eapply validity in he as he'. 2: assumption.
    destruct he' as [_ [l he']].
    ttinv he' he''. destruct he'' as [? [? [? [? [? [? [? hc]]]]]]].
    set (me := mdc Γ e) in *. clearbody me. cbn in hc.
    apply sort_mode_inj in hc. subst.
    eapply validity in hP as hP'. 2: assumption.
    destruct hP' as [_ [lP hP']].
    ttinv hP' hP''. destruct hP'' as [? [? [? [? hc]]]].
    set (mp := mdc Γ P) in *. clearbody mp. cbn in hc.
    apply sort_mode_inj in hc. subst.
    adm. eapply meta_conv.
    - eapply type_app. all: eauto.
    - cbn. reflexivity.
  Qed.

  Lemma type_if :
    ∀ i m b P t f,
      m ≠ mKind →
      Γ ⊢ b : tbool →
      Γ ⊢ P : tbool ⇒[ 0 | (usup m i) / mType | mKind ] Sort m i →
      Γ ⊢ t : app P ttrue →
      Γ ⊢ f : app P tfalse →
      Γ ⊢ tif m b P t f : app P b.
  Proof.
    intros i m b P t f hm hb hP ht hf.
    adm.
    - eapply type_pi. all: constructor.
    - eapply meta_conv.
      + eapply type_app. 1: eassumption.
        constructor.
      + reflexivity.
    - eapply meta_conv.
      + eapply type_app. 1: eassumption.
        constructor.
      + reflexivity.
  Qed.

  Lemma type_bot_elim :
    ∀ i m A p,
      Γ ⊢ A : Sort m i →
      Γ ⊢ p : bot →
      Γ ⊢ bot_elim m A p : A.
  Proof.
    intros. adm.
  Qed.

  Lemma type_conv :
    ∀ i m A B t,
      cscoping Γ t m →
      Γ ⊢ t : A →
      Γ ⊢ A ε≡ B →
      Γ ⊢ B : Sort m i →
      Γ ⊢ t : B.
  Proof.
    intros i m A B t hst ht hc hB.
    eapply validity in ht as hE. 2: assumption.
    destruct hE as [_ [j hE]].
    econstructor. all: eauto.
    all: eapply mode_coherence. all: eauto. all: constructor.
  Qed.

  Lemma type_conv_alt :
    ∀ i j m A B t,
      Γ ⊢ t : A →
      Γ ⊢ A ε≡ B →
      Γ ⊢ A : Sort m i →
      Γ ⊢ B : Sort m j →
      Γ ⊢ t : B.
  Proof.
    intros i j m A B t ht hc hA hB.
    eapply type_conv. all: eauto.
    eapply mode_coherence. 3: eassumption. all: eassumption.
  Qed.

End Admissible.

Lemma type_pi_opt :
  ∀ Γ i j mx m A B,
    wf Γ →
    Γ ⊢ A : Sort mx i →
    (wf (Γ ,, (mx, A)) → Γ ,, (mx, A) ⊢ B : Sort m j) →
    Γ ⊢ Pi i j m mx A B : Sort m (umax mx m i j).
Proof.
  intros Γ i j mx m A B hΓ hA hB.
  eapply type_pi. all: auto.
  apply hB. eapply wf_cons. all: eauto.
Qed.

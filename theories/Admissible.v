(*** Admissible simpler typing rules

  We replace some of the rules from the Typing module by ones that typically
  do not require scoping information.
  We use the same names in order to shadow them on purpose.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
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
      Γ ⊢ lam mx A B t : Pi i j m mx A B.
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
    ∀ i m A t P p,
      In m [ mProp ; mGhost ] →
      Γ ⊢ t : Erased A →
      Γ ⊢ P : Erased A ⇒[ i | S i / mGhost | mKind ] Sort m i →
      Γ ⊢ p : Pi i (S i) m mType A (app (S ⋅ P) (hide (var 0))) →
      Γ ⊢ reveal t P p : app P t.
  Proof.
    intros i m A t P p hm ht hP hp.
    eapply validity in ht as hE. 2: assumption.
    destruct hE as [_ [j hE]]. ttinv hE hA.
    destruct hA as [k ?]. intuition idtac.
    eapply validity in hP as hT. 2: assumption.
    destruct hT as [_ [q hT]].
    ttinv hT hT'. intuition idtac.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [l hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    cbn in hc. apply sort_mode_inj in hc. subst.
    adm. adm.
  Qed.

  Lemma type_Reveal :
    ∀ i A t p,
      Γ ⊢ t : Erased A →
      Γ ⊢ p : A ⇒[ i | 1 / mType | mKind ] Sort mProp 0 →
      Γ ⊢ Reveal t p : Sort mProp 0.
  Proof.
    intros i A t p ht hp.
    eapply validity in ht as hE. 2: assumption.
    destruct hE as [_ [j hE]]. ttinv hE hA.
    destruct hA as [k ?]. intuition idtac.
    eapply validity in hp as hp'. 2: assumption.
    destruct hp' as [_ [l hp']].
    ttinv hp' hp''. destruct hp'' as [? [? [? [? hc]]]].
    cbn in hc. apply sort_mode_inj in hc.
    adm.
    (* WAIT! There is a mistake in the type of Erased, it should be a kind! *)
  Abort.

End Admissible.

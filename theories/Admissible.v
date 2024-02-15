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
    eapply mode_coherence. all: eauto. econstructor.
  Qed.

  Lemma type_pi :
    ∀ i j mx m A B,
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ⊢ Pi i j m mx A B : Sort m (umax mx m i j).
  Proof.
    intros i j mx m A B hA hB.
    eapply type_pi. all: eauto.
    - eapply mode_coherence. all: eauto. econstructor.
    - eapply mode_coherence. all: eauto.
      + eapply wf_cons. eassumption.
      + econstructor.
  Qed.

  Lemma type_lam :
    ∀ mx m i j A B t,
      Γ ⊢ A : Sort mx i →
      Γ ,, (mx, A) ⊢ B : Sort m j →
      Γ ,, (mx, A) ⊢ t : B →
      Γ ⊢ lam mx A B t : Pi i j m mx A B.
  Proof.
    intros mx m i j A B t hA hB ht.
    econstructor. all: eauto.
    all: eapply mode_coherence. all: eauto using wf_cons.
    all: econstructor.
  Qed.

End Admissible.

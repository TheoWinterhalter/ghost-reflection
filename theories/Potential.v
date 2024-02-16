(*** Potential translations from GRTT to GTT and their properties ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory Param RTyping Admissible.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Definition rmctx (Γ : context) :=
  map (λ '(m, A), (m, ε|A|)) Γ.

Definition tr_ctx Γ Γ' :=
  wf Γ' ∧ Γ = rmctx Γ'.

(* Notation "D ∈ ⟦ G ⟧x" :=
  (tr_ctx G D)
  (at level 8, G at next level). *)

Definition tr_ty t A Γ' t' A' :=
  Γ' ⊢ t' : A' ∧ t = ε|t'| ∧ A = ε|A'|.

Notation "D ⊨ t : A ∈ ⟦ u : B ⟧x" :=
  (tr_ty u B D t A)
  (at level 8, t, A, u, B at next level).

Lemma tr_sort :
  ∀ A Γ' A' s' m i,
    wf Γ' →
    Γ' ⊨ A' : s' ∈ ⟦ A : Sort m i ⟧x →
    s' = Sort m i.
Proof.
  intros A Γ' A' s' m i hΓ [h [eA es]].
  eapply (f_equal (λ x, mdc Γ' x)) in es as em. cbn in em.
  rewrite <- md_castrm in em.
  eapply validity in h as hs. 2: assumption.
  destruct hs as [_ [j hs]].
  destruct s'. all: try discriminate.
  - cbn in es. congruence.
  - cbn in em. cbn in es.
    ttinv hs hT. destruct hT as [k [mx ?]]. intuition subst.
    remd in em. subst. contradiction.
Qed.

Lemma tr_sort' :
  ∀ A Γ' A' s' m i,
    wf Γ' →
    Γ' ⊨ A' : s' ∈ ⟦ A : Sort m i ⟧x →
    Γ' ⊨ A' : Sort m i ∈ ⟦ A : Sort m i ⟧x.
Proof.
  intros A Γ' A' s' m i hΓ hA.
  eapply tr_sort in hA as h. 2: assumption.
  subst. assumption.
Qed.

Lemma tr_cons :
  ∀ Γ mx A Γ' A' i,
    tr_ctx Γ Γ' →
    Γ' ⊨ A' : Sort mx i ∈ ⟦ A : Sort mx i ⟧x →
    tr_ctx (Γ,, (mx, A)) (Γ',, (mx, A')).
Proof.
  intros Γ mx A Γ' A' i [hΓ eΓ] [hA eA].
  split.
  - eapply wf_cons. all: eassumption.
  - cbn. intuition subst. reflexivity.
Qed.

Lemma sc_rmctx :
  ∀ Γ, sc (rmctx Γ) = sc Γ.
Proof.
  intros Γ.
  unfold sc, rmctx. rewrite map_map. apply map_ext.
  intros [m A]. reflexivity.
Qed.

Lemma tr_scoping :
  ∀ m Γ' t' A',
    wf Γ' →
    Γ' ⊢ t' : A' →
    cscoping (rmctx Γ') ε|t'| m →
    cscoping Γ' t' m.
Proof.
  intros m Γ' t' A' hΓ ht htm.
  rewrite sc_rmctx in htm.
  eapply validity in ht as vt. 2: assumption.
  destruct vt as [hst _]. eapply scoping_castrm in hst as hst'.
  scoping_fun. assumption.
Qed.

Lemma tr_choice :
  ∀ Γ t A Γ' t' A' A'' m i,
    tr_ctx Γ Γ' →
    cscoping Γ t m →
    Γ' ⊨ t' : A' ∈ ⟦ t : A ⟧x →
    Γ' ⊨ A'' : Sort m i ∈ ⟦ A : Sort m i ⟧x →
    Γ' ⊨ t' : A'' ∈ ⟦ t : A ⟧x.
Proof.
  intros Γ t A Γ' t' A' A'' m i hΓ hmt ht hA.
  destruct hΓ as [hΓ eΓ].
  destruct ht as [ht [et eA]].
  destruct hA as [hA [eA' _]].
  unfold tr_ty. intuition auto.
  eapply type_conv. all: eauto.
  - subst. eapply tr_scoping. all: eauto.
  - rewrite <- eA. rewrite <- eA'. apply conv_refl.
Qed.

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

Lemma tr_choice :
  ∀ t A Γ' t' A' A'' m i,
    Γ' ⊨ t' : A' ∈ ⟦ t : A ⟧x →
    Γ' ⊨ A'' : Sort m i ∈ ⟦ A : Sort m i ⟧x →
    Γ' ⊨ t' : A'' ∈ ⟦ t : A ⟧x.
Proof.
  intros t A Γ' t' A' A'' m i ht hA.
  destruct ht as [ht [et eA]].
  destruct hA as [hA [eA' _]].
  unfold tr_ty. intuition auto.
  econstructor. all: eauto.
  4:{ rewrite <- eA. rewrite <- eA'. apply conv_refl. }
  (* TODO
    We need more assumptions. If we are willing to assume wf Γ' then we can
    also use admissible rules.
    Maybe we could even use type_conv_alt if we have enough to go on.
    We'll see in the course of the proof of the theorem.
  *)
Abort.

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

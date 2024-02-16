(*** Translation from GRTT to GTT ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory Admissible RTyping
  Potential.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Lemma tr_pi :
  ∀ i j m mx A B Γ' A' B',
    wf Γ' →
    Γ' ⊨ A' : Sort mx i ∈ ⟦ A : Sort mx i ⟧x →
    (Γ',, (mx,A')) ⊨ B' : Sort m j ∈ ⟦ B : Sort m j ⟧x →
    Γ' ⊨ (Pi i j m mx A' B') : (Sort m (umax mx m i j)) ∈
    ⟦ (Pi i j m mx A B) : (Sort m (umax mx m i j)) ⟧x.
Proof.
  intros i j m mx A B Γ' A' B' hΓ hA hB.
  unfold tr_ty in *. intuition subst.
  - eapply type_pi. all: eassumption.
  - cbn. intuition reflexivity.
Qed.

Theorem elim_reflection :
  ∀ Γ t A Γ',
    Γ ⊢ˣ t : A →
    tr_ctx Γ Γ' →
    ∑ t' A', Γ' ⊨ t' : A' ∈ ⟦ t : A ⟧x.
Proof.
  intros Γ t A Γ' h hctx.
  induction h in Γ', hctx |- *.
  - destruct hctx as [hΓ ->].
    unfold rmctx in e. rewrite nth_error_map in e.
    destruct nth_error as [[m' B] |] eqn:e'. 2: discriminate.
    cbn in e. noconf e.
    eexists (var x), _. split.
    + econstructor. eassumption.
    + intuition eauto. rewrite castrm_ren. reflexivity.
  - eexists (Sort m i), _. split.
    + constructor.
    + intuition reflexivity.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort' in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh2 with (1 := hext). destruct IHh2 as [B' [s'' hB]].
    eapply tr_sort' in hB. 2: apply hext.
    destruct hctx.
    eexists (Pi i j m mx A' B'), _.
    eapply tr_pi. all: eassumption.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort' in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh2 with (1 := hext). destruct IHh2 as [B' [s'' hB]].
    eapply tr_sort' in hB. 2: apply hext.
    specialize IHh3 with (1 := hext). destruct IHh3 as [t' [B'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (lam mx A' B' t'), _. split.
    + eapply type_lam. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh3 with (1 := hctx). destruct IHh3 as [A' [s' hA]].
    eapply tr_sort' in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh4 with (1 := hext). destruct IHh4 as [B' [s'' hB]].
    eapply tr_sort' in hB. 2: apply hext.
    eapply tr_pi in hB as hPi. 2: apply hctx. 2: eassumption.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [P' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [u' [A'' hu]].
    eapply tr_choice in hu. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (app t' u'), _. split.
    + eapply type_app. all: eassumption.
    + cbn. intuition eauto.
      rewrite castrm_subst. ssimpl. reflexivity.
Abort.

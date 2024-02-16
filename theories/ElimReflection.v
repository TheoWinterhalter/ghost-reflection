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

Lemma tr_bot :
  ∀ Γ', Γ' ⊨ bot : (Sort mProp 0) ∈ ⟦ bot : (Sort mProp 0) ⟧x.
Proof.
  intros Γ'.
  split.
  - eapply type_bot.
  - cbn. intuition reflexivity.
Qed.

Lemma tr_erased :
  ∀ A i Γ' A',
    wf Γ' →
    Γ' ⊨ A' : (Sort mType i) ∈ ⟦ A : (Sort mType i) ⟧x →
    Γ' ⊨ (Erased A') : (Sort mGhost i) ∈ ⟦ (Erased A) : (Sort mGhost i) ⟧x.
Proof.
  intros A i Γ' A' hΓ h.
  unfold tr_ty in *. intuition subst.
  - eapply type_erased. all: eassumption.
  - cbn. intuition reflexivity.
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
  all: try solve [ econstructor ; eauto ].
  all: try solve [ rewrite ?e in * ; econstructor ; eauto ].
  - econstructor. all: eauto.
    eapply IHh2. cbn. f_equal. assumption.
  - econstructor. all: eauto.
    + eapply IHh2. cbn. f_equal. assumption.
    + eapply IHh3. cbn. f_equal. assumption.
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
    eapply tr_sort_inv in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh2 with (1 := hext). destruct IHh2 as [B' [s'' hB]].
    eapply tr_sort_inv in hB. 2: apply hext.
    destruct hctx.
    eexists (Pi i j m mx A' B'), _.
    eapply tr_pi. all: eassumption.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh2 with (1 := hext). destruct IHh2 as [B' [s'' hB]].
    eapply tr_sort_inv in hB. 2: apply hext.
    specialize IHh3 with (1 := hext). destruct IHh3 as [t' [B'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (lam mx A' B' t'), _. split.
    + eapply type_lam. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh3 with (1 := hctx). destruct IHh3 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh4 with (1 := hext). destruct IHh4 as [B' [s'' hB]].
    eapply tr_sort_inv in hB. 2: apply hext.
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
  - specialize IHh with (1 := hctx). destruct IHh as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    destruct hctx.
    eexists (Erased A'), _. eapply tr_erased. all: eassumption.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [t' [A'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (hide t'), _. split.
    + eapply type_hide. all: eassumption.
    + cbn. intuition reflexivity.
  - specialize IHh4 with (1 := hctx). destruct IHh4 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [E' ht]].
    eapply tr_choice in ht. 2: apply hctx. 2: eassumption.
    2:{ destruct hctx. eapply tr_erased. all: eassumption. }
    specialize IHh2 with (1 := hctx). destruct IHh2 as [P' [T' hP]].
    eapply tr_choice in hP. 2: apply hctx. 2: eassumption.
    2:{
      destruct hctx.
      eapply tr_pi.
      - assumption.
      - eapply tr_erased. all: eassumption.
      - cbn. (* TODO It would be good to use tr_sort as a name for this *)
        admit.
    }
    admit.
  - admit.
  - admit.
  - admit.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [u' [A'' hu]].
    eapply tr_choice in hu. 2-4: eassumption.
    specialize IHh3 with (1 := hctx). destruct IHh3 as [v' [A''' hv]].
    eapply tr_choice in hv. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (gheq A' u' v'), _. split.
    + eapply type_gheq. all: eassumption.
    + cbn. intuition reflexivity.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [u' [A'' hu]].
    eapply tr_choice in hu. 2-4: eassumption.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (ghrefl A' u'), _. split.
    + eapply type_ghrefl. all: eassumption.
    + cbn. intuition reflexivity.
  - eexists bot, _. apply tr_bot.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [p' [b' hp]].
    eapply tr_choice in hp. 2: apply hctx. 2: eassumption. 2: apply tr_bot.
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (bot_elim m A' p'), _. split.
    + eapply type_bot_elim. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh2 with (1 := hctx). destruct IHh2 as [B' [s' hB]].
    eapply tr_sort_inv in hB. 2: apply hctx.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [A' ht]].
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists t', _. split.
    + eapply type_conv. all: eauto.
      * eapply tr_scoping. all: eassumption.
      * eapply conv_upto. 1: eassumption.
        apply sc_rmctx.
    + intuition reflexivity.
  - admit.
Abort.

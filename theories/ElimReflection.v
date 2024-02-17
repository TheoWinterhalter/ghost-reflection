(*** Translation from GRTT to GTT ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory Admissible RTyping
  Potential Model.
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

Lemma tr_sort :
  ∀ Γ' m i,
    Γ' ⊨ (Sort m i) : (Sort mKind (usup m i)) ∈
    ⟦ (Sort m i) : (Sort mKind (usup m i)) ⟧x.
Proof.
  intros Γ' m i.
  split.
  - eapply type_sort.
  - intuition reflexivity.
Qed.

Lemma tr_sort_lax :
  ∀ Γ' m i j,
    j = usup m i →
    Γ' ⊨ (Sort m i) : (Sort mKind j) ∈
    ⟦ (Sort m i) : (Sort mKind j) ⟧x.
Proof.
  intros Γ' m i ? ->.
  apply tr_sort.
Qed.

Lemma tr_app :
  ∀ i j m mx A B t u Γ' A' B' t' u',
    wf Γ' →
    Γ' ⊨ t' : (Pi i j m mx A' B') ∈ ⟦ t : (Pi i j m mx A B) ⟧x →
    Γ' ⊨ u' : A' ∈ ⟦ u : A ⟧x →
    Γ' ⊨ (app t' u') : (B' <[ u' .. ]) ∈ ⟦ (app t u) : (B <[ u .. ]) ⟧x.
Proof.
  intros i j m mx A B t u Γ' A' B' t' u' hΓ ht hu.
  destruct ht as [ht [et ePi]]. cbn in ePi. inversion ePi.
  destruct hu. intuition subst.
  split.
  + eapply type_app. all: eassumption.
  + intuition eauto. rewrite castrm_subst. ssimpl. reflexivity.
Qed.

Lemma tr_app_lax :
  ∀ i j m mx A B t u Γ' A' B' t' u' C C',
    wf Γ' →
    Γ' ⊨ t' : (Pi i j m mx A' B') ∈ ⟦ t : (Pi i j m mx A B) ⟧x →
    Γ' ⊨ u' : A' ∈ ⟦ u : A ⟧x →
    C = B <[ u .. ] →
    C' = B' <[ u' .. ] →
    Γ' ⊨ (app t' u') : C' ∈ ⟦ (app t u) : C ⟧x.
Proof.
  intros i j m mx A B t u Γ' A' B' t' u' ? ? hΓ ht hu -> ->.
  eapply tr_app. all: eassumption.
Qed.

Lemma tr_ren :
  ∀ Γ Δ t A t' A' ρ,
    rtyping Δ ρ Γ →
    Γ ⊨ t' : A' ∈ ⟦ t : A ⟧x →
    Δ ⊨ (ρ ⋅ t') : (ρ ⋅ A') ∈ ⟦ (ρ ⋅ t) : (ρ ⋅ A) ⟧x.
Proof.
  intros Γ Δ t A t' A' ρ hρ [ht [-> ->]].
  split.
  - eapply typing_ren. all: eassumption.
  - rewrite !castrm_ren. intuition reflexivity.
Qed.

Lemma tr_ren_lax :
  ∀ Γ Δ t A t' A' ρ rA rA',
    rtyping Δ ρ Γ →
    Γ ⊨ t' : A' ∈ ⟦ t : A ⟧x →
    rA = ρ ⋅ A →
    rA' = ρ ⋅ A' →
    Δ ⊨ (ρ ⋅ t') : rA' ∈ ⟦ (ρ ⋅ t) : rA ⟧x.
Proof.
  intros Γ Δ t A t' A' ρ ?? hρ ht -> ->.
  eapply tr_ren. all: eassumption.
Qed.

Lemma tr_hide :
  ∀ i A t Γ' A' t',
    wf Γ' →
    Γ' ⊨ A' : (Sort mType i) ∈ ⟦ A : (Sort mType i) ⟧x →
    Γ' ⊨ t' : A' ∈ ⟦ t : A ⟧x →
    Γ' ⊨ (hide t') : (Erased A') ∈ ⟦ (hide t) : (Erased A) ⟧x.
Proof.
  intros i A t Γ' A' t' hΓ hA ht.
  unfold tr_ctx, tr_ty in *. intuition subst. 2,3: reflexivity.
  eapply type_hide. all: eassumption.
Qed.

Lemma tr_var :
  ∀ Γ' x m A A',
    nth_error Γ' x = Some (m, A') →
    A = plus (S x) ⋅ ε| A'| →
    Γ' ⊨ (var x) : (plus (S x) ⋅ A') ∈ ⟦ (var x) : A ⟧x.
Proof.
  intros Γ' x m A A' hx ->.
  split.
  - econstructor. eassumption.
  - intuition eauto.
    rewrite castrm_ren. reflexivity.
Qed.

Lemma tr_Reveal :
  ∀ i A t p Γ' A' t' p',
    wf Γ' →
    Γ' ⊨ A' : (Sort mType i) ∈ ⟦ A : (Sort mType i) ⟧x →
    Γ' ⊨ t' : (Erased A') ∈ ⟦ t : (Erased A) ⟧x →
    Γ' ⊨ p' : (Pi i 0 mKind mType A' (Sort mProp 0)) ∈
    ⟦ p : (A ⇒[ i | 0 / mType | mKind] Sort mProp 0) ⟧x →
    Γ' ⊨ (Reveal t' p') : (Sort mProp 0) ∈ ⟦ (Reveal t p) : (Sort mProp 0) ⟧x.
Proof.
  intros i A t p Γ' A' t' p' hΓ hA ht hp.
  unfold tr_ctx, tr_ty in *. intuition subst.
  - eapply type_Reveal. all: eassumption.
  - cbn. intuition reflexivity.
Qed.

Lemma tr_gheq :
  ∀ i A u v Γ' A' u' v',
    wf Γ' →
    Γ' ⊨ A' : (Sort mGhost i) ∈ ⟦ A : (Sort mGhost i) ⟧x →
    Γ' ⊨ u' : A' ∈ ⟦ u : A ⟧x →
    Γ' ⊨ v' : A' ∈ ⟦ v : A ⟧x →
    Γ' ⊨ (gheq A' u' v') : (Sort mProp 0) ∈ ⟦ (gheq A u v) : (Sort mProp 0) ⟧x.
Proof.
  intros i A u v Γ' A' u' v' hΓ hA hu hv.
  unfold tr_ctx, tr_ty in *. intuition subst.
  - eapply type_gheq. all: eassumption.
  - cbn. reflexivity.
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
    eexists (var x), _. eapply tr_var. all: eauto.
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
    destruct hctx.
    eexists (app t' u'), _. eapply tr_app. all: eauto.
  - specialize IHh with (1 := hctx). destruct IHh as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    destruct hctx.
    eexists (Erased A'), _. eapply tr_erased. all: eassumption.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [t' [A'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    destruct hctx.
    eexists (hide t'), _. eapply tr_hide. all: eassumption.
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
      - cbn. eapply tr_sort.
    }
    eapply tr_cons in hA as hext. 2: eassumption.
    specialize IHh3 with (1 := hctx). destruct IHh3 as [p' [Pi' hp]].
    eapply tr_choice in hp. 2: apply hctx. 2: eassumption.
    2:{
      destruct hctx, hext.
      eapply tr_pi.
      - assumption.
      - eassumption.
      - eapply tr_app_lax.
        + eassumption.
        + eapply tr_ren_lax. 1: eapply rtyping_S.
          1: eassumption.
          all: cbn. all: reflexivity.
        + eapply tr_hide.
          * assumption.
          * eapply tr_ren_lax. 1: eapply rtyping_S.
            1: eassumption.
            all: reflexivity.
          * eapply tr_var. 1: reflexivity.
            cbn. destruct hA. intuition subst. reflexivity.
        + reflexivity.
        + reflexivity.
    }
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (reveal t' P' p'), _. split.
    + eapply type_reveal. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh3 with (1 := hctx). destruct IHh3 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [E' ht]].
    eapply tr_choice in ht. 2,3: eassumption.
    2:{ destruct hctx. eapply tr_erased. all: eauto. }
    specialize IHh2 with (1 := hctx). destruct IHh2 as [p' [T' hp]].
    eapply tr_choice in hp. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_pi.
      - assumption.
      - eassumption.
      - cbn. eapply tr_sort.
    }
    destruct hctx.
    eexists (Reveal t' p'), _. eapply tr_Reveal. all: eassumption.
  - specialize IHh4 with (1 := hctx). destruct IHh4 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [A'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [p' [T' hp]].
    eapply tr_choice in hp. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_pi.
      - assumption.
      - eassumption.
      - cbn. eapply tr_sort.
    }
    specialize IHh3 with (1 := hctx). destruct IHh3 as [u' [P' hu]].
    eapply tr_choice in hu. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_app_lax.
      - assumption.
      - eassumption.
      - eassumption.
      - cbn. reflexivity.
      - reflexivity.
    }
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (toRev t' p' u'), _. split.
    + eapply type_toRev. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh4 with (1 := hctx). destruct IHh4 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh1 with (1 := hctx). destruct IHh1 as [t' [A'' ht]].
    eapply tr_choice in ht. 2-4: eassumption.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [p' [T' hp]].
    eapply tr_choice in hp. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_pi.
      - assumption.
      - eassumption.
      - cbn. eapply tr_sort.
    }
    specialize IHh3 with (1 := hctx). destruct IHh3 as [u' [P' hu]].
    eapply tr_choice in hu. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_Reveal. all: eauto.
      eapply tr_hide. all: eauto.
    }
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (fromRev t' p' u'), _. split.
    + eapply type_fromRev. all: eauto.
    + cbn. intuition reflexivity.
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [u' [A'' hu]].
    eapply tr_choice in hu. 2-4: eassumption.
    specialize IHh3 with (1 := hctx). destruct IHh3 as [v' [A''' hv]].
    eapply tr_choice in hv. 2-4: eassumption.
    destruct hctx.
    eexists (gheq A' u' v'), _. eapply tr_gheq. all: eassumption.
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
  - specialize IHh1 with (1 := hctx). destruct IHh1 as [A' [s' hA]].
    eapply tr_sort_inv in hA. 2: apply hctx.
    specialize IHh2 with (1 := hctx). destruct IHh2 as [u' [A'' hu]].
    eapply tr_choice in hu. 2-4: eassumption.
    specialize IHh3 with (1 := hctx). destruct IHh3 as [v' [A''' hv]].
    eapply tr_choice in hv. 2-4: eassumption.
    specialize IHh4 with (1 := hctx). destruct IHh4 as [e' [E' he]].
    eapply tr_choice in he. 2,3: eassumption.
    2:{ destruct hctx. eapply tr_gheq. all: eassumption. }
    specialize IHh5 with (1 := hctx). destruct IHh5 as [P' [T' hP]].
    eapply tr_choice in hP. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_pi. all: eauto.
      cbn. eapply tr_sort.
    }
    specialize IHh6 with (1 := hctx). destruct IHh6 as [t' [T'' ht]].
    eapply tr_choice in ht. 2,3: eassumption.
    2:{
      destruct hctx.
      eapply tr_app_lax. all: eauto. all: reflexivity.
    }
    unfold tr_ctx, tr_ty in *. intuition subst.
    eexists (ghcast A' u' v' e' P' t'), _. split.
    + eapply type_ghcast. all: eassumption.
    + cbn. intuition reflexivity.
Qed.

(** Conservativity **)

Theorem conservativity :
  ∀ A m i t,
    [] ⊢ A : Sort m i →
    [] ⊢ˣ t : ε|A| →
    cscoping [] t m →
    ∑ t', [] ⊢ t' : A ∧ t = ε|t'|.
Proof.
  intros A m i t hA ht hmt.
  eapply elim_reflection in ht.
  2:{ split. 1: constructor. reflexivity. }
  destruct ht as [t' [A' [ht' [et eA]]]].
  exists t'. intuition eauto.
  eapply type_conv. all: eauto.
  - constructor.
  - subst.
    eapply tr_scoping. all: eauto.
    constructor.
  - rewrite <- eA. apply conv_refl.
Qed.

(** Consistency (relative to CC again) **)

Definition grtt_consistency :=
  ∀ t, [] ⊢ˣ t : bot → False.

Theorem consistency :
  cc_consistency →
  grtt_consistency.
Proof.
  intros h t ht.
  eapply relative_consistency in h. eapply h.
  eapply elim_reflection in ht.
  2:{ split. 1: constructor. reflexivity. }
  destruct ht as [t' [b' ht]].
  eapply tr_bot_eq in ht as e. 2: constructor.
  subst.
  exists t'. apply ht.
Qed.

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival.
From Coq Require Import Setoid Morphisms Relation_Definitions.
From GhostTT.param Require Export Term Scope.
From GhostTT.param Require Import Conversion.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
(** Parametricity ignores casts **)

Lemma ccong_pmPi :
  ∀ Γ mx m Te Ae Ap Bp Te' Ae' Ap' Bp',
    Γ ⊢ᶜ Te ≡ Te' →
    Γ ⊢ᶜ Ae ≡ Ae' →
    Γ ⊢ᶜ Ap ≡ Ap' →
    let Γ' :=
      if isProp mx then
        None :: Some (cProp, Ap) :: Γ
      else if isKind mx then
        Some (cType, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, Ae) :: Γ
      else
        Some (cProp, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, Ae) :: Γ
    in
    Γ' ⊢ᶜ Bp ≡ Bp' →
    Γ ⊢ᶜ pmPi mx m Te Ae Ap Bp ≡ pmPi mx m Te' Ae' Ap' Bp'.
Proof.
  cbn zeta.
  intros Γ mx m Te Ae Ap Bp Te' Ae' Ap' Bp' hTe hAe hAp hBp.
  unfold pmPi. destruct (isProp m) eqn:ep.
  - unfold pmPiP. destruct_ifs. all: econv.
    all: try apply crtyping_S.
    apply cstyping_one_none.
  - unfold pmPiNP. econv.
    destruct (isProp mx) eqn:epx. all: econv.
    all: try apply crtyping_S.
    + eapply crtyping_shift. apply crtyping_S.
    + eapply cstyping_one_none.
    + destruct (isKind mx) eqn:ekx.
      * {
        eapply crtyping_shift_eq.
        - eapply crtyping_shift. apply crtyping_S.
        - f_equal. f_equal. f_equal. cbn. ssimpl. reflexivity.
      }
      * {
        eapply crtyping_shift_eq.
        - eapply crtyping_shift. apply crtyping_S.
        - f_equal. f_equal. f_equal. cbn. ssimpl. reflexivity.
      }
Qed.

Hint Opaque pmPi : cc_conv.
Hint Resolve ccong_pmPi : cc_conv.

Lemma meta_ctx_conv_conv :
  ∀ Γ Δ u v,
    Γ ⊢ᶜ u ≡ v →
    Γ = Δ →
    Δ ⊢ᶜ u ≡ v.
Proof.
  intros Γ ? u v h ->.
  assumption.
Qed.

Lemma meta_ctx_param_conv :
  ∀ sΓ Γp sΔ Δp u v,
    Δp ⊢ᶜ ⟦ sΔ | u ⟧p ≡ ⟦ sΔ | v ⟧p →
    Γp = Δp →
    sΓ = sΔ →
    Γp ⊢ᶜ ⟦ sΓ | u ⟧p ≡ ⟦ sΓ | v ⟧p.
Proof.
  intros sΓ Γp sΔ Δp u v h -> ->.
  assumption.
Qed.

Hint Opaque plam : cc_conv.

Lemma meta_ccscoping_conv :
  ∀ Γ t m m',
    ccscoping Γ t m →
    m = m' →
    ccscoping Γ t m'.
Proof.
  intros Γ t m m' h ->.
  assumption.
Qed.

Lemma param_castrm :
  ∀ Γ t m,
    cscoping Γ t m →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | (ε|t|) ⟧p ≡ ⟦ sc Γ | t ⟧p.
Proof.
  intros Δ t m h.
  remember (sc Δ) as Γ eqn:e in *.
  induction h in Δ, e |- *.
  all: try solve [ econv ].
  all: try solve [
    cbn  ; rewrite <- ?md_castrm ;
    rewrite ?erase_castrm, ?revive_castrm ;
    destruct_ifs ; econv
  ].
  - cbn. rewrite !erase_castrm. econv.
    subst.
    eapply meta_ctx_conv_conv.
    + eapply IHh2 with (Δ := Δ ,, (mx, ε|A|)).
      reflexivity.
    + cbn. rewrite !erase_castrm. reflexivity.
  - cbn. rewrite !erase_castrm.
    destruct_ifs.
    + econstructor. 1: eauto.
      eapply cconv_close.
      eapply meta_ctx_conv_conv.
      * eapply IHh2 with (Δ := Δ ,, (mx, ε|A|)).
        subst. reflexivity.
      * cbn. subst. rewrite !erase_castrm. rewrite e0. reflexivity.
    + econv.
      eapply meta_ctx_conv_conv.
      * eapply IHh2 with (Δ := Δ ,, (mx, ε|A|)).
        subst. reflexivity.
      * cbn. subst. rewrite !erase_castrm. rewrite e0,e1. reflexivity.
    + econv.
      eapply meta_ctx_conv_conv.
      * eapply IHh2 with (Δ := Δ ,, (mx, ε|A|)).
        subst. reflexivity.
      * cbn. subst. rewrite !erase_castrm. rewrite e0,e1. reflexivity.
  - eapply cconv_trans. 1:{ eapply IHh6. eassumption. }
    destruct (isKind m) eqn:ek. 1:{ mode_eqs. contradiction. }
    subst.
    apply cconv_irr.
    + eapply param_scoping in h6. rewrite ek in h6.
      rewrite <- csc_param_ctx in h6. assumption.
    + rewrite csc_param_ctx. eapply meta_ccscoping_conv.
      * eapply param_scoping. constructor. all: eassumption.
      * rewrite ek. reflexivity.
  - cbn. rewrite !erase_castrm, !revive_castrm.
    destruct m.
    + eapply ccong_pmifK. all: eauto. all: econv.
    + eapply ccong_pmif. all: eauto. all: econv.
    + eapply ccong_pmif. all: eauto. all: econv.
    + econv.
  - cbn. rewrite !erase_castrm, !revive_castrm.
    destruct m.
    + contradiction.
    + econv.
    + econv.
    + econv.
  - cbn. rewrite !erase_castrm, !revive_castrm.
    destruct m.
    + contradiction.
    + econv.
    + econv.
    + econv.
Qed.

Lemma param_castrm_conv :
  ∀ Γ u v mu mv,
    cscoping Γ u mu →
    cscoping Γ v mv →
    Γ ⊢ u ε≡ v →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | u ⟧p ≡ ⟦ sc Γ | v ⟧p.
Proof.
  intros Γ u v mu mv hu hv h.
  eapply param_conv in h.
  eapply cconv_trans.
  - apply cconv_sym. eapply param_castrm. eassumption.
  - eapply cconv_trans. 1: eassumption.
    eapply param_castrm. eassumption.
Qed.


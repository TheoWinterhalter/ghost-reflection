From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival.
From Coq Require Import Setoid Morphisms Relation_Definitions.
From GhostTT.param Require Export Term Scope.
From GhostTT.param Require Import Renaming Substitution.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.


(** Parametricity preserves conversion **)

Lemma vreg_vpar_dec :
  ∀ n, { n = vpar (Nat.div2 n) } + { n = vreg (Nat.div2 n) }.
Proof.
  intros n.
  destruct (PeanoNat.Nat.Even_Odd_dec n).
  - left. unfold vpar.
    etransitivity.
    + apply PeanoNat.Nat.Even_double. assumption.
    + unfold Nat.double. lia.
  - right. unfold vreg.
    etransitivity.
    + apply PeanoNat.Nat.Odd_double. assumption.
    + unfold Nat.double. lia.
Qed.

Lemma ccong_pPi :
  ∀ Γ mx A B C A' B' C',
    Γ ⊢ᶜ A ≡ A' →
    Γ ⊢ᶜ B ≡ B' →
    Some (mx, capp (S ⋅ B) (cvar 0)) :: Some (cType, A) :: Γ ⊢ᶜ C ≡ C' →
    Γ ⊢ᶜ pPi mx A B C ≡ pPi mx A' B' C'.
Proof.
  intros Γ mx A B C A' B' C' hA hB hC.
  unfold pPi.
  econv.
  eapply cconv_ren. 2: eassumption.
  apply crtyping_S.
Qed.

Hint Resolve ccong_pPi : cc_conv.

Lemma ccong_plam :
  ∀ Γ mp A B t A' B' t',
    Γ ⊢ᶜ A ≡ A' →
    Γ ⊢ᶜ B ≡ B' →
    Some (mp, capp (S ⋅ B) (cvar 0)) :: Some (cType, A) :: Γ ⊢ᶜ t ≡ t' →
    Γ ⊢ᶜ plam mp A B t ≡ plam mp A' B' t'.
Proof.
  intros Γ mp A B t A' B' t' hA hB ht.
  econv.
  eapply cconv_ren. 2: eassumption.
  apply crtyping_S.
Qed.

Hint Resolve ccong_plam : cc_conv.

Transparent epm_lift rpm_lift.

Lemma ccong_epm_lift :
  ∀ Γ Γ' t t',
    ⟦ Γ ⟧ε ⊢ᶜ t ≡ t' →
    Γ' = ⟦ Γ ⟧p →
    Γ' ⊢ᶜ epm_lift t ≡ epm_lift t'.
Proof.
  intros Γ Γ' t t' ht ->.
  unfold epm_lift. eapply cconv_ren.
  - apply typing_er_sub_param.
  - assumption.
Qed.

Lemma ccong_rpm_lift :
  ∀ Γ Γ' t t',
    ⟦ Γ ⟧v ⊢ᶜ t ≡ t' →
    Γ' = ⟦ Γ ⟧p →
    Γ' ⊢ᶜ rpm_lift t ≡ rpm_lift t'.
Proof.
  intros Γ Γ' t t' ht ->.
  unfold rpm_lift. eapply cconv_ren.
  - apply typing_rev_sub_param.
  - assumption.
Qed.

(* Need to have them opaque so that they can't be confused. *)
Hint Opaque epm_lift rpm_lift : cc_scope cc_conv cc_type.
Hint Resolve ccong_epm_lift ccong_rpm_lift : cc_conv.

Opaque epm_lift rpm_lift.

Hint Resolve cconv_ren cconv_subst : cc_conv.

Lemma erase_conv_eq :
  ∀ Γ Γ' Γ'' u v,
    Γ ⊢ u ≡ v →
    Γ' = ⟦ Γ ⟧ε →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | u ⟧ε ≡ ⟦ Γ'' | v ⟧ε.
Proof.
  intros Γ Γ' Γ'' u v h -> ->.
  apply erase_conv. assumption.
Qed.

Hint Resolve erase_conv_eq : cc_conv.

Lemma revive_conv_eq :
  ∀ Γ Γ' Γ'' u v,
    Γ ⊢ u ≡ v →
    Γ' = ⟦ Γ ⟧v →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | u ⟧v ≡ ⟦ Γ'' | v ⟧v.
Proof.
  intros Γ Γ' Γ'' u v h -> ->.
  apply revive_conv. assumption.
Qed.

Hint Resolve revive_conv_eq : cc_conv.

Lemma crtyping_shift_eq :
  ∀ Γ Δ Ξ mx A ρ,
    crtyping Γ ρ Δ →
    Ξ = Some (mx, ρ ⋅ A) :: Γ →
    crtyping Ξ (up_ren ρ) (Some (mx, A) :: Δ).
Proof.
  intros Γ Δ Ξ mx A ρ hρ ->.
  apply crtyping_shift. assumption.
Qed.

Lemma csc_param_ctx :
  ∀ Γ,
    csc ⟦ Γ ⟧p = param_sc (sc Γ).
Proof.
  intros Γ.
  induction Γ as [| [m A] Γ ih].
  - cbn. reflexivity.
  - cbn. destruct_ifs. all: cbn.
    + f_equal. f_equal. apply ih.
    + f_equal. f_equal. apply ih.
    + f_equal. f_equal. apply ih.
Qed.

Lemma ccong_perif :
  ∀ Γ be be' Pe Pe' te te' fe fe',
    Γ ⊢ᶜ be ≡ be' →
    Γ ⊢ᶜ Pe ≡ Pe' →
    Γ ⊢ᶜ te ≡ te' →
    Γ ⊢ᶜ fe ≡ fe' →
    Γ ⊢ᶜ perif be Pe te fe ≡ perif be' Pe' te' fe'.
Proof.
  intros Γ be be' Pe Pe' te te' fe fe' hb hP ht hf.
  unfold perif. econv. apply crtyping_S.
Qed.

Hint Opaque perif : cc_conv.
Hint Resolve ccong_perif : cc_conv.

Lemma ccong_pmif :
  ∀ Γ bP Pe PP te tP fe fP bP' Pe' PP' te' tP' fe' fP',
    Γ ⊢ᶜ bP ≡ bP' →
    Γ ⊢ᶜ Pe ≡ Pe' →
    Γ ⊢ᶜ PP ≡ PP' →
    Γ ⊢ᶜ te ≡ te' →
    Γ ⊢ᶜ tP ≡ tP' →
    Γ ⊢ᶜ fe ≡ fe' →
    Γ ⊢ᶜ fP ≡ fP' →
    Γ ⊢ᶜ pmif bP Pe PP te tP fe fP ≡ pmif bP' Pe' PP' te' tP' fe' fP'.
Proof.
  intros Γ bP Pe PP te tP fe fP bP' Pe' PP' te' tP' fe' fP'.
  intros hbP hPe hPP hte htP hfe hfP.
  unfold pmif. econv. all: apply crtyping_S.
Qed.

Hint Opaque pmif : cc_conv.
Hint Resolve ccong_pmif : cc_conv.

Lemma ccong_pmifK :
  ∀ Γ be bP Pe PP te tP fe fP be' bP' Pe' PP' te' tP' fe' fP',
    Γ ⊢ᶜ be ≡ be' →
    Γ ⊢ᶜ bP ≡ bP' →
    Γ ⊢ᶜ Pe ≡ Pe' →
    Γ ⊢ᶜ PP ≡ PP' →
    Γ ⊢ᶜ te ≡ te' →
    Γ ⊢ᶜ tP ≡ tP' →
    Γ ⊢ᶜ fe ≡ fe' →
    Γ ⊢ᶜ fP ≡ fP' →
    Γ ⊢ᶜ pmifK be bP Pe PP te tP fe fP ≡ pmifK be' bP' Pe' PP' te' tP' fe' fP'.
Proof.
  intros Γ be bP Pe PP te tP fe fP be' bP' Pe' PP' te' tP' fe' fP'.
  intros hbe hbP hPe hPP hte htP hfe hfP.
  unfold pmifK. econv. all: apply crtyping_S.
Qed.

Hint Opaque pmifK : cc_conv.
Hint Resolve ccong_pmifK : cc_conv.

Lemma pren_S :
  ∀ n, pren S n = S (S n).
Proof.
  intro n.
  change (pren S n) with (pren (id >> S) n).
  rewrite pren_comp_S. rewrite pren_id. reflexivity.
Qed.

Lemma pren_S_pw :
  pointwise_relation _ eq (pren S) (S >> S).
Proof.
  intro n. apply pren_S.
Qed.

Lemma param_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | u ⟧p ≡ ⟦ sc Γ | v ⟧p.
Proof.
  intros Γ u v h.
  induction h.
  (* all: try solve [ cbn ; destruct_ifs ; eauto with cc_conv ]. *)
  - cbn.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs. all: try discriminate.
    + eapply cconv_trans.
      1:{ constructor. 2: apply cconv_refl. constructor. }
      cbn.
      eapply cconv_trans. 1: constructor.
      ssimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1:{ eapply param_scoping. eassumption. }
      (* The following we do basically four times, but we don't know how
        to factorise.
      *)
      intros [| []] hx. all: cbn. 1,2: reflexivity.
      unfold inscope in hx. cbn in hx.
      unfold psubst. rewrite div2_SS. cbn.
      destruct (vreg_vpar_dec n) as [en | en].
      * rewrite en in hx. rewrite nth_error_param_vpar in hx.
        destruct nth_error as [mx|] eqn:e1. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        1:{ rewrite en in eodd. rewrite odd_vpar in eodd. discriminate. }
        destruct (isProp mx) eqn:e2. 1: discriminate.
        destruct (isKind mx) eqn:e3. all: mode_eqs.
        -- cbn. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. f_equal. assumption.
          ++ cbn. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:e1. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e2.
        -- mode_eqs. cbn. f_equal. assumption.
        -- unfold relv, ghv. rewrite e1.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + destruct (isType mx) eqn:e2. 2:{ destruct mx. all: discriminate. }
      mode_eqs.
      eapply cconv_trans.
      1:{ constructor. 2: apply cconv_refl. constructor. }
      cbn.
      eapply cconv_trans. 1: constructor.
      ssimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1:{ eapply param_scoping. eassumption. }
      (* Basically same as above, is there a nice lemma to state? *)
      intros [| []] hx. all: cbn. 1,2: reflexivity.
      unfold inscope in hx. cbn in hx.
      unfold psubst. rewrite div2_SS. cbn.
      destruct (vreg_vpar_dec n) as [en | en].
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vpar in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        1:{ rewrite en in eodd. rewrite odd_vpar in eodd. discriminate. }
        destruct (isProp mx) eqn:e2. 1: discriminate.
        destruct (isKind mx) eqn:e3. all: mode_eqs.
        -- cbn. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. f_equal. assumption.
          ++ cbn. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e2.
        -- mode_eqs. cbn. f_equal. assumption.
        -- unfold relv, ghv. rewrite emx.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + eapply cconv_trans.
      1:{ constructor. 2: apply cconv_refl. constructor. }
      cbn.
      eapply cconv_trans. 1: constructor.
      ssimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1:{ eapply param_scoping. eassumption. }
      (* Basically same as above, is there a nice lemma to state? *)
      intros [| []] hx. all: cbn. 1,2: reflexivity.
      unfold inscope in hx. cbn in hx.
      unfold psubst. rewrite div2_SS. cbn.
      destruct (vreg_vpar_dec n) as [en | en].
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vpar in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        1:{ rewrite en in eodd. rewrite odd_vpar in eodd. discriminate. }
        destruct (isProp mx) eqn:e3. 1: discriminate.
        destruct (isKind mx) eqn:e4. all: mode_eqs.
        -- cbn. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. f_equal. assumption.
          ++ cbn. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e3.
        -- mode_eqs. cbn. f_equal. assumption.
        -- unfold relv, ghv. rewrite emx.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + eapply cconv_trans. 1: constructor.
      unfold close. ssimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1:{ eapply param_scoping. eassumption. }
      (* Basically same as above, is there a nice lemma to state? *)
      intros [| []] hx. all: cbn. 1,2: reflexivity.
      unfold inscope in hx. cbn in hx.
      unfold psubst. rewrite div2_SS. cbn.
      destruct (vreg_vpar_dec n) as [en | en].
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vpar in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        1:{ rewrite en in eodd. rewrite odd_vpar in eodd. discriminate. }
        destruct (isProp mx) eqn:e3. 1: discriminate.
        destruct (isKind mx) eqn:e4. all: mode_eqs.
        -- cbn. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. f_equal. assumption.
          ++ cbn. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e3.
        -- mode_eqs. cbn. f_equal. assumption.
        -- unfold relv, ghv. rewrite emx.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + destruct mx. all: discriminate.
  - cbn.
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    destruct_if e.
    1:{
      destruct H2 as [emp | [ emp | ]]. 3: contradiction.
      all: subst. all: discriminate.
    }
    cbn. apply cconv_refl.
  - cbn. destruct m.
    + unfold pmifK. change (epm_lift etrue) with etrue.
      eapply cconv_trans.
      1:{
        econstructor. 2: econv.
        constructor.
      }
      eapply cconv_trans. 1: constructor.
      ssimpl. econv.
    + unfold pmif. constructor.
    + unfold pmif. constructor.
    + constructor.
  - cbn. destruct m.
    + unfold pmifK. change (epm_lift etrue) with etrue.
      eapply cconv_trans.
      1:{
        econstructor. 2: econv.
        constructor.
      }
      eapply cconv_trans. 1: constructor.
      ssimpl. econv.
    + unfold pmif. constructor.
    + unfold pmif. constructor.
    + constructor.
  - cbn. eapply param_scoping in H0, H1, H2.
    rewrite <- csc_param_ctx in H0, H1, H2.
    destruct m.
    + contradiction.
    + cbn in *.
      eapply cconv_irr.
      * escope. all: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. apply csc_param_ctx.
      * assumption.
    + cbn in *.
      eapply cconv_irr.
      * escope. all: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. apply csc_param_ctx.
      * assumption.
    + cbn in *.
      eapply cconv_irr.
      * escope. 2: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. apply csc_param_ctx.
      * assumption.
  - cbn.
    remd.
    eapply param_scoping in H0, H1, H2, H3.
    rewrite <- csc_param_ctx in H0, H1, H2, H3.
    destruct m.
    + contradiction.
    + cbn in *.
      eapply cconv_irr.
      * escope. all: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. 1: reflexivity.
        apply csc_param_ctx.
      * escope. all: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope.
        all: try reflexivity.
        apply csc_param_ctx.
    + cbn in *.
      eapply cconv_irr.
      * escope. all: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. 1: reflexivity.
        apply csc_param_ctx.
      * {
        escope. all: eauto using csc_param_ctx.
        eapply scoping_rpm_lift. 2: apply csc_param_ctx.
        econstructor.
        1,2: eapply scoping_to_rev.
        all: escope. all: reflexivity.
      }
    + cbn in *.
      eapply cconv_irr.
      * escope. 2: eauto using csc_param_ctx.
        eapply scoping_epm_lift. 1: escope. 1: reflexivity.
        apply csc_param_ctx.
      * escope. all: eauto using csc_param_ctx.
  - cbn. eapply param_scoping in H0, H1, H2, H3, H4.
    rewrite <- csc_param_ctx in H0, H1, H2, H3, H4.
    destruct m.
    + contradiction.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        - change (rpm_lift ?t) with t. escope.
        - change (epm_lift ?t) with (vreg ⋅ t). cbn.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          escope. apply csc_param_ctx.
      }
      * auto.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        - change (rpm_lift ?t) with t. escope.
        - change (epm_lift ?t) with (vreg ⋅ t). cbn.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          escope. apply csc_param_ctx.
      }
      * auto.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        - change (rpm_lift ?t) with t. escope.
        - change (epm_lift ?t) with (vreg ⋅ t). cbn.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          escope. apply csc_param_ctx.
      }
      * auto.
  - simpl. remd.
    eapply param_scoping in H0, H1, H2, H3, H4, H5, H6, H7.
    rewrite <- csc_param_ctx in H0, H1, H2, H3, H4, H5, H6, H7.
    destruct m.
    + contradiction.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        escope. all: apply csc_param_ctx.
      }
      * change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (rpm_lift ?t) with (vreg ⋅ t). cbn.
        erewrite !erase_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        ssimpl. rewrite pren_S_pw. ssimpl.
        rewrite <- !rinstInst'_cterm.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite <- !funcomp_assoc.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite !funcomp_assoc.
        rewrite <- !renRen_cterm.
        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        escope. all: cbn. all: eauto using csc_param_ctx.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        escope. all: apply csc_param_ctx.
      }
      * change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (rpm_lift ?t) with (vreg ⋅ t). cbn.
        erewrite !erase_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        ssimpl. rewrite pren_S_pw. ssimpl.
        rewrite <- !rinstInst'_cterm.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite <- !funcomp_assoc.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite !funcomp_assoc.
        rewrite <- !renRen_cterm.
        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (ren_cterm vreg ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        escope. all: cbn. all: eauto using csc_param_ctx.
    + cbn in *. eapply cconv_irr.
      * {
        escope. all: eauto using csc_param_ctx.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        escope. all: apply csc_param_ctx.
      }
      * change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (rpm_lift ?t) with (vreg ⋅ t). cbn.
        erewrite !erase_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        ssimpl. rewrite pren_S_pw. ssimpl.
        rewrite <- !rinstInst'_cterm.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite <- !funcomp_assoc.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite !funcomp_assoc.
        rewrite <- !renRen_cterm.
        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (ren_cterm vreg ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        escope. all: cbn. all: eauto using csc_param_ctx.
  - cbn. apply cconv_refl.
  - cbn.
    destruct m, mx. all: simpl.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * cbn. apply crtyping_shift. apply crtyping_S.
      * eapply cstyping_one_none.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * apply crtyping_shift. apply crtyping_S.
      * apply cstyping_one_none.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * eapply cstyping_nones.
      * cbn. eapply crtyping_shift_eq.
        -- apply crtyping_shift. apply crtyping_S.
        -- cbn. f_equal. ssimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * apply crtyping_shift. apply crtyping_S.
      * apply cstyping_one_none.
    + econv. all: try reflexivity.
      eauto using crtyping_S.
    + econv. all: try reflexivity.
      eauto using crtyping_S.
    + econv. all: try reflexivity.
      eauto using crtyping_S.
    + econv. apply cstyping_one_none.
  - cbn in *. destruct_ifs.
    + econv. apply cstyping_one_none.
    + econv. all: try reflexivity.
      apply crtyping_S.
    + econv. all: try reflexivity.
      apply crtyping_S.
  - cbn.
    eapply conv_md in h2 as e2. rewrite <- e2.
    destruct_ifs.
    + econv. all: reflexivity.
    + econv. all: reflexivity.
    + econv.
  - cbn.
    eapply conv_md in h as e. rewrite <- e.
    destruct_ifs. all: econv.
  - cbn.
    eapply conv_md in h as e. rewrite <- e.
    destruct_ifs. all: econv.
  - cbn.
    eapply conv_md in h3 as e3. rewrite <- e3.
    destruct_ifs. all: econv. all: reflexivity.
  - cbn.
    eapply conv_md in h2 as e2. rewrite <- e2.
    destruct_ifs. all: econv. all: reflexivity.
  - cbn.
    econv. all: reflexivity.
  - cbn. destruct m.
    + econv. all: reflexivity.
    + econv. all: reflexivity.
    + econv. all: reflexivity.
    + econv.
  - cbn. econv.
  - cbn. destruct m.
    all: econv. all: reflexivity.
  - cbn. econv. all: reflexivity.
  - cbn. econv.
  - cbn. econv.
  - cbn. destruct m.
    + econv.
    + econv. all: reflexivity.
    + econv. all: reflexivity.
    + econv. all: reflexivity.
  - cbn.
    destruct_ifs. all: econv. all: reflexivity.
  - econv.
  - apply cconv_sym. assumption.
  - eapply cconv_trans. all: eauto.
  - eapply param_scoping in H, H0. cbn in *.
    apply cconv_irr. all: rewrite csc_param_ctx. all: assumption.
Qed.

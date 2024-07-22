From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival.
From Coq Require Import Setoid Morphisms Relation_Definitions.
From GhostTT Require Export Term.
From GhostTT Require Import Scope Renaming.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Opaque epm_lift rpm_lift.

(** Parametricity commutes with substitution

  As for revival we need to craft a new substitution that gets the scopes as
  input in order to determine the mode of the various variables.

**)

Definition psubst Δ Γ σ n :=
  let p := Nat.div2 n in
  match nth_error Δ p with
  | Some m =>
    if relm m then (
      if Nat.odd n then ⟦ Γ | σ p ⟧pε
      else ⟦ Γ | σ p ⟧p
    )
    else if isGhost m then (
      if Nat.odd n then ⟦ Γ | σ p ⟧pv
      else ⟦ Γ | σ p ⟧p
    )
    else (
      if Nat.odd n then ⟦ Γ | σ p ⟧p
      else cDummy
    )
  | None => cDummy
  end.

Lemma div2_vreg :
  ∀ n, Nat.div2 (vreg n) = n.
Proof.
  intros n.
  unfold vreg. replace (n * 2) with (2 * n) by lia.
  apply PeanoNat.Nat.div2_succ_double.
Qed.

Lemma div2_vpar :
  ∀ n, Nat.div2 (vpar n) = n.
Proof.
  intros n.
  unfold vpar. replace (n * 2) with (2 * n) by lia.
  apply PeanoNat.Nat.div2_double.
Qed.

Lemma odd_vreg :
  ∀ n, Nat.odd (vreg n) = true.
Proof.
  intros n.
  unfold vreg. replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. reflexivity.
Qed.

Lemma odd_vpar :
  ∀ n, Nat.odd (vpar n) = false.
Proof.
  intros n.
  unfold vpar. replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.odd_mul. reflexivity.
Qed.

Lemma psubst_SS :
  ∀ m Δ Γ σ n,
    psubst (m :: Δ) (m :: Γ) (up_term σ) (S (S n)) =
    plus 2 ⋅ psubst Δ Γ σ n.
Proof.
  intros m Δ Γ σ n.
  unfold psubst. rewrite div2_SS. cbn.
  destruct nth_error eqn:e. 2: reflexivity.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_succ.
  destruct_ifs. all: mode_eqs.
  - ssimpl. erewrite erase_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    ssimpl. rewrite <- pren_epm_lift.
    ssimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. ssimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    ssimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. ssimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite revive_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    ssimpl. rewrite <- pren_rpm_lift.
    eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. ssimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    ssimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. ssimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    ssimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. ssimpl. rewrite pren_id. reflexivity.
  - reflexivity.
Qed.

Transparent epm_lift rpm_lift.

Lemma psubst_epm_lift :
  ∀ Γ Δ σ t,
    ccscoping (erase_sc Δ) t cType →
    (epm_lift t) <[ psubst Δ Γ σ ] = epm_lift (t <[ σ >> erase_term Γ ]).
Proof.
  intros Γ Δ σ t ht.
  unfold epm_lift. ssimpl.
  eapply ext_cterm_scoped. 1: eassumption.
  intros x hx.
  ssimpl. unfold psubst. rewrite div2_vreg.
  unfold inscope in hx. unfold erase_sc in hx.
  rewrite nth_error_map in hx.
  destruct (nth_error Δ x) eqn:e. 2: discriminate.
  cbn in hx. destruct (relm m) eqn:e1. 2: discriminate.
  rewrite odd_vreg. reflexivity.
Qed.

Lemma psubst_rpm_lift :
  ∀ Γ Δ σ t,
    ccscoping (revive_sc Δ) t cType →
    (rpm_lift t) <[ psubst Δ Γ σ ] = rpm_lift (t <[ rev_subst Δ Γ σ ]).
Proof.
  intros Γ Δ σ t ht.
  unfold rpm_lift. ssimpl.
  eapply ext_cterm_scoped. 1: eassumption.
  intros x hx.
  ssimpl. unfold psubst. rewrite div2_vreg.
  unfold rev_subst. unfold ghv.
  unfold inscope in hx. unfold revive_sc in hx.
  rewrite nth_error_map in hx.
  destruct (nth_error Δ x) eqn:e. 2: discriminate.
  cbn in hx. destruct (isProp m) eqn:e1. 1: discriminate.
  rewrite odd_vreg.
  destruct_ifs. all: mode_eqs. all: try discriminate.
  all: try reflexivity.
  destruct m. all: discriminate.
Qed.

Opaque epm_lift rpm_lift.

Lemma param_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    ⟦ Γ | t <[ σ ] ⟧p = ⟦ Δ | t ⟧p <[ psubst Δ Γ σ ].
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  - cbn. destruct (nth_error Δ n) eqn:e.
    + destruct_if e1.
      * mode_eqs. cbn. unfold psubst. rewrite div2_vreg.
        rewrite e. cbn. rewrite odd_vreg. reflexivity.
      * cbn. unfold psubst. rewrite div2_vpar. rewrite e.
        rewrite odd_vpar.
        destruct_ifs. all: try reflexivity.
        destruct m. all: discriminate.
    + eapply hcσ in e as e'. destruct e' as [k [e1 e2]].
      rewrite e1. cbn. rewrite e2. reflexivity.
  - cbn. destruct_ifs. all: reflexivity.
  - cbn.
    unfold pmPi, pmPiP, pmPiNP, pPi.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    erewrite !erase_subst.
    2-5: eauto using sscoping_shift, sscoping_comp_shift with cc_scope.
    change (cEl (?t <[ ?σ ])) with ((cEl t) <[ σ ]).
    erewrite <- psubst_epm_lift. 2:{ econstructor. eapply erase_scoping. }
    destruct m, m0. all: cbn in *.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      f_equal. all: f_equal. all: f_equal.
      all: eapply ext_cterm. all: ssimpl. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      f_equal. all: f_equal. all: f_equal.
      all: eapply ext_cterm. all: ssimpl. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      unfold cty_lift. f_equal. all: f_equal.
      all: unfold close. all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl.
        rewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal.
      all: unfold close. all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl.
        erewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl.
      * rewrite rinstInst'_cterm. reflexivity.
      * rewrite rinstInst'_cterm. reflexivity.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl.
        erewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: ssimpl. all: reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. unfold close.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite psubst_SS. ssimpl.
      rewrite rinstInst'_cterm. reflexivity.
  - cbn.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    erewrite erase_subst. 2,3: eassumption.
    change (cEl (?t <[ ?σ ])) with ((cEl t) <[ σ ]).
    erewrite <- psubst_epm_lift. 2:{ econstructor. eapply erase_scoping. }
    destruct_ifs. all: mode_eqs.
    + cbn. f_equal. unfold close. ssimpl.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite psubst_SS. ssimpl.
      erewrite rinstInst'_cterm. reflexivity.
    + cbn. f_equal. unfold plam. f_equal. f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        rewrite psubst_SS. ssimpl. reflexivity.
    + cbn. unfold plam. f_equal. f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn.
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- rewrite psubst_SS. ssimpl. reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_subst. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
    destruct_ifs. all: reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    destruct_ifs. all: reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    destruct_ifs. all: reflexivity.
  - cbn. eauto.
  - cbn. eauto.
  - cbn.
    erewrite !revive_subst. 2-5: eassumption.
    erewrite !erase_subst. 2,3: eassumption.
    erewrite <- !psubst_rpm_lift. 2,3: eapply revive_scoping.
    change (cEl (?t <[ ?σ ])) with ((cEl t) <[ σ ]).
    erewrite <- psubst_epm_lift. 2:{ econstructor. eapply erase_scoping. }
    reflexivity.
  - cbn.
    erewrite erase_subst. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    change (cEl (?t <[ ?σ ])) with ((cEl t) <[ σ ]).
    erewrite <- psubst_epm_lift. 2:{ econstructor. eapply erase_scoping. }
    reflexivity.
  - cbn.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite IHt4. 2,3: eassumption.
    erewrite IHt5. 2,3: eassumption.
    erewrite IHt6. 2,3: eassumption.
    erewrite !erase_subst. 2-5: eassumption.
    erewrite !revive_subst. 2-7: eassumption.
    erewrite <- !psubst_rpm_lift. 2-4: eapply revive_scoping.
    change (cEl (?t <[ ?σ ])) with ((cEl t) <[ σ ]).
    erewrite <- !psubst_epm_lift.
    2: eapply erase_scoping.
    2:{ econstructor. eapply erase_scoping. }
    destruct md eqn:e.
    + reflexivity.
    + unfold pcastTG. cbn. ssimpl. reflexivity.
    + unfold pcastTG. cbn. ssimpl. reflexivity.
    + unfold pcastP. cbn. ssimpl. reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4. 2-9: eassumption.
    erewrite !erase_subst. 2-9: eassumption.
    erewrite !revive_subst. 2-5: eassumption.
    erewrite <- !psubst_rpm_lift. 2-3: eapply revive_scoping.
    erewrite <- !psubst_epm_lift. 2-5: eapply erase_scoping.
    destruct m.
    + unfold pmifK. unfold perif. cbn. f_equal. f_equal. all: f_equal.
      1,4: f_equal. 1,2: f_equal. 1-4: f_equal. 1,2,5-7,10: f_equal.
      2,3,5,6: f_equal. 2,4: f_equal.
      all: ssimpl. all: reflexivity.
    + unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      ssimpl. reflexivity.
    + unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      ssimpl. reflexivity.
    + reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. f_equal. eauto.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4. 2-9: eassumption.
    erewrite !erase_subst. 2-9: eassumption.
    erewrite !revive_subst. 2-5: eassumption.
    erewrite <- !psubst_rpm_lift. 2-3: eapply revive_scoping.
    erewrite <- !psubst_epm_lift. 2-5: eapply erase_scoping.
    destruct m. all: reflexivity.
  - cbn. erewrite IHt1, IHt2. 2-5: eassumption.
    erewrite !erase_subst, !revive_subst. 2-5: eassumption.
    erewrite <- !psubst_epm_lift, <- !psubst_rpm_lift.
    2: eapply revive_scoping.
    2: eapply erase_scoping.
    reflexivity.
  - cbn. erewrite IHt. 2-3: eassumption.
    reflexivity.
  - cbn. erewrite IHt1, IHt2, IHt3. 2-7: eassumption.
    reflexivity.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4, IHt5, IHt6. 2-13: eassumption.
    erewrite !erase_subst. 2-11: eassumption.
    erewrite !revive_subst. 2-7: eassumption.
    erewrite <- !psubst_rpm_lift. 2-4: eapply revive_scoping.
    erewrite <- !psubst_epm_lift. 2-6: eapply erase_scoping.
    destruct m. all: reflexivity.
  - cbn. reflexivity.
  - cbn.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_subst. 2,3: eassumption.
    destruct_ifs. all: try reflexivity.
    + cbn. f_equal. f_equal.
      rewrite psubst_epm_lift. 2: eauto with cc_scope.
      reflexivity.
    + cbn. f_equal. f_equal.
      rewrite psubst_epm_lift. 2: eauto with cc_scope.
      reflexivity.
Qed.

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Test whether a variable is defined and ghost **)

Definition ghv (Γ : scope) x :=
  match nth_error Γ x with
  | Some m => isGhost m
  | None => false
  end.

(** Revival translation **)

Reserved Notation "⟦ G | u '⟧v'" (at level 9, G, u at next level).

Equations revive_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧v := if ghv Γ x then cvar x else cDummy ;
  ⟦ Γ | lam mx A B t ⟧v :=
    if isGhost (md (mx :: Γ) t)
    then
      if isProp mx
      then close ⟦ mx :: Γ | t ⟧v
      else clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧v
    else cDummy ;
  ⟦ Γ | app u v ⟧v :=
    if isGhost (md Γ u)
    then
      if relm (md Γ v)
      then capp ⟦ Γ | u ⟧v ⟦ Γ | v ⟧ε
      else
        if isGhost (md Γ v)
        then capp ⟦ Γ | u ⟧v ⟦ Γ | v ⟧v
        else ⟦ Γ | u ⟧v
    else cDummy ;
  ⟦ Γ | hide t ⟧v := ⟦ Γ | t ⟧ε ;
  ⟦ Γ | reveal t P p ⟧v :=
    if isGhost (md Γ p)
    then capp ⟦ Γ | p ⟧v ⟦ Γ | t ⟧v
    else cDummy ;
  ⟦ Γ | ghcast A u v e P t ⟧v := ⟦ Γ | t ⟧v ;
  ⟦ Γ | tif m b P t f ⟧v :=
    if isGhost m then
      eif cType ⟦ Γ | b ⟧ε
        (clam cType ebool (cEl (capp (S ⋅ ⟦ Γ | P ⟧ε) (cvar 0))))
        ⟦ Γ | t ⟧v ⟦ Γ | f ⟧v (cErr (capp ⟦ Γ | P ⟧ε bool_err))
    else cDummy ;
  ⟦ Γ | bot_elim m A p ⟧v := if isGhost m then ⟦ Γ | A ⟧∅ else cDummy ;
  ⟦ _ | _ ⟧v := cDummy
}
where "⟦ G | u '⟧v'" := (revive_term G u).

Reserved Notation "⟦ G '⟧v'" (at level 9, G at next level).

Equations revive_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧v := [] ;
  ⟦ Γ ,, (mx, A) ⟧v :=
    if isProp mx
    then None :: ⟦ Γ ⟧v
    else Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧v
}
where "⟦ G '⟧v'" := (revive_ctx G).

Definition revive_sc (Γ : scope) : cscope :=
  map (λ m, if isProp m then None else Some cType) Γ.

(** Revival of non-ghost terms is cDummy **)

Lemma revive_ng :
  ∀ Γ t,
    isGhost (md Γ t) = false →
    ⟦ Γ | t ⟧v = cDummy.
Proof.
  intros Γ t hm.
  induction t in Γ, hm |- *.
  all: try reflexivity.
  all: try discriminate hm.
  - cbn in *. unfold ghv.
    destruct (nth_error _ _) eqn:e. 2: reflexivity.
    erewrite nth_error_nth in hm. 2: eassumption.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    destruct_if e. 2: reflexivity.
    destruct (md Γ _) eqn:e'. all: discriminate.
  - cbn - [mode_inb] in *. eauto.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
Qed.

(** ⟦ Γ ⟧ε is a sub-context of ⟦ Γ ⟧v **)

Lemma scoping_sub_rev :
  ∀ Γ,
    crscoping (revive_sc Γ) (λ x, x) (erase_sc Γ).
Proof.
  intros Γ. intros x m e.
  unfold erase_sc in e. rewrite nth_error_map in e.
  unfold revive_sc. rewrite nth_error_map.
  destruct (nth_error Γ x) as [mx|] eqn:ex. 2: discriminate.
  cbn - [mode_inb] in e. cbn - [mode_inb].
  destruct (relm mx) eqn:e1. 2: discriminate.
  noconf e.
  destruct (isProp mx) eqn:e2. 1:{ destruct mx. all: discriminate. }
  reflexivity.
Qed.

Lemma typing_sub_rev :
  ∀ Γ,
    crtyping ⟦ Γ ⟧v (λ x, x) ⟦ Γ ⟧ε.
Proof.
  intros Γ. intros x m A e.
  assert (h : nth_error ⟦ Γ ⟧v x = Some (Some (m, A))).
  { induction Γ as [| [my B] Γ ih] in x, m, A, e |- *.
    1:{ destruct x. all: discriminate. }
    destruct x.
    - cbn - [mode_inb] in e.
      destruct (relm my) eqn:ey. 2: discriminate.
      noconf e. cbn.
      destruct_if e1. 1:{ mode_eqs. discriminate. }
      reflexivity.
    - cbn - [mode_inb] in e.
      destruct (relm my) eqn:ey.
      + cbn. destruct_if e1. 1:{ mode_eqs. discriminate. }
        eapply ih. assumption.
      + cbn. destruct_if e1.
        * eapply ih. assumption.
        * eapply ih. assumption.
  }
  eexists. split.
  - eassumption.
  - ssimpl. reflexivity.
Qed.

Lemma scoping_to_rev :
  ∀ Γ t m,
    ccscoping (erase_sc Γ) t m →
    ccscoping (revive_sc Γ) t m.
Proof.
  intros Γ t m h.
  eapply cscoping_ren in h. 2: eapply scoping_sub_rev.
  rewrite rinstId'_cterm in h. assumption.
Qed.

Lemma conv_to_rev :
  ∀ Γ u v,
    ⟦ Γ ⟧ε ⊢ᶜ u ≡ v →
    ⟦ Γ ⟧v ⊢ᶜ u ≡ v.
Proof.
  intros Γ u v h.
  eapply cconv_ren in h. 2: eapply typing_sub_rev.
  revert h. ssimpl. auto.
Qed.

Lemma type_to_rev :
  ∀ Γ t A,
    ⟦ Γ ⟧ε ⊢ᶜ t : A →
    ⟦ Γ ⟧v ⊢ᶜ t : A.
Proof.
  intros Γ u v h.
  eapply ctyping_ren in h. 2: eapply typing_sub_rev.
  revert h. ssimpl. auto.
Qed.

(** Revival of context and of variables **)

Lemma revive_sc_var :
  ∀ Γ x,
    nth_error Γ x = Some mGhost →
    nth_error (revive_sc Γ) x = Some (Some cType).
Proof.
  intros Γ x e.
  unfold revive_sc. rewrite nth_error_map.
  rewrite e. cbn. reflexivity.
Qed.

(** Revival preserves scoping **)

Lemma revive_scoping :
  ∀ Γ t,
    ccscoping (revive_sc Γ) ⟦ Γ | t ⟧v cType.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. destruct_if e. 2: constructor.
    constructor. eapply revive_sc_var.
    unfold ghv in e. destruct nth_error eqn:e1. 2: discriminate.
    mode_eqs. reflexivity.
  - cbn - [mode_inb].
    destruct_ifs.
    + mode_eqs. eapply cscope_close.
      change (None :: revive_sc Γ) with (revive_sc (mProp :: Γ)).
      eauto.
    + constructor.
      * eapply scoping_to_rev. constructor. eapply erase_scoping.
      * specialize IHt3 with (Γ := m :: Γ). cbn in IHt3.
        rewrite e0 in IHt3. eauto.
    + constructor.
  - cbn - [mode_inb].
    destruct_ifs. 4: eauto with cc_scope.
    + econstructor. 1: eauto.
      eapply scoping_to_rev. eapply erase_scoping.
    + econstructor. all: eauto.
    + eauto.
  - cbn - [mode_inb].
    eapply scoping_to_rev. eapply erase_scoping.
  - cbn - [mode_inb]. destruct_if e. 2: constructor.
    escope.
    + apply scoping_to_rev. apply erase_scoping.
    + eapply cscoping_ren. 1: apply crscoping_S.
      apply scoping_to_rev. apply erase_scoping.
    + reflexivity.
    + apply scoping_to_rev. apply erase_scoping.
  - cbn - [mode_inb].
    destruct_if e. 2: constructor.
    constructor. eapply scoping_to_rev. eapply erase_scoping.
Qed.

(** Revival commutes with renaming **)

Lemma revive_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧v = ρ ⋅ ⟦ Δ | t ⟧v.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  - cbn - [mode_inb].
    unfold ghv.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e.
      destruct (isGhost m). all: reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn - [mode_inb]. ssimpl.
    erewrite IHt3.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    erewrite md_ren.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    destruct_ifs. 3: reflexivity.
    + unfold close. ssimpl. reflexivity.
    + ssimpl. f_equal. erewrite erase_ren. 2,3: eassumption.
      reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: try solve [ eauto ].
    ssimpl. f_equal.
    erewrite erase_ren. 2,3: eassumption.
    reflexivity.
  - cbn - [mode_inb].
    erewrite erase_ren. 2,3: eassumption.
    reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb]. destruct_ifs. 2: eauto.
    cbn. erewrite IHt3, IHt4. 2-5: eassumption.
    erewrite !erase_ren. 2-5: eassumption.
    f_equal. ssimpl. reflexivity.
  - cbn - [mode_inb].
    destruct_ifs. 2: eauto.
    erewrite erase_ren. 2,3: eassumption.
    reflexivity.
Qed.

(** Revival commutes with substitution **)

Definition rev_subst Δ Γ σ n :=
  if ghv Δ n then ⟦ Γ | σ n ⟧v else ⟦ Γ | σ n ⟧ε.

Lemma erase_rev_subst :
  ∀ Γ Δ t σ,
    ⟦ Δ | t ⟧ε <[ σ >> erase_term Γ ] = ⟦ Δ | t ⟧ε <[ rev_subst Δ Γ σ ].
Proof.
  intros Γ Δ t σ.
  eapply ext_cterm_scoped. 1: eapply erase_scoping. intros x hx.
  unfold rev_subst. unfold ghv.
  unfold inscope in hx. unfold erase_sc in hx. rewrite nth_error_map in hx.
  destruct nth_error as [m |] eqn:e1. 2: discriminate.
  cbn - [mode_inb] in hx.
  destruct (relm m) eqn:e2. 2: discriminate.
  destruct_if e3. 1:{ destruct m. all: discriminate. }
  reflexivity.
Qed.

Lemma revive_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    ⟦ Γ | t <[ σ ] ⟧v = ⟦ Δ | t ⟧v <[ rev_subst Δ Γ σ ].
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  - ssimpl. cbn. unfold ghv. unfold rev_subst. destruct (nth_error Δ n) eqn:e.
    + destruct (isGhost m) eqn:em.
      * cbn. unfold ghv. rewrite e. rewrite em. reflexivity.
      * cbn. eapply revive_ng. clear hcσ.
        induction hσ as [| σ Δ mx hσ ih hm] in n, m, e, em |- *.
        1: destruct n ; discriminate.
        destruct n.
        -- cbn - [mode_inb] in *.
          erewrite scoping_md. 2: eassumption.
          noconf e. assumption.
        -- cbn in e. eapply ih. all: eassumption.
    + cbn. eapply hcσ in e as e'. destruct e' as [m [e1 e2]].
      rewrite e1. cbn.
      unfold ghv. rewrite e2. reflexivity.
  - cbn.
    erewrite md_subst.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ ssimpl. eapply sscoping_comp_shift. assumption. }
    erewrite erase_subst. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ ssimpl. eapply sscoping_comp_shift. assumption. }
    destruct_ifs.
    + destruct m. all: try discriminate.
      unfold close. ssimpl.
      eapply ext_cterm. intros [].
      * cbn. reflexivity.
      * cbn. unfold rev_subst. ssimpl. unfold ghv. cbn.
        destruct (nth_error Δ n) eqn:e1.
        -- destruct_if e2.
          ++ ssimpl. erewrite revive_ren.
            2:{ eapply rscoping_S. }
            2:{ eapply rscoping_comp_S. }
            ssimpl. reflexivity.
          ++ ssimpl. erewrite erase_ren.
            2:{ eapply rscoping_S. }
            2:{ eapply rscoping_comp_S. }
            ssimpl. reflexivity.
        -- ssimpl. erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
    + cbn. ssimpl. f_equal.
      * f_equal. eapply erase_rev_subst.
      * eapply ext_cterm. intros [].
        -- cbn. unfold rev_subst. unfold ghv. cbn - [mode_inb].
          destruct_if e1. 1: reflexivity.
          destruct_if e2. 2:{ destruct m. all: discriminate. }
          reflexivity.
        -- cbn. unfold rev_subst. unfold ghv. cbn.
          destruct (nth_error _ _) eqn:e1.
          ++ destruct_if e2.
            ** ssimpl. erewrite revive_ren.
              2: eapply rscoping_S.
              2: eapply rscoping_comp_S.
              reflexivity.
            ** ssimpl. erewrite erase_ren.
              2: eapply rscoping_S.
              2: eapply rscoping_comp_S.
              reflexivity.
          ++ ssimpl. erewrite erase_ren.
            2: eapply rscoping_S.
            2: eapply rscoping_comp_S.
            reflexivity.
    + reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eauto.
    erewrite IHt2. 2,3: eauto.
    destruct_ifs.
    + cbn. ssimpl. f_equal. erewrite erase_subst. 2,3: eassumption.
      apply erase_rev_subst.
    + cbn. reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn - [mode_inb].
    erewrite erase_subst. 2,3: eassumption.
    apply erase_rev_subst.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    destruct_ifs. 2: reflexivity.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt3. 2,3: eassumption.
    erewrite IHt4. 2,3: eassumption.
    erewrite !erase_subst. 2-5: eassumption.
    rewrite !erase_rev_subst.
    destruct_if eg. 2: reflexivity.
    cbn. f_equal. ssimpl. reflexivity.
  - cbn - [mode_inb].
    destruct_ifs. 2: reflexivity.
    erewrite erase_subst. 2,3: eassumption.
    cbn. f_equal. apply erase_rev_subst.
Qed.

(** Revival preserves conversion **)

Lemma revive_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧v ⊢ᶜ ⟦ sc Γ | u ⟧v ≡ ⟦ sc Γ | v ⟧v.
Proof.
  intros Γ u v h.
  induction h.
  all: try solve [ cbn - [mode_inb] ; constructor ].
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs. all: try discriminate.
    + eapply cmeta_conv_trans_r. 1: constructor.
      erewrite revive_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped. 1: eapply revive_scoping.
      unfold rev_subst. unfold ghv.
      intros [| x] ex.
      * cbn. destruct_if e2. 1:{ mode_eqs. discriminate. }
        reflexivity.
      * cbn. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (isProp m) eqn:e2. 1: discriminate.
        destruct_if e3.
        -- mode_eqs. unfold ghv. rewrite e'. cbn. reflexivity.
        -- unfold relv. rewrite e'.
          destruct_if e4. 2:{ destruct m. all: discriminate. }
          reflexivity.
    + eapply cmeta_conv_trans_r. 1: constructor.
      erewrite revive_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped. 1: eapply revive_scoping.
      unfold rev_subst. unfold ghv.
      intros [| x] ex.
      * cbn. reflexivity.
      * cbn. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (isProp m) eqn:e3. 1: discriminate.
        destruct_if e4.
        -- mode_eqs. unfold ghv. rewrite e'. cbn. reflexivity.
        -- unfold relv. rewrite e'.
          destruct_ifs. 2:{ destruct m. all: discriminate. }
          reflexivity.
    + unfold close. erewrite revive_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. apply ccmeta_refl.
      eapply ext_cterm_scoped. 1: eapply revive_scoping.
      intros [| x] ex.
      1:{ unfold inscope in ex. cbn - [mode_inb] in ex. discriminate. }
      cbn. unfold rev_subst. unfold ghv. unfold inscope in ex.
      cbn - [mode_inb] in ex.
      rewrite nth_error_map in ex.
      destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
      cbn - [mode_inb] in ex.
      destruct (isProp m) eqn:e2. 1: discriminate.
      cbn. rewrite e'.
      destruct_if e3.
      * mode_eqs. unfold ghv. rewrite e'. cbn. reflexivity.
      * unfold relv. rewrite e'.
        destruct_ifs. 2:{ destruct m. all: discriminate. }
        reflexivity.
    + destruct mx. all: discriminate.
    + erewrite revive_ng.
      2:{ erewrite md_subst.
        2:{ eapply sscoping_one. eassumption. }
        2:{ eapply sscoping_comp_one. }
        erewrite scoping_md. 2: eassumption.
        assumption.
      }
      constructor.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption. cbn.
    apply cconv_refl.
  - cbn - [mode_inb]. destruct_if eg.
    + constructor.
    + erewrite revive_ng. 2:{ remd. assumption. }
      constructor.
  - cbn - [mode_inb]. destruct_if eg.
    + constructor.
    + erewrite revive_ng. 2:{ remd. assumption. }
      constructor.
  - cbn - [mode_inb].
    cbn - [mode_inb] in IHh2, IHh3.
    eapply conv_md in h3 as e3. simpl in e3. rewrite <- e3.
    destruct_ifs.
    + eapply cconv_close. eauto.
    + constructor.
      * constructor. eapply conv_to_rev. eapply erase_conv. assumption.
      * eauto.
    + constructor.
  - cbn - [mode_inb].
    eapply conv_md in h1 as e1. rewrite <- e1.
    eapply conv_md in h2 as e2. rewrite <- e2.
    destruct_ifs.
    + constructor. all: eauto.
      eapply conv_to_rev. eapply erase_conv. assumption.
    + constructor. all: eauto.
    + eauto.
    + constructor.
  - cbn - [mode_inb]. eapply conv_to_rev. eapply erase_conv. assumption.
  - cbn - [mode_inb].
    eapply conv_md in h3 as e1. rewrite <- e1.
    destruct_if'.
    + constructor. all: eauto.
    + constructor.
  - cbn - [mode_inb]. destruct_if eg. 2: constructor.
    econv. 1,3: eapply conv_to_rev. 1,2: eapply erase_conv ; eauto.
    eapply cconv_ren. 1: apply crtyping_S.
    eapply conv_to_rev. eapply erase_conv. assumption.
  - cbn - [mode_inb].
    destruct_ifs. 2: constructor.
    constructor. eapply conv_to_rev. eapply erase_conv. assumption.
  - constructor. eassumption.
  - eapply cconv_trans. all: eauto.
  - rewrite 2!revive_ng. 1: constructor.
    all: erewrite scoping_md ; [| eassumption ]. all: reflexivity.
Qed.

(** Revival ignores casts **)

Lemma revive_castrm :
  ∀ Γ t,
    ⟦ Γ | ε|t| ⟧v = ⟦ Γ | t ⟧v.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try reflexivity.
  all: try solve [ cbn - [mode_inb] ; eauto ].
  - cbn - [mode_inb]. erewrite IHt3. erewrite !erase_castrm.
    rewrite <- md_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite IHt1, IHt2. erewrite !erase_castrm.
    rewrite <- !md_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite !erase_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite IHt1, IHt3.
    rewrite <- !md_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite IHt3, IHt4. erewrite !erase_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite !erase_castrm. reflexivity.
Qed.

(** Revival of erased conversion **)

Lemma revive_castrm_conv :
  ∀ Γ u v,
    Γ ⊢ u ε≡ v →
    ⟦ Γ ⟧v ⊢ᶜ ⟦ sc Γ | u ⟧v ≡ ⟦ sc Γ | v ⟧v.
Proof.
  intros Γ u v h.
  eapply revive_conv in h.
  rewrite !revive_castrm in h.
  assumption.
Qed.

(** Revival preserves typing **)

Lemma revive_ctx_var :
  ∀ Γ x A,
    nth_error Γ x = Some (mGhost, A) →
    nth_error ⟦ Γ ⟧v x = Some (Some (cType, ⟦ skipn (S x) (sc Γ) | A ⟧τ)).
Proof.
  intros Γ x A e.
  induction Γ as [| [my B] Γ ih ] in x, A, e |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn. reflexivity.
  - cbn in e. cbn - [mode_inb skipn].
    destruct_if e1.
    + erewrite ih. 2: eauto. reflexivity.
    + erewrite ih. 2: eauto. reflexivity.
Qed.

Theorem revive_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    mdc Γ t = mGhost →
    ⟦ Γ ⟧v ⊢ᶜ ⟦ sc Γ | t ⟧v : ⟦ sc Γ | A ⟧τ.
Proof.
  intros Γ t A h hm.
  induction h.
  all: try solve [ cbn in hm ; discriminate ].
  - cbn. unfold ghv. unfold sc. rewrite nth_error_map.
    rewrite H. cbn - [mode_inb].
    cbn in hm.
    erewrite nth_error_nth in hm.
    2:{ unfold sc. erewrite nth_error_map. erewrite H. reflexivity. }
    cbn - [mode_inb] in hm. subst.
    cbn. eapply ccmeta_conv.
    + econstructor. eapply revive_ctx_var. eassumption.
    + cbn - [skipn]. f_equal.
      erewrite erase_ren.
      * reflexivity.
      * intros y my ey. rewrite <- nth_error_skipn in ey. assumption.
      * intros y ey. rewrite <- nth_error_skipn in ey. assumption.
  - cbn - [mode_inb]. cbn - [mode_inb] in IHh3.
    repeat (erewrite scoping_md ; [| eassumption]).
    cbn - [mode_inb] in hm.
    erewrite scoping_md in hm. 2: eassumption. subst.
    erewrite scoping_md in IHh3. 2: eassumption.
    simpl isGhost. cbn match. change (true && ?c) with c.
    destruct_ifs. all: mode_eqs. all: try discriminate.
    + econstructor.
      * eapply ctype_close. eauto.
      * unfold close. apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. apply cconv_refl.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        -- econstructor.
          ++ eapply ctype_close.
            eapply erase_typing in h2.
            2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
            eapply type_to_rev in h2.
            cbn in h2. eassumption.
          ++ unfold close. cbn. constructor.
          ++ eauto with cc_type.
        -- econstructor.
          ++ eapply ctype_close.
            eapply erase_typing in h2.
            2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
            eapply type_to_rev in h2.
            cbn in h2. eassumption.
          ++ unfold close. cbn. constructor.
          ++ eauto with cc_type.
    + econstructor.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        -- econstructor.
          ++ eapply erase_typing in h1.
            2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
            eapply type_to_rev in h1.
            cbn in h1. rewrite e in h1. eassumption.
          ++ constructor.
          ++ eauto with cc_type.
      * apply cconv_sym.
        eapply cconv_trans. 1: constructor.
        apply cconv_refl.
      * econstructor. econstructor.
        -- econstructor.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h1.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h1.
              cbn in h1. rewrite e in h1. eassumption.
            ** constructor.
            ** eauto with cc_type.
          ++ constructor. econstructor.
            ** eapply erase_typing in h2.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h2.
              cbn in h2. rewrite e in h2. eassumption.
            ** constructor.
            ** eauto with cc_type.
        -- econstructor.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h1.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h1.
              cbn in h1. rewrite e in h1. eassumption.
            ** constructor.
            ** eauto with cc_type.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h2.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h2.
              cbn in h2. rewrite e in h2. eassumption.
            ** constructor.
            ** eauto with cc_type.
    + ssimpl. erewrite ext_cterm_scoped with (θ := ids).
      2: eapply erase_scoping.
      2:{
        intros [] ex.
        - cbn. discriminate.
        - cbn. ssimpl. reflexivity.
      }
      ssimpl.
      unfold nones. ssimpl.
      erewrite ext_cterm_scoped with (θ := ids).
      2: eapply erase_scoping.
      2:{
        intros [] ex.
        - cbn. discriminate.
        - cbn. ssimpl. reflexivity.
      }
      ssimpl.
      econstructor.
      * econstructor.
        -- econstructor. econstructor.
          ++ eapply erase_typing in h1.
            2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
            eapply type_to_rev in h1.
            cbn in h1. eassumption.
          ++ constructor.
          ++ eauto with cc_type.
        -- eauto.
      * apply cconv_sym.
        eapply cconv_trans. 1: constructor. apply cconv_refl.
      * econstructor. econstructor.
        -- econstructor.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h1.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h1.
              cbn in h1. eassumption.
            ** constructor.
            ** eauto with cc_type.
          ++ constructor. econstructor.
            ** eapply erase_typing in h2.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h2.
              cbn in h2. eassumption.
            ** constructor.
            ** eauto with cc_type.
        -- econstructor.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h1.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h1.
              cbn in h1. eassumption.
            ** constructor.
            ** eauto with cc_type.
          ++ econstructor. econstructor.
            ** eapply erase_typing in h2.
              2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
              eapply type_to_rev in h2.
              cbn in h2. eassumption.
            ** constructor.
            ** eauto with cc_type.
    + destruct mx. all: discriminate.
  - cbn - [mode_inb] in *.
    erewrite scoping_md in hm. 2: eassumption. subst.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh2. 2: eassumption.
    repeat (erewrite scoping_md ; [| eassumption]).
    simpl isGhost. cbn match.
    destruct_ifs. all: mode_eqs.
    + cbn in IHh1.
      destruct (isProp mx) eqn:e1. 1:{ mode_eqs. discriminate. }
      econstructor.
      * econstructor.
        -- econstructor.
          ++ eauto.
          ++ constructor.
          ++ constructor.
            ** constructor. econstructor.
              --- eapply erase_typing in h3.
                  2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
                  eapply type_to_rev in h3.
                  cbn in h3. rewrite e1 in h3. eassumption.
              --- constructor.
              --- eauto with cc_type.
            ** constructor. econstructor.
              --- eapply erase_typing in h4.
                  2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
                  eapply type_to_rev in h4.
                  cbn in h4. rewrite e1 in h4. eassumption.
              --- constructor.
              --- eauto with cc_type.
        -- eapply erase_typing in h2.
          2:{ erewrite scoping_md. 2: eassumption. assumption. }
          eapply type_to_rev in h2. eassumption.
      * erewrite erase_subst.
        2:{ eapply sscoping_one. eauto. }
        2: eapply sscoping_comp_one.
        cbn. apply ccmeta_refl. f_equal.
        eapply ext_cterm_scoped. 1: eapply erase_scoping.
        intros [] ex.
        -- cbn. reflexivity.
        -- cbn. unfold relv. unfold inscope in ex.
          cbn - [mode_inb] in ex. rewrite nth_error_map in ex.
          destruct nth_error eqn:e2. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct_ifs. 2: discriminate.
          reflexivity.
      * eapply typing_subst in h4.
        2:{ eapply styping_one. 2: eassumption. assumption. }
        cbn in h4. eapply erase_typing in h4.
        2:{
          erewrite md_subst.
          2:{ eapply sscoping_one. eassumption. }
          2: eapply sscoping_comp_one.
          erewrite scoping_md. 2: eassumption. reflexivity.
        }
        eapply type_to_rev in h4. cbn in h4.
        econstructor. econstructor.
        -- eassumption.
        -- constructor.
        -- eauto with cc_type.
    + cbn in IHh1.
      revert IHh1.
      ssimpl. erewrite ext_cterm_scoped with (θ := ids).
      2: eapply erase_scoping.
      2:{
        intros [] ex.
        - cbn. discriminate.
        - cbn. ssimpl. reflexivity.
      }
      ssimpl.
      unfold nones. ssimpl.
      erewrite ext_cterm_scoped with (θ := ids).
      2: eapply erase_scoping.
      2:{
        intros [] ex.
        - cbn. discriminate.
        - cbn. ssimpl. reflexivity.
      }
      ssimpl. intro ih.
      econstructor.
      * econstructor.
        -- econstructor.
          ++ eauto.
          ++ constructor.
          ++ constructor.
            ** constructor. econstructor.
              --- eapply erase_typing in h3.
                  2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
                  eapply type_to_rev in h3.
                  cbn in h3. eassumption.
              --- constructor.
              --- eauto with cc_type.
            ** constructor. econstructor.
              --- eapply erase_typing in h4.
                  2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
                  eapply type_to_rev in h4.
                  cbn in h4. eassumption.
              --- constructor.
              --- eauto with cc_type.
        -- eauto.
      * cbn. erewrite erase_subst.
        2:{ eapply sscoping_one. eauto. }
        2: eapply sscoping_comp_one.
        apply ccmeta_refl. f_equal.
        eapply ext_cterm_scoped. 1: eapply erase_scoping.
        intros [] ex. 1: discriminate.
        cbn. unfold relv. unfold inscope in ex.
        cbn - [mode_inb] in ex. rewrite nth_error_map in ex.
        destruct nth_error eqn:e2. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct_ifs. 2: discriminate.
        reflexivity.
      * eapply typing_subst in h4.
        2:{ eapply styping_one. 2: eassumption. assumption. }
        cbn in h4. eapply erase_typing in h4.
        2:{
          erewrite md_subst.
          2:{ eapply sscoping_one. eassumption. }
          2: eapply sscoping_comp_one.
          erewrite scoping_md. 2: eassumption. reflexivity.
        }
        eapply type_to_rev in h4. cbn in h4.
        econstructor. econstructor.
        -- eassumption.
        -- constructor.
        -- eauto with cc_type.
    + cbn in IHh1. econstructor.
      * eauto.
      * eapply cconv_trans. 1: constructor.
        apply ccmeta_refl. f_equal.
        unfold close. erewrite erase_subst.
        2:{ eapply sscoping_one. eassumption. }
        2: eapply sscoping_comp_one.
        ssimpl. eapply ext_cterm_scoped. 1: eapply erase_scoping.
        intros [] ex.
        -- cbn - [mode_inb] in ex. rewrite e in ex. discriminate.
        -- cbn. unfold relv. unfold inscope in ex. unfold erase_sc in ex.
          rewrite nth_error_map in ex. cbn - [mode_inb] in ex.
          destruct nth_error eqn:e2. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct_ifs. 2: discriminate.
          reflexivity.
      * eapply typing_subst in h4.
        2:{ eapply styping_one. 2: eassumption. assumption. }
        cbn in h4. eapply erase_typing in h4.
        2:{
          erewrite md_subst.
          2:{ eapply sscoping_one. eassumption. }
          2: eapply sscoping_comp_one.
          erewrite scoping_md. 2: eassumption. reflexivity.
        }
        eapply type_to_rev in h4. cbn in h4.
        econstructor. econstructor.
        -- eassumption.
        -- constructor.
        -- eauto with cc_type.
  - cbn - [mode_inb]. eapply type_to_rev. eapply erase_typing.
    + assumption.
    + erewrite scoping_md. 2: eassumption. reflexivity.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    cbn. cbn in hm. erewrite scoping_md in hm. 2: eassumption.
    destruct m. all: try discriminate.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh3. 2: eassumption.
    cbn in IHh1. cbn - [mode_inb] in IHh3.
    erewrite md_ren in IHh3.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    erewrite scoping_md in IHh3. 2: eassumption.
    cbn in IHh3.
    cbn. econstructor.
    + econstructor.
      * econstructor.
        -- eauto.
        -- constructor.
        -- constructor.
          ++ cbn in h4. eapply erase_typing in h4.
            2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
            eapply type_to_rev in h4. cbn in h4.
            econstructor. econstructor.
            ** eassumption.
            ** constructor.
            ** eauto with cc_type.
          ++ eapply typing_ren in h2. 2: eapply rtyping_S with (m := mType).
            cbn in h2. eapply erase_typing in h2.
            2:{
              cbn - [mode_inb].
              erewrite md_ren.
              2: eapply rscoping_S.
              2: eapply rscoping_comp_S.
              erewrite scoping_md. 2: eassumption. reflexivity.
            }
            eapply type_to_rev in h2. cbn in h2.
            econstructor. econstructor.
            ** eassumption.
            ** eapply cconv_trans. 1: constructor.
              constructor.
            ** eauto with cc_type.
      * eauto.
    + ssimpl. apply ccmeta_refl.
      erewrite erase_ren.
      2: eapply rscoping_S.
      2: eapply rscoping_comp_S.
      ssimpl. reflexivity.
    + eapply erase_typing in h2.
      2:{
        cbn - [mode_inb].
        erewrite scoping_md. 2: eassumption. reflexivity.
      }
      eapply type_to_rev in h2. cbn in h2.
      econstructor. econstructor.
      * eassumption.
      * eapply cconv_trans. 1: constructor.
        constructor.
      * eauto with cc_type.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    cbn. cbn - [mode_inb] in IHh6.
    cbn in hm. erewrite scoping_md in hm. 2: eassumption. subst.
    erewrite scoping_md in IHh6. 2: eassumption.
    erewrite scoping_md in IHh6. 2: eassumption.
    erewrite scoping_md in IHh6. 2: eassumption.
    cbn in IHh6. eauto.
  - cbn - [mode_inb]. cbn in hm. subst m. remd. cbn.
    eapply erase_typing in h1 as hbe. 2:{ remd. reflexivity. }
    cbn in hbe. eapply ctype_conv in hbe.
    2:{ constructor. }
    2: etype.
    eapply erase_typing in h2 as hPe. 2:{ remd. reflexivity. }
    cbn in hPe.
    eapply ctype_conv in hPe.
    2:{
      eapply cconv_trans. 1: constructor.
      econstructor. all: constructor.
    }
    2: etype.
    remd in IHh3. forward IHh3 by reflexivity. cbn - [mode_inb] in IHh3.
    remd in IHh3. cbn in IHh3.
    remd in IHh4. forward IHh4 by reflexivity. cbn - [mode_inb] in IHh4.
    remd in IHh4. cbn in IHh4.
    apply type_to_rev in hbe. apply type_to_rev in hPe.
    econstructor.
    + econstructor.
      * assumption.
      * {
        econstructor. 1: etype.
        cbn. econstructor.
        eapply ccmeta_conv.
        - econstructor.
          + eapply ccmeta_conv.
            * eapply ctyping_ren. 1: apply crtyping_S.
              eauto.
            * cbn. reflexivity.
          + eapply ccmeta_conv.
            * econstructor. reflexivity.
            * reflexivity.
        - cbn. reflexivity.
      }
      * {
        econstructor.
        - eauto.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. ssimpl. apply cconv_refl.
        - eapply ccmeta_conv.
          + econstructor. 2: eauto with cc_type.
            econstructor. 1: etype.
            constructor. eapply ccmeta_conv.
            * {
              etype. 2: reflexivity.
              cbn. eapply ccmeta_conv.
              - eapply ctyping_ren. 1: apply crtyping_S.
                eauto.
              - cbn. reflexivity.
            }
            * cbn. reflexivity.
          + cbn. reflexivity.
      }
      * {
        econstructor.
        - eauto.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. ssimpl. apply cconv_refl.
        - eapply ccmeta_conv.
          + econstructor. 2: eauto with cc_type.
            econstructor. 1: etype.
            constructor. eapply ccmeta_conv.
            * {
              etype. 2: reflexivity.
              cbn. eapply ccmeta_conv.
              - eapply ctyping_ren. 1: apply crtyping_S.
                eauto.
              - cbn. reflexivity.
            }
            * cbn. reflexivity.
          + cbn. reflexivity.
      }
      * {
        econstructor.
        - etype. eapply ccmeta_conv.
          + etype.
          + cbn. reflexivity.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. ssimpl. apply cconv_refl.
        - eapply ccmeta_conv.
          + etype. eapply ccmeta_conv.
            * {
              etype. 2: reflexivity.
              cbn. eapply ccmeta_conv.
              - eapply ctyping_ren. 1: apply crtyping_S.
                eauto.
              - cbn. reflexivity.
            }
            * cbn. reflexivity.
          + cbn. reflexivity.
      }
    + eapply cconv_trans. 1: constructor.
      cbn. ssimpl. apply cconv_refl.
    + etype. eapply ccmeta_conv.
      * etype.
      * cbn. reflexivity.
  - cbn - [mode_inb].
    cbn in hm. subst. cbn.
    eapply erase_typing in h1.
    2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
    eapply type_to_rev in h1. cbn in h1.
    econstructor. econstructor.
    + eassumption.
    + constructor.
    + eauto with cc_type.
  - econstructor.
    + eauto.
    + constructor. eapply conv_to_rev. eapply erase_castrm_conv. assumption.
    + eapply erase_typing in h2.
      2:{ erewrite scoping_md. 2: eassumption. reflexivity. }
      eapply type_to_rev in h2. cbn in h2.
      erewrite scoping_md in hm. 2: eassumption. subst.
      cbn in h2.
      econstructor. econstructor.
      * eassumption.
      * constructor.
      * eauto with cc_type.
Qed.

Corollary revive_context :
  ∀ Γ,
    wf Γ →
    cwf ⟦ Γ ⟧v.
Proof.
  intros Γ h.
  induction h.
  - constructor.
  - cbn - [mode_inb]. destruct (isProp m) eqn:ep.
    + constructor. 1: assumption.
      constructor.
    + constructor. 1: assumption.
      cbn. exists i.
      eapply erase_typing_El.
      * apply type_to_rev. eapply erase_typing. 1: eassumption.
        erewrite scoping_md. 2: eassumption.
        reflexivity.
      * assumption.
Qed.

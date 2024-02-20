From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Lifting from cty i to cty j **)

Definition cty_lift A :=
  ctyval Any (cEl A) (cErr A).

Lemma cscope_ty_lift :
  ∀ Γ A,
    ccscoping Γ A cType →
    ccscoping Γ (cty_lift A) cType.
Proof.
  intros Γ A h.
  unfold cty_lift.
  constructor. all: constructor. all: assumption.
Qed.

Hint Resolve cscope_ty_lift : cc_scope.

Lemma ctype_ty_lift :
  ∀ Γ i j A,
    Γ ⊢ᶜ A : cty i →
    i ≤ j →
    Γ ⊢ᶜ cty_lift A : cty j.
Proof.
  intros Γ i j A h hij.
  unfold cty_lift.
  constructor.
  - eapply ctype_cumul.
    + econstructor. eassumption.
    + assumption.
  - econstructor. eassumption.
Qed.

Lemma cconv_ty_lift :
  ∀ Γ A B,
    Γ ⊢ᶜ A ≡ B →
    Γ ⊢ᶜ cty_lift A ≡ cty_lift B.
Proof.
  intros Γ A B h.
  unfold cty_lift. constructor.
  all: constructor. all: assumption.
Qed.

Hint Resolve ctype_ty_lift : cc_type.

(* TODO MOVE *)

Lemma ccmeta_refl :
  ∀ Γ u v,
    u = v →
    Γ ⊢ᶜ u ≡ v.
Proof.
  intros Γ u ? ->. constructor.
Qed.

Definition cDummy := ctt.

(** Test whether a variable is defined and relevant **)

Definition relv (Γ : scope) x :=
  match nth_error Γ x with
  | Some m => relm m
  | None => false
  end.

(** Mark corresponding to a mode **)

Definition mdmk (m : mode) :=
  match m with
  | mKind => WasKind
  | mType => WasType
  | mGhost => WasGhost
  | mProp => Any
  end.

(** Erasure translation **)

Reserved Notation "⟦ G | u '⟧ε'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧τ'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧∅'" (at level 9, G, u at next level).

Equations erase_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧ε := if relv Γ x then cvar x else cDummy ;
  ⟦ Γ | Sort m i ⟧ε :=
    if isProp m
    then ctyval Any cunit ctt
    else ctyval (mdmk m) (cty i) ctyerr ;
  ⟦ Γ | Pi i j m mx A B ⟧ε :=
    if relm mx && negb (isProp m)
    then ctyval Any (cPi cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧τ) (clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧∅)
    else if isGhost m && isGhost mx
    then ctyval Any (⟦ Γ | A ⟧τ ⇒[ cType ] (close ⟦ mx :: Γ | B ⟧τ)) (clam cType ⟦ Γ | A ⟧τ (ignore ⟦ mx :: Γ | B ⟧∅))
    else if isProp m
    then ctt
    else cty_lift (close ⟦ mx :: Γ | B ⟧ε) ;
  ⟦ Γ | lam mx A B t ⟧ε :=
    if relm (md (mx :: Γ) t)
    then
      if relm mx
      then clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧ε
      else close ⟦ mx :: Γ | t ⟧ε
    else cDummy ;
  ⟦ Γ | app u v ⟧ε :=
    if relm (md Γ u)
    then
      if relm (md Γ v)
      then capp ⟦ Γ | u ⟧ε ⟦ Γ | v ⟧ε
      else ⟦ Γ | u ⟧ε
    else cDummy ;
  ⟦ Γ | Erased A ⟧ε := ⟦ Γ | A ⟧ε ;
  ⟦ Γ | Reveal t p ⟧ε := ctt ;
  ⟦ Γ | gheq A u v ⟧ε := ctt ;
  ⟦ Γ | ghcast A u v e P t ⟧ε := ⟦ Γ | t ⟧ε ;
  ⟦ Γ | tbool ⟧ε := ctyval Any ebool bool_err ;
  ⟦ Γ | ttrue ⟧ε := etrue ;
  ⟦ Γ | tfalse ⟧ε := efalse ;
  ⟦ Γ | tif m b P t f ⟧ε :=
    if relm m then
      eif cType ⟦ Γ | b ⟧ε
        (clam cType ebool (cEl (capp (S ⋅ ⟦ Γ | P ⟧ε) (cvar 0))))
        ⟦ Γ | t ⟧ε ⟦ Γ | f ⟧ε (cErr (capp ⟦ Γ | P ⟧ε bool_err))
    else cDummy ;
  ⟦ Γ | bot ⟧ε := ctt ;
  ⟦ Γ | bot_elim m A p ⟧ε := if relm m then ⟦ Γ | A ⟧∅ else cDummy ;
  ⟦ _ | _ ⟧ε := cDummy
}
where "⟦ G | u '⟧ε'" := (erase_term G u)
where "⟦ G | u '⟧τ'" := (cEl ⟦ G | u ⟧ε)
where "⟦ G | u '⟧∅'" := (cErr ⟦ G | u ⟧ε).

Reserved Notation "⟦ G '⟧ε'" (at level 9, G at next level).

Equations erase_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧ε := [] ;
  ⟦ Γ ,, (mx, A) ⟧ε :=
    if relm mx
    then Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
    else None :: ⟦ Γ ⟧ε
}
where "⟦ G '⟧ε'" := (erase_ctx G).

Definition erase_sc (Γ : scope) : cscope :=
  map (λ m, if relm m then Some cType else None) Γ.

(** Erasure of irrelevant terms is cDummy **)

Lemma erase_irr :
  ∀ Γ t,
    relm (md Γ t) = false →
    ⟦ Γ | t ⟧ε = cDummy.
Proof.
  intros Γ t hm.
  induction t in Γ, hm |- *.
  all: try reflexivity.
  all: try discriminate hm.
  - cbn - [mode_inb] in *. unfold relv.
    destruct (nth_error _ _) eqn:e. 2: reflexivity.
    erewrite nth_error_nth in hm. 2: eassumption.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. cbn. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *. eauto.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
Qed.

(** Erasure of context and of variables **)

Lemma erase_sc_var :
  ∀ Γ x m,
    nth_error Γ x = Some m →
    relm m = true →
    nth_error (erase_sc Γ) x = Some (Some cType).
Proof.
  intros Γ x m e hr.
  unfold erase_sc. rewrite nth_error_map.
  rewrite e. cbn - [mode_inb]. rewrite hr. reflexivity.
Qed.

Lemma erase_ctx_var :
  ∀ Γ x m A,
    nth_error Γ x = Some (m, A) →
    relm m = true →
    nth_error ⟦ Γ ⟧ε x = Some (Some (cType, ⟦ skipn (S x) (sc Γ) | A ⟧τ)).
Proof.
  intros Γ x m A e hr.
  induction Γ as [| [my B] Γ ih ] in x, m, A, e, hr |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn - [mode_inb]. rewrite hr. reflexivity.
  - cbn in e. cbn - [mode_inb skipn]. destruct (mode_inb my _) eqn:ey.
    + erewrite ih. 2,3: eauto. reflexivity.
    + cbn - [mode_inb skipn]. erewrite ih. 2,3: eauto. reflexivity.
Qed.

Lemma rscoping_weak :
  ∀ Γ Δ,
    rscoping (Δ ++ Γ) (plus #|Δ|) Γ.
Proof.
  intros Γ Δ. intros n m e.
  rewrite nth_error_app_r. assumption.
Qed.

Lemma rscoping_upren :
  ∀ Γ Δ m ρ,
    rscoping Γ ρ Δ →
    rscoping (m :: Γ) (up_ren ρ) (m :: Δ).
Proof.
  intros Γ Δ m ρ h. intros x mx e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

Lemma rscoping_comp_weak :
  ∀ Γ Δ,
    rscoping_comp (Δ ++ Γ) (plus #|Δ|) Γ.
Proof.
  intros Γ Δ. intros n e.
  rewrite nth_error_app_r. assumption.
Qed.

(** Erasure preserves scoping **)

Lemma erase_scoping :
  ∀ Γ t,
    ccscoping (erase_sc Γ) ⟦ Γ | t ⟧ε cType.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. destruct_if e. 2: constructor.
    constructor. unfold relv in e.
    destruct nth_error eqn:e1. 2: discriminate.
    eapply erase_sc_var. all: eauto.
  - cbn - [mode_inb].
    specialize IHt2 with (Γ := m0 :: Γ). cbn - [mode_inb] in IHt2.
    fold (erase_sc Γ) in IHt2.
    destruct_ifs.
    all: try solve [ eauto with cc_scope cc_type ].
    + destruct (relm m0) eqn:e1. 2: discriminate.
      constructor. all: constructor. all: constructor. all: eauto.
    + destruct m. all: try discriminate.
      destruct m0. all: try discriminate. simpl relm in IHt2. cbn match in IHt2.
      constructor. all: constructor. all: constructor. all: eauto.
      * eapply cscoping_ren. 1: eapply crscoping_S.
        eapply cscope_close. eauto.
      * eapply cscope_ignore. eauto.
    + destruct (relm m0) eqn:e2. 1: discriminate.
      eauto with cc_scope.
  - cbn - [mode_inb].
    specialize IHt3 with (Γ := m :: Γ). cbn - [mode_inb] in IHt3.
    fold (erase_sc Γ) in IHt3.
    destruct_ifs. all: eauto with cc_scope.
  - cbn - [mode_inb]. destruct (relm m) eqn:er. 2: constructor.
    econstructor. all: eauto with cc_scope.
    constructor. 1: constructor.
    constructor. econstructor.
    + eapply cscoping_ren. 1: apply crscoping_S.
      eauto.
    + constructor. reflexivity.
Qed.

(** Erasure commutes with renaming **)

Lemma erase_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧ε = ρ ⋅ ⟦ Δ | t ⟧ε.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  - cbn - [mode_inb].
    unfold relv.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e.
      destruct (relm m). all: reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn - [mode_inb].
    destruct_if e. all: eauto.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct_ifs. all: try solve [ eauto ].
    2:{ unfold close. ssimpl. cbn. unfold cty_lift. ssimpl. reflexivity. }
    ssimpl. cbn. ssimpl. unfold nones. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    erewrite md_ren.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct_ifs. all: eauto.
    unfold close. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite IHt4. 2,3: eassumption.
    destruct_ifs. all: eauto.
    cbn. f_equal. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    destruct_ifs. all: eauto.
Qed.

(** Erasure commutes with substitution **)

Lemma erase_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    ⟦ Γ | t <[ σ ] ⟧ε = ⟦ Δ | t ⟧ε <[ σ >> erase_term Γ ].
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  (* all: try solve [ cbn - [mode_inb] ; destruct_ifs ; ssimpl ; eauto ]. *)
  (* Solves only 1 *)
  - ssimpl. cbn. unfold relv. destruct (nth_error Δ n) eqn:e.
    + destruct (relm m) eqn:em.
      * cbn. ssimpl. reflexivity.
      * cbn. eapply erase_irr. clear hcσ.
        induction hσ as [| σ Δ mx hσ ih hm] in n, m, e, em |- *.
        1: destruct n ; discriminate.
        destruct n.
        -- cbn - [mode_inb] in *.
          erewrite scoping_md. 2: eassumption.
          noconf e. assumption.
        -- cbn in e. eapply ih. all: eassumption.
    + cbn. eapply hcσ in e as e'. destruct e' as [m [e1 e2]].
      rewrite e1. cbn.
      unfold relv. rewrite e2. reflexivity.
  - cbn. destruct_if em.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eauto.
    erewrite IHt2.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ ssimpl. eapply sscoping_comp_shift. assumption. }
    destruct_ifs.
    + cbn. ssimpl. f_equal. all: f_equal. all: f_equal.
      * eapply ext_cterm. intros [].
        -- ssimpl. cbn - [mode_inb]. destruct_if e'. 2: discriminate.
          reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
      * (* cbn - [mode_inb]. destruct_if e'. 2: discriminate. *)
        eapply ext_cterm. intros [].
        -- ssimpl. cbn - [mode_inb]. destruct_if e'. 2: discriminate.
          reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
    + destruct m. all: try discriminate.
      destruct m0. all: try discriminate.
      cbn. ssimpl. f_equal. all: f_equal. all: f_equal.
      * cbn.
        eapply ext_cterm. intros [].
        -- ssimpl. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. rewrite rinstInst'_cterm.
          eapply ext_cterm. intro x.
          cbn. ssimpl. reflexivity.
      * cbn.
        eapply ext_cterm. intros [].
        -- ssimpl. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. rewrite rinstInst'_cterm.
          eapply ext_cterm. intro x.
          cbn. ssimpl. reflexivity.
    + reflexivity.
    + unfold close, cty_lift. ssimpl. cbn - [mode_inb].
      destruct_if e'. 1: discriminate.
      cbn. f_equal.
      * f_equal. eapply ext_cterm. intros [].
        -- cbn. reflexivity.
        -- cbn. ssimpl. erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
      * f_equal. eapply ext_cterm. intros [].
        -- cbn. reflexivity.
        -- cbn. ssimpl. erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    destruct_ifs.
    + erewrite IHt1. 2,3: eauto.
      erewrite IHt3.
      2:{ eapply sscoping_shift. eassumption. }
      2:{ eapply sscoping_comp_shift. assumption. }
      ssimpl. f_equal.
      eapply ext_cterm. intros [].
      * cbn - [mode_inb]. rewrite e0. reflexivity.
      * cbn. ssimpl.
        erewrite erase_ren.
        2:{ eapply rscoping_S. }
        2:{ eapply rscoping_comp_S. }
        ssimpl. reflexivity.
    + unfold close. ssimpl.
      erewrite IHt3.
      2:{ eapply sscoping_shift. eassumption. }
      2:{ eapply sscoping_comp_shift. assumption. }
      ssimpl. eapply ext_cterm. intros [].
      * cbn - [mode_inb]. rewrite e0. reflexivity.
      * cbn. ssimpl.
        erewrite erase_ren.
        2:{ eapply rscoping_S. }
        2:{ eapply rscoping_comp_S. }
        ssimpl. reflexivity.
    + reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eauto.
    erewrite md_subst. 2,3: eauto.
    erewrite IHt1. 2,3: eauto.
    erewrite IHt2. 2,3: eauto.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite IHt4. 2,3: eassumption.
    destruct_ifs. 2: reflexivity.
    cbn. f_equal. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
Qed.

(** Erasure preserves conversion **)

Ltac remd :=
  erewrite !scoping_md by eassumption.

Tactic Notation "remd" "in" hyp(h) :=
  erewrite !scoping_md in h by eassumption.

Lemma erase_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | u ⟧ε ≡ ⟦ sc Γ | v ⟧ε.
Proof.
  intros Γ u v h.
  induction h.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs.
    + eapply cmeta_conv_trans_r. 1: constructor.
      erewrite erase_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped. 1: eapply erase_scoping.
      intros [| x] ex.
      * cbn. reflexivity.
      * cbn. unfold relv. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (relm m0). 2: discriminate.
        reflexivity.
    + unfold close. eapply cmeta_conv_trans_r. 1: constructor.
      erewrite erase_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped. 1: eapply erase_scoping.
      intros [| x] ex.
      * unfold inscope in ex. cbn - [mode_inb] in ex.
        rewrite e0 in ex. discriminate.
      * cbn. unfold relv. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (relm m0). 2: discriminate.
        reflexivity.
    + erewrite erase_irr.
      2:{ erewrite md_subst.
        2:{ eapply sscoping_one. eassumption. }
        2:{ eapply sscoping_comp_one. }
        erewrite scoping_md. 2: eassumption.
        assumption.
      }
      constructor.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    cbn in H2.
    destruct_if e.
    1:{ destruct mp. all: intuition discriminate. }
    constructor.
  - cbn - [mode_inb]. destruct (relm m) eqn:er.
    + constructor.
    + erewrite erase_irr. 2:{ remd. assumption. }
      constructor.
  - cbn - [mode_inb]. destruct (relm m) eqn:er.
    + constructor.
    + erewrite erase_irr. 2:{ remd. assumption. }
      constructor.
  - cbn - [mode_inb]. apply cconv_refl.
  - cbn - [mode_inb].
    cbn - [mode_inb] in IHh2.
    destruct_ifs.
    + destruct (relm mx) eqn:e1. 2: discriminate.
      constructor. all: constructor. all: constructor. all: eauto.
    + destruct m. all: try discriminate.
      destruct mx. all: try discriminate.
      cbn in *. constructor. all: constructor. all: constructor. all: eauto.
      * eapply cconv_ren. 1: eapply crtyping_S.
        eapply cconv_subst. 1:eapply cstyping_one_none.
        eauto.
      * eapply cconv_subst. 2: eauto.
        eapply cstyping_nones.
    + constructor.
    + destruct (relm mx) eqn:e'. 1: discriminate.
      eapply cconv_ty_lift.
      eapply cconv_close. eauto.
  - cbn - [mode_inb].
    cbn - [mode_inb] in IHh2, IHh3.
    eapply conv_md in h3 as e3. simpl in e3. rewrite <- e3.
    destruct_ifs.
    + constructor. 1: constructor. all: eauto.
    + eapply cconv_close. eauto.
    + constructor.
  - cbn - [mode_inb].
    eapply conv_md in h1 as e1. simpl in e1. rewrite <- e1.
    eapply conv_md in h2 as e2. simpl in e2. rewrite <- e2.
    destruct_ifs.
    + constructor. all: eauto.
    + eauto.
    + constructor.
  - cbn - [mode_inb]. eauto.
  - cbn - [mode_inb]. constructor.
  - cbn - [mode_inb]. constructor.
  - cbn - [mode_inb]. constructor.
  - cbn - [mode_inb]. constructor.
  - cbn - [mode_inb]. destruct_if'. 2: constructor.
    constructor. all: eauto.
    all: constructor. all: constructor. 2: auto. 2: econv.
    constructor. 2: constructor.
    eapply cconv_ren.
    + apply crtyping_S.
    + auto.
  - cbn - [mode_inb]. destruct_if'.
    + constructor. eauto.
    + constructor.
  - constructor.
  - constructor. eassumption.
  - eapply cconv_trans. all: eauto.
  - rewrite 2!erase_irr. 1: constructor.
    all: erewrite scoping_md ; [| eassumption ]. all: reflexivity.
Qed.

(** Erasure ignores casts **)

Lemma erase_castrm :
  ∀ Γ t,
    ⟦ Γ | (ε|t|) ⟧ε = ⟦ Γ | t ⟧ε.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try reflexivity.
  - cbn - [mode_inb]. erewrite IHt1, IHt2. reflexivity.
  - cbn - [mode_inb]. erewrite IHt1, IHt3.
    rewrite <- md_castrm. reflexivity.
  - cbn - [mode_inb]. erewrite IHt1, IHt2. rewrite <- !md_castrm. reflexivity.
  - cbn - [mode_inb]. eauto.
  - cbn - [mode_inb]. eauto.
  - cbn - [mode_inb]. erewrite IHt1, IHt2, IHt3, IHt4. reflexivity.
  - cbn - [mode_inb]. erewrite IHt1. reflexivity.
Qed.

(** Erasure of erased conversion **)

Lemma erase_castrm_conv :
  ∀ Γ u v,
    Γ ⊢ u ε≡ v →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | u ⟧ε ≡ ⟦ sc Γ | v ⟧ε.
Proof.
  intros Γ u v h.
  eapply erase_conv in h.
  rewrite !erase_castrm in h.
  assumption.
Qed.

(** Erasure preserves typing **)

Lemma erase_typing_El :
  ∀ Γ Γ' A m i,
    Γ' ⊢ᶜ ⟦ Γ | A ⟧ε : ⟦ Γ | Sort m i ⟧τ →
    isProp m = false →
    Γ' ⊢ᶜ ⟦ Γ | A ⟧τ : cSort cType i.
Proof.
  intros Γ Γ' A m i h hm.
  econstructor. cbn in h. rewrite hm in h.
  econstructor.
  - eassumption.
  - constructor.
  - econstructor.
Qed.

Lemma erase_typing_Err :
  ∀ Γ Γ' A m i,
    Γ' ⊢ᶜ ⟦ Γ | A ⟧ε : ⟦ Γ | Sort m i ⟧τ →
    isProp m = false →
    Γ' ⊢ᶜ ⟦ Γ | A ⟧∅ : ⟦ Γ | A ⟧τ.
Proof.
  intros Γ Γ' A m i h hm.
  econstructor. cbn in h. rewrite hm in h.
  econstructor.
  - eassumption.
  - constructor.
  - econstructor.
Qed.

Theorem erase_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    relm (mdc Γ t) = true →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | t ⟧ε : ⟦ sc Γ | A ⟧τ.
Proof.
  intros Γ t A h hm.
  induction h.
  all: try solve [ cbn in hm ; discriminate ].
  (* all: try solve [ cbn ; eauto using erase_typing_El, erase_typing_Err with cc_scope cc_type ]. *)
  - cbn. unfold relv. unfold sc. rewrite nth_error_map.
    rewrite H. cbn - [mode_inb].
    cbn - [mode_inb] in hm.
    erewrite nth_error_nth in hm.
    2:{ unfold sc. erewrite nth_error_map. erewrite H. reflexivity. }
    cbn - [mode_inb] in hm. rewrite hm.
    cbn. eapply ccmeta_conv.
    + econstructor. eapply erase_ctx_var. all: eassumption.
    + cbn - [skipn]. f_equal.
      erewrite erase_ren.
      * reflexivity.
      * intros y my ey. rewrite <- nth_error_skipn in ey. assumption.
      * intros y ey. rewrite <- nth_error_skipn in ey. assumption.
  - cbn. destruct_if e.
    + econstructor.
      * constructor. all: constructor.
      * apply cconv_sym. eapply cconv_trans. 1: econstructor.
        unfold usup. rewrite e. constructor.
      * repeat econstructor.
    + econstructor.
      * repeat constructor.
      * unfold usup. rewrite e. apply cconv_sym. econstructor.
      * repeat econstructor.
  - cbn - [mode_inb]. cbn - [mode_inb] in IHh1, IHh2.
    destruct_ifs.
    (* repeat (d_if ; cbn - [mode_inb]).
    all: try solve [ destruct m ; discriminate ]. *)
    + (* Redundant case *)
      destruct mx. all: discriminate.
    + destruct (relm mx) eqn:e'. 2: discriminate.
      econstructor.
      * econstructor. all: econstructor.
      (* TODO IH tactic *)
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ destruct mx. all: try discriminate. all: reflexivity.
        -- eapply erase_typing_El. 2: eassumption.
          cbn. rewrite e0. eapply IHh2. erewrite scoping_md. 2: eauto.
          reflexivity.
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ destruct mx. all: try discriminate. all: reflexivity.
        -- eapply erase_typing_Err. 2: eassumption.
          cbn. rewrite e0. eapply IHh2. erewrite scoping_md. 2: eauto.
          reflexivity.
      * unfold umax. rewrite e0.
        destruct_if e1. 1:{ mode_eqs. discriminate. }
        apply cconv_sym. constructor.
      * repeat econstructor.
    + destruct m. all: try discriminate.
    + destruct m. all: try discriminate.
      destruct mx. all: try discriminate.
      ssimpl.
      econstructor.
      * econstructor. all: econstructor.
        -- eapply erase_typing_El. 1: eapply IHh1. 2: reflexivity.
          erewrite scoping_md. 2: eassumption. reflexivity.
        -- econstructor. econstructor.
          ++ eapply ctype_ignore.
            eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. econstructor.
          ++ eauto with cc_scope cc_type.
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ reflexivity.
        -- econstructor. econstructor.
          ++ eapply ctype_ignore.
            eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. constructor.
          ++ eauto with cc_scope cc_type.
      * eapply cconv_sym. constructor.
      * eauto with cc_scope cc_type.
    + econstructor.
      * eauto with cc_scope cc_type.
      * eapply cconv_sym. constructor.
      * eauto with cc_scope cc_type.
    + destruct (relm mx) eqn:e'. 1: discriminate.
      econstructor.
      * eapply ctype_ty_lift with (j := umax mx m i j).
        -- econstructor.
          ++ eapply ctype_close. eapply IHh2.
            erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. constructor.
          ++ eauto with cc_type.
        -- unfold umax. rewrite e1. destruct_ifs. all: lia.
      * apply cconv_sym. constructor.
      * eauto with cc_scope cc_type.
  - cbn - [mode_inb]. cbn - [mode_inb] in IHh1, IHh2, IHh3.
    repeat (erewrite scoping_md ; [| eassumption]).
    cbn - [mode_inb] in hm.
    erewrite scoping_md in hm. 2: eassumption.
    rewrite hm.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh2. 2: eassumption.
    erewrite scoping_md in IHh3. 2: eassumption.
    rewrite hm in IHh3.
    destruct_ifs. all: try discriminate.
    + destruct (isProp m) eqn:e'. 1: discriminate.
      destruct (isProp mx) eqn:ex.
      1:{ destruct mx ; discriminate. }
      econstructor.
      * econstructor.
        -- eapply erase_typing_El. 2: eassumption.
          econstructor.
          ++ eauto.
          ++ cbn. rewrite e'. eapply cconv_trans. 1: constructor.
            apply cconv_sym. constructor.
          ++ eapply erase_typing_El with (m := mKind). 2: reflexivity.
            cbn. rewrite e'.
            econstructor.
            ** eauto with cc_type.
            ** apply cconv_sym. constructor.
            ** eauto with cc_type.
        -- eauto.
      * apply cconv_sym. constructor.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        -- econstructor.
          ++ eauto.
          ++ constructor.
          ++ eauto with cc_type.
        -- eapply erase_typing_El.
          ++ cbn. rewrite ex. econstructor.
            ** eauto.
            ** eapply cconv_trans. 1: constructor.
              apply cconv_sym. constructor.
            ** econstructor. econstructor. all: econstructor.
          ++ assumption.
        -- econstructor.
          ++ eapply erase_typing_El.
            ** cbn. rewrite ex. eauto.
            ** assumption.
          ++ eapply erase_typing_Err.
            ** cbn. rewrite ex. econstructor.
              --- eauto.
              --- eapply cconv_trans. 1: constructor.
                apply cconv_sym. constructor.
              --- econstructor. econstructor. all: econstructor.
            ** assumption.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + econstructor.
      * eapply ctype_close. eauto.
      * apply cconv_sym. unfold cty_lift.
        eapply cconv_trans. 1: constructor.
        unfold close. cbn. apply cconv_refl.
      * econstructor. eapply ctype_ty_lift.
        -- econstructor.
          ++ eapply ctype_close. eauto.
          ++ cbn. constructor.
          ++ eauto with cc_type.
        -- reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md in hm. 2: eassumption.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh2. 2: eassumption.
    erewrite scoping_md in IHh3. 2: eassumption.
    erewrite scoping_md in IHh4. 2: eassumption.
    repeat (erewrite scoping_md ; [| eassumption]).
    rewrite hm.
    destruct_ifs.
    + destruct (isProp m) eqn:e1. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      destruct (isProp mx) eqn:e2. 1:{ destruct mx ; discriminate. }
      eapply ccmeta_conv.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        econstructor.
        -- eauto.
        -- constructor.
        -- unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
          ++ econstructor.
            ** eauto.
            ** constructor.
            ** eauto with cc_type.
          ++ econstructor.
            ** eauto.
            ** constructor.
            ** eauto with cc_type.
      * cbn. f_equal. erewrite erase_subst.
        2: eapply sscoping_one. 2: eassumption.
        2: eapply sscoping_comp_one.
        ssimpl.
        eapply ext_cterm_scoped. 1: eapply erase_scoping.
        intros [| x] ex.
        -- cbn. reflexivity.
        -- cbn. unfold relv. unfold inscope in ex.
          cbn - [mode_inb] in ex.
          rewrite nth_error_map in ex.
          destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct (relm m0). 2: discriminate.
          reflexivity.
    + destruct (isProp m) eqn:e1. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      destruct (isGhost m) eqn:e2. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      erewrite erase_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      erewrite ext_cterm_scoped with (θ := ctt..).
      2: eapply erase_scoping.
      2:{
        intros [| x] ex.
        - unfold inscope in ex. cbn - [mode_inb] in ex.
          rewrite e in ex. discriminate.
        - cbn. unfold relv. unfold inscope in ex.
          cbn - [mode_inb] in ex.
          rewrite nth_error_map in ex.
          destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct (relm m0). 2: discriminate.
          reflexivity.
      }
      econstructor.
      * eauto.
      * unfold cty_lift. eapply cconv_trans. 1: constructor.
        apply cconv_refl.
      * econstructor.
        econstructor.
        -- eapply ctype_close. eauto.
        -- cbn. constructor.
        -- eauto with cc_type.
  - erewrite scoping_md in IHh. 2: eassumption.
    cbn. econstructor.
    + eauto.
    + apply cconv_sym. cbn. eapply cconv_trans. 1: constructor.
      apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb] in hm. erewrite scoping_md in hm. 2: eassumption.
    destruct m. all: discriminate.
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb].
    cbn - [mode_inb] in hm. erewrite scoping_md in hm. 2: eassumption.
    repeat (erewrite scoping_md ; [| eassumption]). cbn.
    cbn - [mode_inb] in IHh6.
    repeat (erewrite scoping_md in IHh6 ; [| eassumption]).
    rewrite hm in IHh6.
    cbn in IHh6. eauto.
  - cbn. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb]. cbn - [mode_inb] in hm. rewrite hm.
    remd. cbn.
    remd in IHh1. forward IHh1 by reflexivity. cbn in IHh1.
    eapply ctype_conv in IHh1.
    2:{ constructor. }
    2:{ eauto with cc_type. }
    remd in IHh2. forward IHh2 by reflexivity. cbn in IHh2.
    destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
    eapply ctype_conv in IHh2.
    2:{
      eapply cconv_trans. 1: constructor.
      econstructor. all: constructor.
    }
    2:{ eauto with cc_type. }
    remd in IHh3. forward IHh3 by assumption. cbn - [mode_inb] in IHh3.
    remd in IHh3. cbn in IHh3.
    remd in IHh4. forward IHh4 by assumption. cbn - [mode_inb] in IHh4.
    remd in IHh4. cbn in IHh4.
    econstructor.
    + econstructor.
      * assumption.
      * {
        econstructor. 1: eauto with cc_type.
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
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb]. cbn - [mode_inb] in hm.
    rewrite hm. eapply erase_typing_Err.
    + eapply IHh1. erewrite scoping_md. 2: eassumption.
      reflexivity.
    + destruct m. all: try reflexivity. discriminate.
  - econstructor.
    + eauto.
    + constructor. eapply erase_castrm_conv. assumption.
    + eapply erase_typing_El.
      * eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
      * erewrite scoping_md in hm. 2: eassumption.
        destruct m. all: try reflexivity. discriminate.
Qed.

Corollary erase_context :
  ∀ Γ,
    wf Γ →
    cwf ⟦ Γ ⟧ε.
Proof.
  intros Γ h.
  induction h.
  - constructor.
  - cbn - [mode_inb]. destruct (relm m) eqn:er.
    + constructor. 1: assumption.
      cbn. exists i. eapply erase_typing_El.
      * eapply erase_typing. 1: eassumption.
        erewrite scoping_md. 2: eassumption.
        reflexivity.
      * destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
        reflexivity.
    + constructor. 2: constructor. assumption.
Qed.

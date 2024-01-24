From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CScoping
  Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure.
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
  ⟦ Γ | ghcast e P t ⟧v := ⟦ Γ | t ⟧v ;
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

Lemma scoping_to_rev :
  ∀ Γ t m,
    ccscoping (erase_sc Γ) t m →
    ccscoping (revive_sc Γ) t m.
Proof.
  intros Γ t m h.
  eapply cscoping_ren in h. 2: eapply scoping_sub_rev.
  rewrite rinstId'_cterm in h. assumption.
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
  ∀ Γ t m,
    m = mGhost →
    scoping Γ t m →
    ccscoping (revive_sc Γ) ⟦ Γ | t ⟧v cType.
Proof.
  intros Γ t m em h.
  induction h in em |- *. all: subst.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. destruct_if e. 2: constructor.
    constructor. eapply revive_sc_var. assumption.
  - cbn - [mode_inb].
    cbn - [mode_inb] in IHh3. fold (revive_sc Γ) in IHh3.
    erewrite scoping_md. 2: eassumption. cbn.
    destruct_ifs.
    + eauto with cc_scope.
    + constructor.
      * constructor. eapply scoping_to_rev. eapply erase_scoping. 2: eauto.
        reflexivity.
      * eauto.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    cbn - [mode_inb].
    destruct_ifs. 3: eauto with cc_scope.
    + econstructor. 1: eauto.
      eapply scoping_to_rev. eapply erase_scoping. 2: eauto.
      assumption.
    + destruct mx. all: try discriminate.
      eauto with cc_scope.
  - cbn - [mode_inb].
    eapply scoping_to_rev. eapply erase_scoping. 2: eauto.
    reflexivity.
  - cbn - [mode_inb].
    constructor.
    eapply scoping_to_rev. eapply erase_scoping. 2: eauto.
    reflexivity.
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
  eapply ext_cterm_scoped. 1: eapply erase_scoping_strong. intros x hx.
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
    destruct_ifs. 2: reflexivity.
    erewrite erase_subst. 2,3: eassumption.
    cbn. f_equal. apply erase_rev_subst.
Qed.

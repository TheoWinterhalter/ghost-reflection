(*** Parametricity ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Variables and parametricity

  x : A in the context is translated to x : A, xP : AP when A is not a Prop.
  When x : P : Prop then x is translated to only one variable. To keep the
  context regular we will still make use of our flexible contexts.
  Variables are then either odd and regular or even and correspond to
  parametricity.

**)

Definition vreg x := S (x * 2).
Definition vpar x := x * 2.

(** Lifting erasure and revival

  Because erasure and revival produce terms in ⟦ Γ ⟧ε and ⟦ Γ ⟧v respectively
  when we expect ⟦ Γ ⟧p, we need to do some lifting. Thankfully this lifting
  can be done simply by using vreg as a renaming.
  We define handy notations to make it all work.

**)

Definition epm_lift (t : cterm) :=
  vreg ⋅ t.

Definition rpm_lift (t : cterm) :=
  vreg ⋅ t.

Notation "⟦ G | u '⟧pε'":=
  (epm_lift ⟦ G | u ⟧ε) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧pτ'":=
  (epm_lift ⟦ G | u ⟧τ) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧p∅'":=
  (epm_lift ⟦ G | u ⟧∅) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧pv'":=
  (rpm_lift ⟦ G | u ⟧v) (at level 9, G, u at next level).

(** Parametricity translation

  We start by defining useful shorthands.

**)

Definition pKind i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cType i).

Definition pType i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cProp 0).

Definition pProp :=
  clam cType (cty 0) (cSort cProp 0).

(* ∀ (x : A) (x@mp : B x). C *)
Definition pPi mp A B C :=
  cPi cType A (cPi mp (capp (S ⋅ B) (cvar 0)) C).

Definition plam mp A B t :=
  clam cType A (clam mp (capp (S ⋅ B) (cvar 0)) t).

Definition pcastTG Ae AP uv vv vP eP PP te tP :=
  sq_elim
    eP
    (clam cProp (squash (teq Ae uv vv)) (S ⋅ (capp (capp (capp PP vv) vP) te)))
    (clam cType (teq Ae uv vv) (
      capp
        (tJ
          (cvar 0)
          (S ⋅ (clam cType Ae (
            clam cType (teq (S ⋅ Ae) (S ⋅ uv) (cvar 0)) (
              cPi cProp (capp (plus 2 ⋅ AP) (cvar 1)) (
                capp (capp (capp (plus 3 ⋅ PP) (cvar 2)) (cvar 0)) (plus 3 ⋅ te)
              )
            )
          )))
          (S ⋅ (clam cProp (capp AP uv) (S ⋅ tP))))
        (S ⋅ vP)
    )).

Definition pcastP Ae AP uv vv vP eP PP tP :=
  sq_elim
    eP
    (clam cProp (squash (teq Ae uv vv)) (S ⋅ (capp (capp PP vv) vP)))
    (clam cType (teq Ae uv vv) (
      capp
        (tJ
          (cvar 0)
          (S ⋅ (clam cType Ae (
            clam cType (teq (S ⋅ Ae) (S ⋅ uv) (cvar 0)) (
              cPi cProp (capp (plus 2 ⋅ AP) (cvar 1)) (
                capp (capp (plus 3 ⋅ PP) (cvar 2)) (cvar 0)
              )
            )
          )))
          (S ⋅ (clam cProp (capp AP uv) (S ⋅ tP))))
        (S ⋅ vP)
    )).

Reserved Notation "⟦ G | u '⟧p'" (at level 9, G, u at next level).

Equations param_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧p :=
    match nth_error Γ x with
    | Some m => cvar (if isProp m then vreg x else vpar x)
    | None => cDummy
    end ;
  ⟦ Γ | Sort m i ⟧p :=
    if isKind m then pKind i
    else if isProp m then pProp
    else pType i ;
  ⟦ Γ | Pi i j m mx A B ⟧p :=
    let Te := ⟦ Γ | Pi i j m mx A B ⟧pε in
    let Ae := ⟦ Γ | A ⟧pε in
    let Ap := ⟦ Γ | A ⟧p in
    let Bp := ⟦ mx :: Γ | B ⟧p in
    let k := umax m i j in
    match m with
    | mKind =>
      clam cType (capp (pKind k) Te) (
        match mx with
        | mKind => pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mType => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mGhost => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (cvar 2))
        | mProp => cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        end
      )
    | mType =>
      clam cProp (capp (pKind k) Te) (
        match mx with
        | mKind => pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mType => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mGhost => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (cvar 2))
        | mProp => cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        end
      )
    | mGhost =>
      clam cProp (capp (pKind k) Te) (
        if isKind mx then pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        else if isProp mx then cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        else pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
      )
    | mProp =>
      if isProp mx then cPi cProp Ap (close Bp)
      else if isKind mx then pPi cType Ae Ap Bp
      else pPi cProp Ae Ap Bp
    end ;
  ⟦ Γ | lam mx A B t ⟧p :=
    if isProp mx then clam cProp ⟦ Γ | A ⟧p (close ⟦ mx :: Γ | t ⟧p)
    else if isKind mx then plam cType ⟦ Γ | A ⟧pε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p
    else plam cProp ⟦ Γ | A ⟧pε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p ;
  ⟦ Γ | app u v ⟧p :=
    if relm (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧pε) ⟦ Γ | v ⟧p
    else if isGhost (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧pv) ⟦ Γ | v ⟧p
    else capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧p
  ;
  ⟦ Γ | Erased A ⟧p :=
    if isKind (md Γ A) then ⟦ Γ | A ⟧p else cDummy ;
  ⟦ Γ | hide t ⟧p :=
    if isType (md Γ t) then ⟦ Γ | t ⟧p else cDummy ;
  ⟦ Γ | reveal t P p ⟧p :=
    if relm (md Γ p) then cDummy
    else capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧pv) ⟦ Γ | t ⟧p ;
  ⟦ Γ | revealP t p ⟧p :=
    if isKind (md Γ p) then capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧pv) ⟦ Γ | t ⟧p
    else cDummy ;
  ⟦ Γ | gheq A u v ⟧p := squash (teq ⟦ Γ | A ⟧pε ⟦ Γ | u ⟧pv ⟦ Γ | v ⟧pv) ;
  ⟦ Γ | ghrefl A u ⟧p := sq (trefl ⟦ Γ | A ⟧pε ⟦ Γ | u ⟧pv) ;
  ⟦ Γ | ghcast A u v e P t ⟧p :=
    let eP := ⟦ Γ | e ⟧p in
    let PP := ⟦ Γ | P ⟧p in
    let uv := ⟦ Γ | u ⟧pv in
    let vv := ⟦ Γ | v ⟧pv in
    let vP := ⟦ Γ | v ⟧p in
    let Ae := ⟦ Γ | A ⟧pε in
    let AP := ⟦ Γ | A ⟧p in
    let te := ⟦ Γ | t ⟧pε in
    let tv := ⟦ Γ | t ⟧pv in
    let tP := ⟦ Γ | t ⟧p in
    match md Γ t with
    | mKind => tP (* Not cDummy for technical reasons *)
    | mType => pcastTG Ae AP uv vv vP eP PP te tP
    | mGhost => pcastTG Ae AP uv vv vP eP PP tv tP
    | mProp => pcastP Ae AP uv vv vP eP PP tP
    end ;
  ⟦ Γ | bot ⟧p := cbot ;
  ⟦ Γ | bot_elim m A p ⟧p :=
    if isProp m then cbot_elim cProp ⟦ Γ | A ⟧p ⟦ Γ | p ⟧p
    else if isKind m then cbot_elim cType (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧p∅) ⟦ Γ | p ⟧p
    else cbot_elim cProp (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧p∅) ⟦ Γ | p ⟧p
}
where "⟦ G | u '⟧p'" := (param_term G u).

Reserved Notation "⟦ G '⟧p'" (at level 9, G at next level).

Equations param_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧p := [] ;
  ⟦ Γ ,, (mx, A) ⟧p :=
    if isProp mx then None :: Some (cProp, ⟦ sc Γ | A ⟧p) :: ⟦ Γ ⟧p
    else if isKind mx then
      Some (cType, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧pτ) :: ⟦ Γ ⟧p
    else
      Some (cProp, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧pτ) :: ⟦ Γ ⟧p
}
where "⟦ G '⟧p'" := (param_ctx G).

Fixpoint param_sc (Γ : scope) : cscope :=
  match Γ with
  | [] => []
  | m :: Γ =>
    if isProp m then None :: Some cProp :: param_sc Γ
    else if isKind m then Some cType :: Some cType :: param_sc Γ
    else Some cProp :: Some cType :: param_sc Γ
  end.

(** Scope lookups **)

Lemma nth_error_param_vreg :
  ∀ Γ x,
    nth_error (param_sc Γ) (vreg x) =
    option_map (λ m, if isProp m then Some cProp else Some cType) (nth_error Γ x).
Proof.
  intros Γ x.
  induction Γ as [| m Γ ih] in x |- *.
  - destruct x. all: reflexivity.
  - destruct x.
    + cbn. destruct_ifs. all: reflexivity.
    + unfold vreg. simpl "*". remember (S (x * 2)) as y eqn:e.
      cbn. subst. destruct_ifs. all: eapply ih.
Qed.

Lemma nth_error_param_vpar :
  ∀ Γ x,
    nth_error (param_sc Γ) (vpar x) =
    option_map (λ m,
      if isProp m then None
      else if isKind m then Some cType
      else Some cProp
    ) (nth_error Γ x).
Proof.
  intros Γ x.
  induction Γ as [| m Γ ih] in x |- *.
  - destruct x. all: reflexivity.
  - destruct x.
    + cbn. destruct_ifs. all: reflexivity.
    + cbn. destruct_ifs. all: eapply ih.
Qed.

(** ⟦ Γ ⟧v is a sub-context of ⟦ Γ ⟧p **)

Lemma scoping_rev_sub_param :
  ∀ Γ,
    crscoping (param_sc Γ) vreg (revive_sc Γ).
Proof.
  intros Γ. intros x m e.
  unfold revive_sc in e. rewrite nth_error_map in e.
  rewrite nth_error_param_vreg.
  destruct (nth_error Γ x) as [mx|] eqn:ex. 2: discriminate.
  cbn - [mode_inb] in e. cbn - [mode_inb].
  destruct_ifs. 1: discriminate.
  assumption.
Qed.

Hint Resolve scoping_rev_sub_param : cc_scope.

Lemma typing_rev_sub_param :
  ∀ Γ,
    crtyping ⟦ Γ ⟧p vreg ⟦ Γ ⟧v.
Proof.
  intros Γ. intros x m A e.
  assert (h : nth_error ⟦ Γ ⟧p (vreg x) = Some (Some (m, vreg ⋅ A))).
  { induction Γ as [| [my B] Γ ih] in x, m, A, e |- *.
    1:{ destruct x. all: discriminate. }
    destruct x.
    - cbn - [mode_inb] in e.
      destruct (isProp my) eqn:ey. 1: discriminate.
      noconf e. cbn. rewrite ey.
      destruct_if e1. all: reflexivity.
    - cbn - [mode_inb] in e.
      unfold vreg. simpl "*". remember (S (x * 2)) as z eqn:ez.
      cbn - [mode_inb]. subst.
      destruct_if ey.
      + eapply ih. assumption.
      + destruct_if e1.
        * eapply ih. assumption.
        * eapply ih. assumption.
  }
  eexists. split.
  - eassumption.
  - ssimpl. unfold vreg. cbn. ssimpl. eapply extRen_cterm.
    intro. ssimpl. lia.
Qed.

(** ⟦ Γ ⟧ε is a sub-context of ⟦ Γ ⟧p **)

Lemma crscoping_comp :
  ∀ Γ Δ Ξ ρ δ,
    crscoping Γ ρ Δ →
    crscoping Δ δ Ξ →
    crscoping Γ (δ >> ρ) Ξ.
Proof.
  intros Γ Δ Ξ ρ δ hρ hδ.
  intros x m e.
  unfold_funcomp. eapply hρ. eapply hδ. assumption.
Qed.

Lemma scoping_er_sub_param :
  ∀ Γ,
    crscoping (param_sc Γ) vreg (erase_sc Γ).
Proof.
  intros Γ.
  pose proof (scoping_sub_rev Γ) as lem.
  eapply crscoping_comp in lem. 2: eapply scoping_rev_sub_param.
  eapply crscoping_morphism. all: eauto.
  intros x. reflexivity.
Qed.

Hint Resolve scoping_er_sub_param : cc_scope.

Lemma crtyping_comp :
  ∀ Γ Δ Ξ ρ δ,
    crtyping Γ ρ Δ →
    crtyping Δ δ Ξ →
    crtyping Γ (δ >> ρ) Ξ.
Proof.
  intros Γ Δ Ξ ρ δ hρ hδ.
  intros x m A e.
  eapply hδ in e as [B [e eB]].
  eapply hρ in e as [C [e eC]].
  eexists. split.
  - eassumption.
  - eapply (f_equal (λ A, ρ ⋅ A)) in eB.
    revert eB eC. ssimpl. intros eB eC.
    rewrite eB. assumption.
Qed.

Lemma typing_er_sub_param :
  ∀ Γ,
    crtyping ⟦ Γ ⟧p vreg ⟦ Γ ⟧ε.
Proof.
  intros Γ.
  pose proof (typing_sub_rev Γ) as lem.
  eapply crtyping_comp in lem. 2: eapply typing_rev_sub_param.
  eapply crtyping_morphism. all: eauto.
  intros x. reflexivity.
Qed.

(** Parametricity preserves scoping **)

Lemma scoping_epm_lift :
  ∀ Γ Γ' t,
    ccscoping (erase_sc Γ) t cType →
    Γ' = param_sc Γ →
    ccscoping Γ' (epm_lift t) cType.
Proof.
  intros Γ Γ' t h ->.
  eapply cscoping_ren.
  - eapply scoping_er_sub_param.
  - assumption.
Qed.

(* Hint Resolve scoping_epm_lift | 1000 : cc_scope. *)

Lemma pscoping_erase_term :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pε cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - eapply erase_scoping.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_term : cc_scope.

Lemma pscoping_erase_type :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pτ cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - constructor. eapply erase_scoping.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_type : cc_scope.

Lemma pscoping_erase_err :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧p∅ cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - constructor. eapply erase_scoping.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_err : cc_scope.

Lemma scoping_rpm_lift :
  ∀ Γ Γ' t,
    ccscoping (revive_sc Γ) t cType →
    Γ' = param_sc Γ →
    ccscoping Γ' (rpm_lift t) cType.
Proof.
  intros Γ Γ' t h ->.
  eapply cscoping_ren.
  - eapply scoping_rev_sub_param.
  - assumption.
Qed.

(* Hint Resolve scoping_rpm_lift | 1000 : cc_scope. *)

Lemma pscoping_revive :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pv cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_rpm_lift.
  - eapply revive_scoping.
  - reflexivity.
Qed.

Hint Resolve pscoping_revive : cc_scope.

Lemma erase_scoping_eq :
  ∀ Γ Γ' t,
    Γ' = erase_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧ε cType.
Proof.
  intros Γ ? t ->.
  eapply erase_scoping.
Qed.

Lemma revive_scoping_eq :
  ∀ Γ Γ' t,
    Γ' = revive_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧v cType.
Proof.
  intros Γ ? t ->.
  eapply revive_scoping.
Qed.

Hint Resolve erase_scoping_eq : cc_scope.
Hint Resolve revive_scoping_eq : cc_scope.
Hint Resolve revive_scoping : cc_scope.
Hint Resolve cscoping_ren : cc_scope.
Hint Resolve crscoping_S : cc_scope.
Hint Resolve crscoping_plus : cc_scope.

Lemma pPi_scoping :
  ∀ Γ mx A B C,
    ccscoping Γ A cType →
    ccscoping Γ B cType →
    ccscoping (Some mx :: Some cType :: Γ) C cType →
    ccscoping Γ (pPi mx A B C) cType.
Proof.
  intros Γ mx A B C hA hB hC.
  unshelve eauto with cc_scope shelvedb ; shelve_unifiable.
  constructor. reflexivity.
Qed.

Hint Resolve pPi_scoping : cc_scope.

(* So that they're not unfolded too eagerly *)
Opaque epm_lift rpm_lift.

Lemma param_scoping :
  ∀ Γ t m,
    scoping Γ t m →
    ccscoping (param_sc Γ) ⟦ Γ | t ⟧p (if isKind m then cType else cProp).
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. rewrite H. destruct_if e.
    + mode_eqs. cbn. constructor.
      rewrite nth_error_param_vreg. rewrite H. reflexivity.
    + constructor. rewrite nth_error_param_vpar. rewrite H.
      cbn. rewrite e. destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    destruct m, mx. all: cbn in *.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      1:{
        eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      }
      eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
  - cbn - [mode_inb] in *. destruct_ifs. all: mode_eqs. all: cbn in *.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    cbn. assumption.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs. all: try intuition discriminate.
    1:{ destruct m. all: intuition discriminate. }
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    reflexivity.
  - cbn - [mode_inb] in *.
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    all: reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    destruct m. 1: contradiction.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
  - cbn - [mode_inb] in *.
    destruct_ifs. all: mode_eqs. all: try discriminate.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
Qed.

(** Parametricity commutes with renaming

  For this we define pren ρ which is basically the following function:
  pren ρ (2 * n) = 2 * (ρ n)
  pren ρ (2 * n + 1) = 2 * (ρ n) + 1

**)

Definition pren (ρ : nat → nat) :=
  λ n, PeanoNat.Nat.b2n (Nat.odd n) + 2 * ρ (Nat.div2 n).

Lemma pren_even :
  ∀ ρ n,
    pren ρ (n * 2) = (ρ n) * 2.
Proof.
  intros ρ n.
  unfold pren.
  replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.div2_double.
  rewrite PeanoNat.Nat.odd_mul. cbn. lia.
Qed.

Lemma pren_odd :
  ∀ ρ n,
    pren ρ (S (n * 2)) = S ((ρ n) * 2).
Proof.
  intros ρ n.
  unfold pren.
  replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.div2_succ_double.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. cbn. lia.
Qed.

Lemma div2_SS :
  ∀ n, Nat.div2 (S (S n)) = S (Nat.div2 n).
Proof.
  intro n.
  destruct (PeanoNat.Nat.Even_Odd_dec n) as [h | h].
  - rewrite <- PeanoNat.Nat.Odd_div2.
    2:{ apply PeanoNat.Nat.Odd_succ. assumption. }
    rewrite <- PeanoNat.Nat.Even_div2. 2: assumption.
    reflexivity.
  - rewrite <- PeanoNat.Nat.Even_div2.
    2:{ apply PeanoNat.Nat.Even_succ. assumption. }
    rewrite <- PeanoNat.Nat.Odd_div2. 2: assumption.
    reflexivity.
Qed.

Lemma pren_SS :
  ∀ ρ n, pren ρ (S (S n)) = pren (S >> ρ) n.
Proof.
  intros ρ n.
  unfold pren.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_succ.
  rewrite div2_SS. reflexivity.
Qed.

Lemma pren_comp_S :
  ∀ ρ n, pren (ρ >> S) n = S (S (pren ρ n)).
Proof.
  intros ρ n.
  unfold pren. ssimpl. lia.
Qed.

Lemma pren_id :
  ∀ n, pren id n = n.
Proof.
  intros n.
  unfold pren.
  rewrite PeanoNat.Nat.div2_div.
  symmetry. etransitivity. 1: eapply PeanoNat.Nat.div_mod_eq with (y := 2).
  rewrite <- PeanoNat.Nat.bit0_mod.
  rewrite PeanoNat.Nat.bit0_odd.
  unfold id. unfold Datatypes.id. lia.
Qed.

Transparent epm_lift rpm_lift.

Lemma pren_epm_lift :
  ∀ ρ t,
    pren ρ ⋅ epm_lift t = epm_lift (ρ ⋅ t).
Proof.
  intros ρ t.
  unfold epm_lift. ssimpl.
  eapply extRen_cterm. intro x.
  unfold vreg, pren. ssimpl.
  replace (x * 2) with (2 * x) by lia.
  rewrite PeanoNat.Nat.div2_succ_double.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. cbn. lia.
Qed.

Lemma pren_rpm_lift :
  ∀ ρ t,
    pren ρ ⋅ rpm_lift t = rpm_lift (ρ ⋅ t).
Proof.
  intros ρ t.
  apply pren_epm_lift.
Qed.

Opaque epm_lift rpm_lift.

Lemma param_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧p = (pren ρ) ⋅ ⟦ Δ | t ⟧p.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  - cbn - [mode_inb].
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e as e'. rewrite e'.
      destruct_if e1.
      * unfold vreg, pren. ssimpl. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_succ_double.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_mul. cbn. lia.
      * unfold pren, vpar. ssimpl. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_double.
        rewrite PeanoNat.Nat.odd_mul. cbn. lia.
    + eapply hcρ in e as e'. rewrite e'. reflexivity.
  - cbn - [mode_inb]. destruct_ifs. all: reflexivity.
  - cbn - [mode_inb]. unfold pPi.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    erewrite ?erase_ren, ?revive_ren.
    2-5: eauto using rscoping_upren, rscoping_comp_upren.
    rewrite ?pren_epm_lift, ?pren_rpm_lift.
    destruct m, m0. all: cbn in *. (* all: try reflexivity. *)
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. unfold close. ssimpl.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    unfold plam.
    erewrite erase_ren. 2,3: eassumption.
    destruct_ifs. all: mode_eqs.
    + cbn. unfold close. ssimpl. f_equal.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + cbn. rewrite pren_epm_lift. ssimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + cbn. rewrite pren_epm_lift. ssimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_ren. 2,3: eassumption.
    erewrite revive_ren. 2,3: eassumption.
    rewrite <- pren_epm_lift. rewrite <- pren_rpm_lift.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. erewrite IHt3. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 2: reflexivity.
    cbn. erewrite IHt2. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite ?erase_ren, ?revive_ren. 2-7: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite ?erase_ren, ?revive_ren. 2-5: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-11: eassumption.
    destruct (md _ _).
    + eauto.
    + unfold pcastTG. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      2:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. f_equal.
      ssimpl. reflexivity.
    + unfold pcastTG. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      2:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. f_equal.
      ssimpl. reflexivity.
    + unfold pcastP. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. reflexivity.
  - cbn - [mode_inb]. reflexivity.
  - cbn - [mode_inb]. destruct_ifs. all: mode_eqs.
    + cbn. f_equal. all: eauto.
    + cbn. f_equal. 1: f_equal. all: eauto.
      erewrite erase_ren. 2,3: eassumption.
      rewrite pren_epm_lift. reflexivity.
    + cbn. f_equal. 1: f_equal. all: eauto.
      erewrite erase_ren. 2,3: eassumption.
      rewrite pren_epm_lift. reflexivity.
Qed.

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
  unfold psubst. rewrite div2_SS. cbn - [mode_inb].
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
  cbn - [mode_inb] in hx. destruct (relm m) eqn:e1. 2: discriminate.
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
  - cbn - [mode_inb]. destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    unfold pPi.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    erewrite !erase_subst.
    2-5: eauto using sscoping_shift, sscoping_comp_shift with cc_scope.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
    destruct m, m0. all: cbn in *.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      all: f_equal. all: f_equal.
      all: eapply ext_cterm. all: ssimpl. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      all: f_equal. all: f_equal.
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
      cbn. unfold cty_lift. f_equal. all: f_equal.
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
      cbn. f_equal. all: f_equal. all: f_equal.
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
      cbn. f_equal. all: f_equal. all: f_equal.
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
      cbn. unfold cty_lift. f_equal. all: f_equal. all: unfold close.
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
      cbn. unfold cty_lift. f_equal. all: f_equal. all: unfold close.
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
      cbn. f_equal. all: f_equal. all: f_equal.
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
      cbn. f_equal. all: f_equal. all: f_equal.
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
      cbn. f_equal. all: f_equal. all: f_equal.
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
      cbn. unfold cty_lift. f_equal. all: f_equal. all: unfold close.
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
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    erewrite erase_subst. 2,3: eassumption.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
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
      * ssimpl. eapply ext_cterm. intros [| []]. all: cbn - [mode_inb].
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- rewrite psubst_SS. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_subst. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite !revive_subst. 2-5: eassumption.
    erewrite !erase_subst. 2,3: eassumption.
    erewrite <- !psubst_rpm_lift. 2,3: eapply revive_scoping.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
    reflexivity.
  - cbn - [mode_inb].
    erewrite erase_subst. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    erewrite <- psubst_rpm_lift. 2: eapply revive_scoping.
    erewrite <- psubst_epm_lift. 2: eapply erase_scoping.
    reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite IHt4. 2,3: eassumption.
    erewrite IHt5. 2,3: eassumption.
    erewrite IHt6. 2,3: eassumption.
    erewrite !erase_subst. 2-5: eassumption.
    erewrite !revive_subst. 2-7: eassumption.
    erewrite <- !psubst_rpm_lift. 2-4: eapply revive_scoping.
    erewrite <- !psubst_epm_lift. 2,3: eapply erase_scoping.
    destruct md eqn:e.
    + reflexivity.
    + unfold pcastTG. cbn. ssimpl. reflexivity.
    + unfold pcastTG. cbn. ssimpl. reflexivity.
    + unfold pcastP. cbn. ssimpl. reflexivity.
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

Lemma param_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | u ⟧p ≡ ⟦ sc Γ | v ⟧p.
Proof.
  intros Γ u v h.
  induction h.
  (* all: try solve [ cbn ; destruct_ifs ; eauto with cc_conv ]. *)
  - cbn - [mode_inb].
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
      (* The following we do basically four times, but I don't know how
        to factorise.
      *)
      intros [| []] hx. all: cbn. 1,2: reflexivity.
      unfold inscope in hx. cbn in hx.
      unfold psubst. rewrite div2_SS. cbn - [mode_inb].
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
      unfold psubst. rewrite div2_SS. cbn - [mode_inb].
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
      unfold psubst. rewrite div2_SS. cbn - [mode_inb].
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
      unfold psubst. rewrite div2_SS. cbn - [mode_inb].
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
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    destruct_if e.
    1:{
      destruct H2 as [emp | [ emp | ]]. 3: contradiction.
      all: subst. all: discriminate.
    }
    cbn. apply cconv_refl.
  - cbn - [mode_inb].
    erewrite md_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    cbn.
    (* In the end, this still doesn't work.
      Two options:
      - Give up on this conversion rule and have it only as a logical
        equivalence, which it basically is already.
        In that case we see revealP as a type constructor and maybe we call it
        Reveal.
      - Change the parametricity translation of revealP so that it prepends
        ⊤ ⇒.
    *)
    admit.
  - cbn - [mode_inb]. apply cconv_refl.
  - cbn - [mode_inb].
    destruct m, mx. all: simpl.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      (* TODO Problem:
        for cty I have different universes and that's not great
        It might be better to give up on those weird sort conversions and
        instead give up on uniqueness of type. We could then revert some changes
        made to the syntax. This means that we may have to give up on getting
        rid of redundant annotations which is not great though.
      *)
Abort.

(** Parametricity preserves typing **)

Definition ptype Γ t A :=
  if relm (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧ε
  else if isGhost (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧v
  else ⟦ sc Γ | A ⟧p.

Theorem param_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    ⟦ Γ ⟧v ⊢ᶜ ⟦ sc Γ | t ⟧p : ptype Γ t A.
Proof.
  intros Γ t A h.
  induction h.
Abort.

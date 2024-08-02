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
  clam cType cunit (cSort cProp 0).

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

(** Translation of Pi types, to factorise a bit **)

(* Prop case *)
Definition pmPiP mx Ae Ap Bp :=
  if isProp mx then cPi cProp Ap (close Bp)
  else if isKind mx then pPi cType Ae Ap Bp
  else pPi cProp Ae Ap Bp.

(* Non-prop case *)
Definition pmPiNP mx m Te Ae Ap Bp :=
  let cm := if isKind mx then cType else cProp in
  clam cType Te (
    if isProp mx then cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
    else (
      pPi cm (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (
        if isGhost mx && relm m then cvar 2
        else capp (cvar 2) (cvar 1)
      ))
    )
  ).

(* General case *)
Definition pmPi mx m Te Ae Ap Bp :=
  if isProp m then pmPiP mx Ae Ap Bp
  else pmPiNP mx m Te Ae Ap Bp.

(* Parametricity for if *)

Definition perif be Pe te fe :=
  eif cType be
    (clam cType ebool (cEl (capp (S ⋅ Pe) (cvar 0))))
    te fe (cErr (capp Pe bool_err)).

Definition pmif bP Pe PP te tP fe fP :=
  pif bP
    (plam cProp ebool pbool (
      capp
        (capp (capp (S ⋅ S ⋅ PP) (cvar 1)) (cvar 0))
        (S ⋅ (perif (cvar 0) (S ⋅ Pe) (S ⋅ te) (S ⋅ fe)))
    ))
    tP fP.

(* Proves cbot from pbool bool_err *)
Definition pbool_bool_err_inv h :=
  pif h (clam cType ebool (
    clam cProp (capp pbool (cvar 0)) (
      eif cType (cvar 1) (clam cType ebool (cSort cProp 0)) ctop ctop cbot
    )
  )) cstar cstar.

Definition pmifK be bP Pe PP te tP fe fP :=
  capp (
    eif cType be
    (clam cType ebool (
      cPi cProp (capp pbool (cvar 0)) (
        capps (S ⋅ S ⋅ PP) [
          cvar 1 ;
          cvar 0 ;
          perif (cvar 1) (S ⋅ S ⋅ Pe) (S ⋅ S ⋅ te) (S ⋅ S ⋅ fe)
        ]
      )
    ))
    (clam cProp (capp pbool etrue) (S ⋅ tP))
    (clam cProp (capp pbool efalse) (S ⋅ fP))
    (clam cProp (capp pbool bool_err) (
      cbot_elim cType (
        capps (S ⋅ PP) [
          bool_err ;
          cvar 0 ;
          perif bool_err (S ⋅ Pe) (S ⋅ te) (S ⋅ fe)
        ]
      ) (pbool_bool_err_inv (cvar 0))
    ))
  ) bP.

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
    let Te := ⟦ Γ | Pi i j m mx A B ⟧pτ in
    let Ae := ⟦ Γ | A ⟧pτ in
    let Ap := ⟦ Γ | A ⟧p in
    let Bp := ⟦ mx :: Γ | B ⟧p in
    pmPi mx m Te Ae Ap Bp ;
  ⟦ Γ | lam mx A t ⟧p :=
    if isProp mx then clam cProp ⟦ Γ | A ⟧p (close ⟦ mx :: Γ | t ⟧p)
    else (
      let cm := if isKind mx then cType else cProp in
      plam cm ⟦ Γ | A ⟧pτ ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p
    ) ;
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
  ⟦ Γ | Reveal t p ⟧p :=
    if isKind (md Γ p) then capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧pv) ⟦ Γ | t ⟧p
    else cDummy ;
  ⟦ Γ | toRev t p u ⟧p := ⟦ Γ | u ⟧p ;
  ⟦ Γ | fromRev t p u ⟧p := ⟦ Γ | u ⟧p ;
  ⟦ Γ | gheq A u v ⟧p := squash (teq ⟦ Γ | A ⟧pτ ⟦ Γ | u ⟧pv ⟦ Γ | v ⟧pv) ;
  ⟦ Γ | ghrefl A u ⟧p := sq (trefl ⟦ Γ | A ⟧pτ ⟦ Γ | u ⟧pv) ;
  ⟦ Γ | ghcast A u v e P t ⟧p :=
    let eP := ⟦ Γ | e ⟧p in
    let PP := ⟦ Γ | P ⟧p in
    let uv := ⟦ Γ | u ⟧pv in
    let vv := ⟦ Γ | v ⟧pv in
    let vP := ⟦ Γ | v ⟧p in
    let Ae := ⟦ Γ | A ⟧pτ in
    let AP := ⟦ Γ | A ⟧p in
    let te := ⟦ Γ | t ⟧pε in
    let tv := ⟦ Γ | t ⟧pv in
    let tP := ⟦ Γ | t ⟧p in
    match md Γ t with
    | mKind => cDummy
    | mType => pcastTG Ae AP uv vv vP eP PP te tP
    | mGhost => pcastTG Ae AP uv vv vP eP PP tv tP
    | mProp => pcastP Ae AP uv vv vP eP PP tP
    end ;
  ⟦ Γ | tbool ⟧p := pbool ;
  ⟦ Γ | ttrue ⟧p := ptrue ;
  ⟦ Γ | tfalse ⟧p := pfalse ;
  ⟦ Γ | tif m b P t f ⟧p :=
    let be := ⟦ Γ | b ⟧pε in
    let bP := ⟦ Γ | b ⟧p in
    let Pe := ⟦ Γ | P ⟧pε in
    let PP := ⟦ Γ | P ⟧p in
    let te := ⟦ Γ | t ⟧pε in
    let tv := ⟦ Γ | t ⟧pv in
    let tP := ⟦ Γ | t ⟧p in
    let fe := ⟦ Γ | f ⟧pε in
    let fv := ⟦ Γ | f ⟧pv in
    let fP := ⟦ Γ | f ⟧p in
    match m with
    | mKind => pmifK be bP Pe PP te tP fe fP
    | mType => pmif bP Pe PP te tP fe fP
    | mGhost => pmif bP Pe PP tv tP fv fP
    | mProp => pif bP PP tP fP
    end ;
  ⟦ Γ | tnat ⟧p := pnat ;
  ⟦ Γ | tzero ⟧p := pzero ;
  ⟦ Γ | tsucc n ⟧p := psucc ⟦ Γ | n ⟧p ;
  ⟦ Γ | tnat_elim m n P z s ⟧p :=
    let ne := ⟦ Γ | n ⟧pε in
    let nP := ⟦ Γ | n ⟧p in
    let Pe := ⟦ Γ | P ⟧pε in
    let PP := ⟦ Γ | P ⟧p in
    let ze := ⟦ Γ | z ⟧pε in
    let zv := ⟦ Γ | z ⟧pv in
    let zP := ⟦ Γ | z ⟧p in
    let se := ⟦ Γ | s ⟧pε in
    let sv := ⟦ Γ | s ⟧pv in
    let sP := ⟦ Γ | s ⟧p in
    match m with
    | mKind => cDummy
    | mType => pnat_elim ne nP Pe PP ze zP se sP
    | mGhost => pnat_elim ne nP Pe PP zv zP sv sP
    | mProp => pnat_elimP ne nP Pe PP zP sP
    end ;
  ⟦ Γ | tvec A n ⟧p := pvec ⟦ Γ | A ⟧pε ⟦ Γ | A ⟧p ⟦ Γ | n ⟧pv ⟦ Γ | n ⟧p ;
  ⟦ Γ | tvnil A ⟧p := pvnil ⟦ Γ | A ⟧p ;
  ⟦ Γ | tvcons a n v ⟧p := pvcons ⟦ Γ | a ⟧p  ⟦ Γ | n ⟧p ⟦ Γ | v ⟧p ;
  ⟦ Γ | tvec_elim m A n v P z s ⟧p :=
    let Ae := ⟦ Γ | A ⟧pε in
    let AP := ⟦ Γ | A ⟧p in
    let nv := ⟦ Γ | n ⟧pv in
    let nP := ⟦ Γ | n ⟧p in
    let ve := ⟦ Γ | v ⟧pε in
    let vP := ⟦ Γ | v ⟧p in
    let Pe := ⟦ Γ | P ⟧pε in
    let PP := ⟦ Γ | P ⟧p in
    let ze := ⟦ Γ | z ⟧pε in
    let zv := ⟦ Γ | z ⟧pv in
    let zP := ⟦ Γ | z ⟧p in
    let se := ⟦ Γ | s ⟧pε in
    let sv := ⟦ Γ | s ⟧pv in
    let sP := ⟦ Γ | s ⟧p in
    match m with
    | mKind => cDummy
    | mType =>  pvec_elim Ae AP nv nP ve vP Pe PP ze zP se sP
    | mGhost => pvec_elimG Ae AP nv nP ve vP Pe PP zv zP sv sP
    | mProp => pvec_elimP Ae AP nv nP ve vP Pe PP zP sP
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
  cbn in e. cbn.
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
    - cbn in e.
      destruct (isProp my) eqn:ey. 1: discriminate.
      noconf e. cbn. rewrite ey.
      destruct_if e1. all: reflexivity.
    - cbn in e.
      unfold vreg. simpl "*". remember (S (x * 2)) as z eqn:ez.
      cbn. subst.
      destruct_if ey.
      + eapply ih. assumption.
      + destruct_if e1.
        * eapply ih. assumption.
        * eapply ih. assumption.
  }
  eexists. split.
  - eassumption.
  - rasimpl. unfold vreg. cbn. rasimpl. eapply extRen_cterm.
    intro. ssimpl. unfold shift. lia.
Qed.

(** ⟦ Γ ⟧ε is a sub-context of ⟦ Γ ⟧p **)

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
  - cbn.
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
  - cbn in *. destruct_ifs. all: mode_eqs. all: cbn in *.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
  - cbn in *.
    erewrite scoping_md. 2: eassumption.
    cbn. assumption.
  - cbn in *.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs. all: try intuition discriminate.
    1:{ destruct m. all: intuition discriminate. }
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    reflexivity.
  - cbn in *.
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    all: reflexivity.
  - cbn in *.
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
  - cbn in *.
    destruct m.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope.
  - cbn in *.
    destruct m.
    + contradiction.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
  - cbn in *.
    destruct m.
    + contradiction.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
    + cbn in *. escope. all: reflexivity.
  - cbn in *.
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
  unfold epm_lift. rasimpl.
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

Ltac cEl_ren :=
  change (cEl (?ρ ⋅ ?t)) with (ρ ⋅ (cEl t)).

Lemma param_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧p = (pren ρ) ⋅ ⟦ Δ | t ⟧p.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  - cbn.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e as e'. rewrite e'.
      destruct_if e1.
      * unfold vreg, pren. rasimpl. cbn [ren_cterm]. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_succ_double.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_mul. cbn. lia.
      * unfold pren, vpar. rasimpl. cbn [ren_cterm]. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_double.
        rewrite PeanoNat.Nat.odd_mul. cbn. lia.
    + eapply hcρ in e as e'. rewrite e'. reflexivity.
  - cbn. destruct_ifs. all: reflexivity.
  - cbn. unfold pmPi, pmPiP, pmPiNP, pPi.
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
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
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
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ cEl_ren. rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rasimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. all: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rasimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rasimpl. reflexivity. }
      rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ rasimpl. reflexivity. }
      rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ rasimpl. reflexivity. }
      rasimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. unfold close. rasimpl.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
  - cbn.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    unfold plam.
    erewrite erase_ren. 2,3: eassumption.
    destruct_ifs. all: mode_eqs.
    + cbn. unfold close. rasimpl. f_equal.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + cbn. rewrite pren_epm_lift. rasimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + cbn. rewrite pren_epm_lift. rasimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
  - cbn.
    erewrite md_ren. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_ren. 2,3: eassumption.
    erewrite revive_ren. 2,3: eassumption.
    rewrite <- pren_epm_lift. rewrite <- pren_rpm_lift.
    destruct_ifs. all: reflexivity.
  - cbn.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. erewrite IHt3. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 2: reflexivity.
    cbn. erewrite IHt2. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn. eauto.
  - cbn. eauto.
  - cbn.
    erewrite ?erase_ren, ?revive_ren. 2-7: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn.
    erewrite ?erase_ren, ?revive_ren. 2-5: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn.
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
      2:{ rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      2:{ rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      3:{ rasimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. f_equal.
      rasimpl. reflexivity.
    + unfold pcastTG. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      2:{ rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      1:{ cEl_ren. rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      3:{ rasimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      f_equal. f_equal.
      rasimpl. reflexivity.
    + unfold pcastP. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      3:{ rasimpl. reflexivity. }
      all: f_equal.
      3:{ rasimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ cEl_ren. rewrite <- pren_epm_lift. rasimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. rasimpl. reflexivity. }
      all: f_equal.
      1:{ rasimpl. reflexivity. }
      f_equal.
      rasimpl. reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4. 2-9: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-13: eassumption.
    rewrite <- !pren_epm_lift.
    change (epm_lift ⟦ ?G | ?t ⟧v) with (⟦ G | t⟧pv).
    destruct m. 4: reflexivity.
    + unfold pmifK. unfold perif. cbn. f_equal. f_equal.
      all: f_equal. 1,4: f_equal.
      1,2: f_equal. 1-4: f_equal. 1,2,5-7,10: f_equal.
      2,3,5,6: f_equal. 2,4: f_equal.
      all: rasimpl. all: reflexivity.
    + cbn. unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      rasimpl. reflexivity.
    + cbn. unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      rasimpl. reflexivity.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. f_equal. eauto.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4. 2-9: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-13: eassumption.
    rewrite <- !pren_epm_lift.
    change (epm_lift ⟦ ?G | ?t ⟧v) with (⟦ G | t⟧pv).
    destruct m. all: reflexivity.
  - cbn. erewrite IHt1, IHt2. 2-5: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-5: eassumption.
    rewrite <- !pren_epm_lift.
    reflexivity.
  - cbn. erewrite IHt. 2-3: eassumption.
    reflexivity.
  - cbn. erewrite IHt1, IHt2, IHt3. 2-7: eassumption.
    reflexivity.
  - cbn.
    erewrite IHt1, IHt2, IHt3, IHt4, IHt5, IHt6. 2-13: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-17: eassumption.
    rewrite <- !pren_epm_lift.
    change (epm_lift ⟦ ?G | ?t ⟧v) with (⟦ G | t⟧pv).
    destruct m. all: reflexivity.
  - cbn. reflexivity.
  - cbn. destruct_ifs. all: mode_eqs.
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
  unfold psubst. rewrite div2_SS. cbn.
  destruct nth_error eqn:e. 2: reflexivity.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_succ.
  destruct_ifs. all: mode_eqs.
  - ssimpl. erewrite erase_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    rasimpl. rewrite <- pren_epm_lift.
    rasimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. rasimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    rasimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. rasimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite revive_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    rasimpl. rewrite <- pren_rpm_lift.
    eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. rasimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    rasimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. rasimpl. rewrite pren_id. reflexivity.
  - ssimpl. erewrite param_ren.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    rasimpl. eapply extRen_cterm.
    intro x. unfold shift. change (pren S) with (pren (id >> S)).
    rewrite pren_comp_S. rasimpl. rewrite pren_id. reflexivity.
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
  unfold rpm_lift. rasimpl.
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
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl. reflexivity.
      }
      f_equal. all: f_equal. all: f_equal.
      all: eapply ext_cterm. all: rasimpl. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl. reflexivity.
      }
      f_equal. all: f_equal. all: f_equal.
      all: eapply ext_cterm. all: rasimpl. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: cbn. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl. reflexivity.
      }
      unfold cty_lift. f_equal. all: f_equal.
      all: unfold close. all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl.
        rewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal.
      all: unfold close. all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: rasimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: rasimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl.
        erewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl. all: reflexivity.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: rasimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: rasimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      2:{
        rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
      }
      cbn. f_equal. f_equal. all: f_equal. all: f_equal.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl.
      * rewrite rinstInst'_cterm. reflexivity.
      * rewrite rinstInst'_cterm. reflexivity.
    + f_equal. all: f_equal.
      2:{ rasimpl. reflexivity. }
      1: rewrite psubst_epm_lift.
      2:{ unshelve typeclasses eauto with cc_scope shelvedb. all: reflexivity. }
      all: f_equal.
      2:{
        ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. rasimpl.
        erewrite rinstInst'_cterm. reflexivity.
      }
      cbn. unfold cty_lift. f_equal. f_equal. all: f_equal. all: unfold close.
      all: ssimpl.
      all: eapply ext_cterm. all: intros [].
      all: cbn. 1,3: reflexivity.
      all: ssimpl.
      all: erewrite erase_ren ; eauto using rscoping_S, rscoping_comp_S.
      all: rasimpl. all: reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. all: f_equal. 1: f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite psubst_SS. ssimpl. reflexivity.
    + f_equal. unfold close.
      rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite psubst_SS. rasimpl.
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
    + cbn. f_equal. unfold close. rasimpl.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite psubst_SS. rasimpl.
      erewrite rinstInst'_cterm. reflexivity.
    + cbn. unfold plam. f_equal. f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        rewrite psubst_SS. rasimpl. reflexivity.
    + cbn. unfold plam. f_equal. f_equal.
      * rasimpl. reflexivity.
      * rasimpl. eapply ext_cterm. intros [| []]. all: cbn.
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- destruct_ifs. all: mode_eqs. all: try discriminate.
          all: try reflexivity.
          destruct m. all: discriminate.
        --- rewrite psubst_SS. rasimpl. reflexivity.
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
    + unfold pcastTG. cbn. rasimpl.

        aunfold. minimize.

        rewrite_strat (topdown (hints asimpl)).
        (* Goal 54 is already instantiated!

          So there is no way to solve it after the fact. But where is it coming
          from??

          I can test in the 1st goal to see where it appears by using f_equal
          and the presence check.

        *)
        1:{
          f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
          f_equal. f_equal. f_equal.
          match goal with
          | |- context [ PeanoNat.Nat.ones ] => idtac
          end.
        }

        2-61: try (exact _).
        Search PeanoNat.Nat.ones.
        (** TODO
          How do we solve this issue? If the rhs gets instantiated before
          it is solved we run into a problem. This comes from the fact that
          setoid rewrite considers things a success even though it hasn't yet
          found an instance.

          Another way to solve this particular case is to remove RenSimpl but
          that would break other things.
          Although I expect most times there shouldn't be overlap between
          evars, so why is this happening here?

          Maybe we should only rewrite ren and substs with triggers like for
          terms? That might also save some time?
        **)



      clear. f_equal. all: f_equal. all: f_equal. 1,3: f_equal.
      1,3,4: f_equal. 4,5: f_equal. 4,5: f_equal. 6,7: f_equal.
      7: f_equal. 7: f_equal.
      all: rasimpl. all: reflexivity.
      reflexivity.
    + unfold pcastTG. cbn. rasimpl. reflexivity.
    + unfold pcastP. cbn. rasimpl. reflexivity.
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
      all: rasimpl. all: reflexivity.
    + unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      rasimpl. reflexivity.
    + unfold pmif, plam. cbn. f_equal. f_equal. f_equal.
      rasimpl. reflexivity.
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
      rasimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      rasimpl. eapply ext_cterm_scoped.
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
        -- cbn. rasimpl. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. ssimpl. f_equal. assumption.
          ++ cbn. ssimpl. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:e1. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e2.
        -- mode_eqs. cbn. ssimpl. f_equal. assumption.
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
      rasimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      rasimpl. eapply ext_cterm_scoped.
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
        -- cbn. ssimpl. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. ssimpl. f_equal. assumption.
          ++ cbn. ssimpl. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e2.
        -- mode_eqs. cbn. ssimpl. f_equal. assumption.
        -- unfold relv, ghv. rewrite emx.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + eapply cconv_trans.
      1:{ constructor. 2: apply cconv_refl. constructor. }
      cbn.
      eapply cconv_trans. 1: constructor.
      rasimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      rasimpl. eapply ext_cterm_scoped.
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
        -- cbn. ssimpl. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. ssimpl. f_equal. assumption.
          ++ cbn. ssimpl. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e3.
        -- mode_eqs. cbn. ssimpl. f_equal. assumption.
        -- unfold relv, ghv. rewrite emx.
          destruct_ifs.
          ++ rewrite en. reflexivity.
          ++ rewrite en. reflexivity.
          ++ destruct mx. all: discriminate.
    + eapply cconv_trans. 1: constructor.
      unfold close. rasimpl. apply ccmeta_refl.
      erewrite param_subst.
      2:{ eapply sscoping_one. eassumption. }
      2: eapply sscoping_comp_one.
      rasimpl. eapply ext_cterm_scoped.
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
        -- cbn. ssimpl. f_equal. assumption.
        -- destruct mx. all: try discriminate.
          ++ cbn. ssimpl. f_equal. assumption.
          ++ cbn. ssimpl. f_equal. assumption.
      * set (p := Nat.div2 n) in *.
        rewrite en in hx. rewrite nth_error_param_vreg in hx.
        destruct nth_error as [mx|] eqn:emx. 2: discriminate.
        cbn in hx.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_succ.
        destruct PeanoNat.Nat.odd eqn:eodd.
        2:{ rewrite en in eodd. rewrite odd_vreg in eodd. discriminate. }
        destruct (isProp mx) eqn:e3.
        -- mode_eqs. cbn. ssimpl. f_equal. assumption.
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
      rasimpl. econv.
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
      rasimpl. econv.
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
  - cbn. eapply param_scoping in H0, H1, H2, H3.
    rewrite <- csc_param_ctx in H0, H1, H2, H3.
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
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * cbn. apply crtyping_shift. apply crtyping_S.
      * eapply cstyping_one_none.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * apply crtyping_shift. apply crtyping_S.
      * apply cstyping_one_none.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S.
      cbn. eapply crtyping_shift_eq.
      * apply crtyping_shift. apply crtyping_S.
      * cbn. f_equal. rasimpl. reflexivity.
    + econv. all: try reflexivity.
      all: eauto using crtyping_S, cstyping_one_none.
      * eapply cstyping_nones.
      * cbn. eapply crtyping_shift_eq.
        -- apply crtyping_shift. apply crtyping_S.
        -- cbn. f_equal. rasimpl. reflexivity.
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
        - f_equal. f_equal. f_equal. cbn. rasimpl. reflexivity.
      }
      * {
        eapply crtyping_shift_eq.
        - eapply crtyping_shift. apply crtyping_S.
        - f_equal. f_equal. f_equal. cbn. rasimpl. reflexivity.
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

(** Parametricity preserves typing **)

Definition ptype Γ t A :=
  if relm (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧pε
  else if isGhost (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧pv
  else ⟦ sc Γ | A ⟧p.

Lemma param_ctx_vreg :
  ∀ Γ x A,
    nth_error Γ x = Some (mProp, A) →
    nth_error ⟦ Γ ⟧p (vreg x) = Some (Some (cProp, ⟦ skipn (S x) (sc Γ) | A ⟧p)).
Proof.
  intros Γ x A e.
  induction Γ as [| [my B] Γ ih ] in x, A, e |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn. reflexivity.
  - cbn in e. change (vreg (S x)) with (S (S (vreg x))).
    remember (vreg x) as p eqn:ep.
    cbn - [skipn].
    destruct_ifs. all: mode_eqs. all: subst.
    + erewrite ih. 2: eauto. reflexivity.
    + erewrite ih. 2: eauto. reflexivity.
    + erewrite ih. 2: eauto. reflexivity.
Qed.

Lemma param_ctx_vpar :
  ∀ Γ x m A,
    nth_error Γ x = Some (m, A) →
    isProp m = false →
    nth_error ⟦ Γ ⟧p (vpar x) =
    Some (Some (if isKind m then cType else cProp, capp (S ⋅ ⟦ skipn (S x) (sc Γ) | A ⟧p) (cvar 0))).
Proof.
  intros Γ x m A e hm.
  induction Γ as [| [my B] Γ ih ] in x, m, A, e, hm |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn. rewrite hm.
    destruct_ifs. all: reflexivity.
  - cbn in e. change (vpar (S x)) with (S (S (vpar x))).
    remember (vpar x) as p eqn:ep.
    cbn - [skipn].
    destruct_if e1. 2: destruct_if e2. all: mode_eqs. all: subst.
    + erewrite ih. 2,3: eauto. reflexivity.
    + erewrite ih. 2,3: eauto. reflexivity.
    + erewrite ih. 2,3: eauto. reflexivity.
Qed.

Lemma pren_plus :
  ∀ n m, pren (plus m) n = n + 2 * m.
Proof.
  intros n m.
  unfold pren.
  pose proof (pren_id n) as e. unfold pren in e.
  unfold id in e. unfold Datatypes.id in e. lia.
Qed.

Lemma epm_lift_eq :
  ∀ t, epm_lift t = vreg ⋅ t.
Proof.
  intro. reflexivity.
Qed.

Lemma rpm_lift_eq :
  ∀ t, rpm_lift t = vreg ⋅ t.
Proof.
  intro. reflexivity.
Qed.

Hint Resolve csc_param_ctx : cc_scope.

Lemma type_epm_lift :
  ∀ Γ t A,
    ⟦ Γ ⟧ε ⊢ᶜ t : A →
    ⟦ Γ ⟧p ⊢ᶜ epm_lift t : epm_lift A.
Proof.
  intros Γ t A h.
  rewrite epm_lift_eq. eapply ctyping_ren.
  - eapply typing_er_sub_param.
  - eassumption.
Qed.

(* Hint Resolve type_epm_lift : cc_type. *)

Lemma type_epm_lift_eq :
  ∀ Γ Γ' t A,
    ⟦ Γ ⟧ε ⊢ᶜ t : A →
    Γ' = ⟦ Γ ⟧p →
    Γ' ⊢ᶜ epm_lift t : epm_lift A.
Proof.
  intros Γ Γ' t A h ->.
  apply type_epm_lift. assumption.
Qed.

Lemma type_rpm_lift :
  ∀ Γ t A,
    ⟦ Γ ⟧v ⊢ᶜ t : A →
    ⟦ Γ ⟧p ⊢ᶜ rpm_lift t : epm_lift A.
Proof.
  intros Γ t A h.
  rewrite rpm_lift_eq. eapply ctyping_ren.
  - eapply typing_rev_sub_param.
  - eassumption.
Qed.

(* Hint Resolve type_rpm_lift : cc_type. *)

Lemma type_rpm_lift_eq :
  ∀ Γ Γ' t A,
    ⟦ Γ ⟧v ⊢ᶜ t : A →
    Γ' = ⟦ Γ ⟧p →
    Γ' ⊢ᶜ rpm_lift t : epm_lift A.
Proof.
  intros Γ Γ' t A h ->.
  apply type_rpm_lift. assumption.
Qed.

(* Hint Resolve erase_typing revive_typing : cc_type. *)

Hint Extern 5 =>
  eapply erase_typing ; [
    eassumption
  | idtac
  ] : cc_type.

Hint Extern 5 =>
  eapply revive_typing ; [
    eassumption
  | idtac
  ] : cc_type.

Lemma erase_typing_eq :
  ∀ Γ Γ' Γ'' t A,
    Γ ⊢ t : A →
    relm (mdc Γ t) = true →
    Γ' = ⟦ Γ ⟧ε →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | t ⟧ε : ⟦ Γ'' | A ⟧τ.
Proof.
  intros Γ ? ? t A ? ? -> ->.
  apply erase_typing. all: assumption.
Qed.

Lemma revive_typing_eq :
  ∀ Γ Γ' Γ'' t A,
    Γ ⊢ t : A →
    mdc Γ t = mGhost →
    Γ' = ⟦ Γ ⟧v →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | t ⟧v : ⟦ Γ'' | A ⟧τ.
Proof.
  intros Γ ? ? t A ? ? -> ->.
  apply revive_typing. all: assumption.
Qed.

Hint Extern 10 =>
  eapply erase_typing_eq ; [
    eassumption
  | idtac
  | reflexivity
  | reflexivity
  ] : cc_type.

Hint Extern 10 =>
  eapply revive_typing_eq ; [
    eassumption
  | idtac
  | reflexivity
  | reflexivity
  ] : cc_type.

Lemma cstyping_shift_eq :
  ∀ Γ Γ' Δ mx A σ,
    cstyping Γ σ Δ →
    Γ' = Some (mx, A <[ σ ]) :: Γ →
    cstyping Γ' (cvar 0 .: σ >> ren1 S) (Some (mx, A) :: Δ).
Proof.
  intros Γ Γ' Δ mx A σ h ->.
  apply cstyping_shift. assumption.
Qed.

Hint Extern 11 (relm _ = _) =>
  remd ; reflexivity : cc_type.

Hint Extern 10 (relm _ = _) =>
  reflexivity : cc_type.

Hint Extern 11 (md _ _ = _) =>
  remd ; reflexivity : cc_type.

Hint Extern 10 (md _ _ = _) =>
  reflexivity : cc_type.

Hint Extern 11 (isProp _ = _) =>
  remd ; reflexivity : cc_type.

Hint Extern 10 (isProp _ = _) =>
  reflexivity : cc_type.

Hint Extern 100 (nth_error _ _ = _) =>
  reflexivity : cc_type.

Lemma param_erase_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    relm (mdc Γ t) = true →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | t ⟧pε : ⟦ sc Γ | A ⟧pτ.
Proof.
  intros Γ t A h e.
  eapply type_epm_lift. etype.
Qed.

Hint Resolve param_erase_typing : cc_type.

Lemma param_revive_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    mdc Γ t = mGhost →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | t ⟧pv : ⟦ sc Γ | A ⟧pτ.
Proof.
  intros Γ t A h e.
  eapply type_rpm_lift. etype.
Qed.

(* Hint Resolve param_revive_typing : cc_type. *)

Hint Extern 6 =>
  eapply param_revive_typing ; [
    eassumption
  | idtac
  ] : cc_type.

Lemma param_erase_ty_tm :
  ∀ Γ A,
    ⟦ Γ | A ⟧pτ = cEl ⟦ Γ | A ⟧pε.
Proof.
  intros Γ A.
  reflexivity.
Qed.

Lemma param_erase_ty :
  ∀ Γ Γ' Γ'' A m i,
    Γ ⊢ A : Sort m i →
    isProp m = false →
    relm (mdc Γ A) = true →
    Γ' = sc Γ →
    Γ'' = ⟦ Γ ⟧p →
    Γ'' ⊢ᶜ ⟦ Γ' | A ⟧pτ : cSort cType i.
Proof.
  intros Γ Γ' Γ'' A m i h hpm hrm -> ->.
  eapply ccmeta_conv.
  - eapply type_epm_lift. etype.
    econstructor.
    + etype.
    + cbn. rewrite hpm. constructor.
    + etype.
  - reflexivity.
Qed.

(* Hint Resolve param_erase_ty : cc_type. *)

Hint Extern 15 =>
  eapply param_erase_ty ; [
    eassumption (* To avoid using the lemma when not applicable *)
  | idtac
  | idtac
  | reflexivity
  | reflexivity
  ] : cc_type.

Lemma param_erase_err :
  ∀ Γ Γ' Γ'' A m i,
    Γ ⊢ A : Sort m i →
    isProp m = false →
    relm (mdc Γ A) = true →
    Γ' = sc Γ →
    Γ'' = ⟦ Γ ⟧p →
    Γ'' ⊢ᶜ ⟦ Γ' | A ⟧p∅ : ⟦ Γ' | A ⟧pτ.
Proof.
  intros Γ Γ' Γ'' A m i h hpm hrm -> ->.
  eapply ccmeta_conv.
  - eapply type_epm_lift. etype.
    econstructor.
    + etype.
    + cbn. rewrite hpm. constructor.
    + etype.
  - reflexivity.
Qed.

(* Hint Resolve param_erase_ty : cc_type. *)

Hint Extern 15 =>
  eapply param_erase_err ; [
    eassumption
  | idtac
  | idtac
  | reflexivity
  | reflexivity
  ] : cc_type.

Lemma param_pProp :
  ∀ Γ A Ae,
    Γ ⊢ᶜ A : capp pProp Ae →
    Γ ⊢ᶜ A : cSort cProp 0.
Proof.
  intros Γ A Ae h.
  econstructor.
  - eassumption.
  - unfold pProp. eapply cconv_trans. 1: constructor.
    cbn. econv.
  - etype.
Qed.

Lemma param_pType :
  ∀ Γ A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mType i →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : capp (pType i) ⟦ sc Γ | A ⟧pε →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : ⟦ sc Γ | A ⟧pτ ⇒[ cType ] cSort cProp 0.
Proof.
  intros Γ A i hmA hA h.
  econstructor.
  - eassumption.
  - unfold pType. eapply cconv_trans. 1: constructor.
    cbn. econv. rewrite param_erase_ty_tm. econv.
  - etype.
Qed.

Lemma param_pType_eq :
  ∀ Γ Γ' Γ'' A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mType i →
    Γ' = ⟦ Γ ⟧p →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | A ⟧p : capp (pType i) ⟦ Γ'' | A ⟧pε →
    Γ' ⊢ᶜ ⟦ Γ'' | A ⟧p : ⟦ Γ'' | A ⟧pτ ⇒[ cType ] cSort cProp 0.
Proof.
  intros Γ ?? A i hmA hA -> -> h.
  eapply param_pType. all: eassumption.
Qed.

Lemma param_pGhost :
  ∀ Γ A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mGhost i →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : capp (pType i) ⟦ sc Γ | A ⟧pε →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : ⟦ sc Γ | A ⟧pτ ⇒[ cType ] cSort cProp 0.
Proof.
  intros Γ A i hmA hA h.
  econstructor.
  - eassumption.
  - unfold pType. eapply cconv_trans. 1: constructor.
    cbn. econv. rewrite param_erase_ty_tm. econv.
  - etype.
Qed.

Lemma param_pGhost_eq :
  ∀ Γ Γ' Γ'' A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mGhost i →
    Γ' = ⟦ Γ ⟧p →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | A ⟧p : capp (pType i) ⟦ Γ'' | A ⟧pε →
    Γ' ⊢ᶜ ⟦ Γ'' | A ⟧p : ⟦ Γ'' | A ⟧pτ ⇒[ cType ] cSort cProp 0.
Proof.
  intros Γ ?? A i hmA hA -> -> h.
  eapply param_pGhost. all: eassumption.
Qed.

Lemma param_pKind :
  ∀ Γ A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mKind i →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : capp (pKind i) ⟦ sc Γ | A ⟧pε →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : ⟦ sc Γ | A ⟧pτ ⇒[ cType ] cSort cType i.
Proof.
  intros Γ A i hmA hA h.
  econstructor.
  - eassumption.
  - unfold pKind. eapply cconv_trans. 1: constructor.
    cbn. econv. rewrite param_erase_ty_tm. econv.
  - etype.
Qed.

Lemma param_pKind_eq :
  ∀ Γ Γ' Γ'' A i,
    cscoping Γ A mKind →
    Γ ⊢ A : Sort mKind i →
    Γ' = ⟦ Γ ⟧p →
    Γ'' = sc Γ →
    Γ' ⊢ᶜ ⟦ Γ'' | A ⟧p : capp (pKind i) ⟦ Γ'' | A ⟧pε →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : ⟦ sc Γ | A ⟧pτ ⇒[ cType ] cSort cType i.
Proof.
  intros Γ ? ? A i hmA hA -> -> h.
  apply param_pKind. all: assumption.
Qed.

Lemma type_pcastTG :
  ∀ Γ i Ae AP uv uP vv vP eP Pe PP te tP,
    Γ ⊢ᶜ Ae : cSort cType i →
    Γ ⊢ᶜ AP : cPi cType Ae (cSort cProp 0) →
    Γ ⊢ᶜ uv : Ae →
    Γ ⊢ᶜ uP : capp AP uv →
    Γ ⊢ᶜ vv : Ae →
    Γ ⊢ᶜ vP : capp AP vv →
    Γ ⊢ᶜ eP : squash (teq Ae uv vv) →
    Γ ⊢ᶜ Pe : cty i →
    Γ ⊢ᶜ PP :
      cPi cType Ae
        (cPi cProp (capp (S ⋅ AP) (cvar 0))
          (cPi cType (cEl ((S >> S) ⋅ Pe))
            (cSort cProp 0))) →
    Γ ⊢ᶜ te : cEl Pe →
    Γ ⊢ᶜ tP : capp (capp (capp PP uv) uP) te →
    ccxscoping Γ uP cProp →
    Γ ⊢ᶜ pcastTG Ae AP uv vv vP eP PP te tP : capp (capp (capp PP vv) vP) te.
Proof.
  intros Γ i Ae AP uv uP vv vP eP Pe PP te tP. intros.
  unfold pcastTG. cbn. rasimpl.
  change (λ n, S (S (S n))) with (S >> S >> S). rasimpl.
  econstructor.
  - ertype.
    + eapply ccmeta_conv.
      * {
        ertype.
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. rasimpl. reflexivity.
          + cbn. rasimpl. rewrite !rinstInst'_cterm. reflexivity.
        - cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
      }
      * cbn. reflexivity.
    + econstructor.
      * {
        ertype. econstructor.
        - ertype.
          + eapply ccmeta_conv. 1: ertype.
            cbn. rasimpl. reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                cbn. rasimpl. reflexivity.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. f_equal. rasimpl. reflexivity.
                + cbn. reflexivity.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv. 1: ertype.
                      cbn. lhs_ssimpl. f_equal. rasimpl. reflexivity.
                    - cbn. lhs_ssimpl. f_equal. rasimpl.
                      rewrite rinstInst'_cterm. reflexivity.
                  }
                  * cbn. rasimpl. reflexivity.
                + cbn. reflexivity.
            }
            * cbn. f_equal. rasimpl. reflexivity.
          + econstructor.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - cbn. reflexivity.
            }
            * cbn. eapply cconv_sym. eapply cconv_trans.
              1:{
                econstructor. 2: econv.
                constructor.
              }
              cbn. rasimpl. eapply cconv_trans. 1: constructor.
              cbn. rasimpl. rewrite !rinstInst'_cterm. rasimpl. econv.
              apply cconv_irr.
              -- escope. reflexivity.
              -- eapply cscoping_ren.
                1:{ eapply crscoping_comp. all: apply crscoping_S. }
                assumption.
            * {
              eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    ertype.
                    - eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - eapply ccmeta_conv. 1: ertype.
                      cbn. rasimpl. reflexivity.
                    - eapply ccmeta_conv.
                      + ertype. eapply ccmeta_conv. 1: ertype.
                        cbn. f_equal. rasimpl. reflexivity.
                      + cbn. reflexivity.
                    - eapply ccmeta_conv.
                      + ertype. eapply ccmeta_conv.
                        * {
                          ertype. eapply ccmeta_conv.
                          - ertype. eapply ccmeta_conv. 1: ertype.
                            cbn. lhs_ssimpl. f_equal. rasimpl. reflexivity.
                          - cbn. lhs_ssimpl. f_equal. rasimpl.
                            rewrite rinstInst'_cterm. reflexivity.
                        }
                        * cbn. rasimpl. reflexivity.
                      + cbn. reflexivity.
                  }
                  * cbn. rasimpl. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
              - cbn. reflexivity.
            }
        - eapply cconv_trans.
          1:{
            constructor. 2: econv.
            constructor.
          }
          cbn. lhs_ssimpl. eapply cconv_trans. 1: constructor.
          cbn. lhs_ssimpl. rewrite <- !funcomp_assoc.
          rewrite <- !rinstInst'_cterm. econv.
        - ertype.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. rasimpl. reflexivity.
                + cbn. rasimpl. reflexivity.
              - cbn. lhs_ssimpl. rewrite <- funcomp_assoc.
                rewrite <- !rinstInst'_cterm. reflexivity.
            }
            * cbn. reflexivity.
      }
      * cbn. rasimpl. apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        cbn. rasimpl. eapply ccmeta_conv.
        - ertype.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                cbn. rasimpl. reflexivity.
              - cbn. rasimpl. reflexivity.
            }
            * cbn. rasimpl. reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
        - cbn. reflexivity.
      }
  - eapply cconv_trans. 1: constructor.
    cbn. rasimpl. econv.
  - eapply ccmeta_conv.
    + ertype. eapply ccmeta_conv.
      * ertype. eapply ccmeta_conv. 1: ertype.
        cbn. rasimpl. reflexivity.
      * cbn. rasimpl. reflexivity.
    + cbn. reflexivity.
Qed.

Lemma type_pPi :
  ∀ Γ i j k mm mp A B C,
    Γ ⊢ᶜ A : cSort cType i →
    Γ ⊢ᶜ B : A ⇒[ cType ] cSort mp j →
    Some (mp, capp (S ⋅ B) (cvar 0)) :: Some (cType, A) :: Γ ⊢ᶜ C : cSort mm k →
    Γ ⊢ᶜ pPi mp A B C : cSort mm (cumax cType mm i (cumax mp mm j k)).
Proof.
  intros Γ i j k mm mp A B C hA hB hC.
  unfold pPi.
  eapply ccmeta_conv.
  - ertype.
    eapply ccmeta_conv.
    + ertype. eapply ccmeta_conv. 1: ertype.
      cbn. reflexivity.
    + cbn. reflexivity.
  - reflexivity.
Qed.

Hint Resolve type_pPi : cc_type.
Hint Opaque pPi : cc_type.

Lemma type_plam :
  ∀ Γ i j mp A B C t,
    Γ ⊢ᶜ A : cSort cType i →
    Γ ⊢ᶜ B : A ⇒[ cType ] cSort mp j →
    Some (mp, capp (S ⋅ B) (cvar 0)) :: Some (cType, A) :: Γ ⊢ᶜ t : C →
    Γ ⊢ᶜ plam mp A B t : pPi mp A B C.
Proof.
  intros Γ i j mp A B C t hA hB ht.
  unfold plam, pPi.
  ertype.
  eapply ccmeta_conv.
  - ertype. eapply ccmeta_conv. 1: ertype.
    cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Hint Resolve type_plam : cc_type.
Hint Opaque plam : cc_type.

Hint Opaque cty_lift : cc_type.

Lemma type_pmPiP :
  ∀ Γ i mx Ae Ae' Ap Bp,
    (isProp mx = false → Γ ⊢ᶜ Ae : cty i) →
    Γ ⊢ᶜ Ap : capp (if isKind mx then pKind i else if isProp mx then pProp else pType i) Ae →
    let Γ' :=
      if isProp mx then
        None :: Some (cProp, Ap) :: Γ
      else if isKind mx then
        Some (cType, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γ
      else
        Some (cProp, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γ
    in
    Γ' ⊢ᶜ Bp : cSort cProp 0 →
    Ae' = cEl Ae →
    Γ ⊢ᶜ pmPiP mx Ae' Ap Bp : cSort cProp 0.
Proof.
  intros Γ i mx Ae Ae' Ap Bp hAe hAp Γ' hBp ->. subst Γ'.
  unfold pmPiP. destruct_ifs. all: mode_eqs. all: cbn in *.
  - eapply param_pProp in hAp.
    eapply ccmeta_conv.
    + ertype. eapply ccmeta_conv. 1: ertype.
      cbn. reflexivity.
    + cbn. reflexivity.
  - eapply ctype_conv in hAp.
    2:{
      unfold pKind. eapply cconv_trans. 1: constructor.
      cbn. econv.
    }
    2: ertype.
    eapply ccmeta_conv.
    + ertype.
    + cbn. reflexivity.
  - forward hAe by auto.
    eapply ccmeta_conv.
    + ertype. econstructor.
      * ertype.
      * unfold pType. eapply cconv_trans. 1: constructor.
        cbn. econv.
      * ertype.
    + cbn. reflexivity.
Qed.

Lemma type_perif :
  ∀ Γ i be Pe te fe,
    Γ ⊢ᶜ be : ebool →
    Γ ⊢ᶜ Pe : ebool ⇒[ cType ] cty i →
    Γ ⊢ᶜ te : cEl (capp Pe etrue) →
    Γ ⊢ᶜ fe : cEl (capp Pe efalse) →
    Γ ⊢ᶜ perif be Pe te fe : cEl (capp Pe be).
Proof.
  intros Γ i be Pe te fe hbe hPe hte hfe.
  cbn in hPe.
  unfold perif. econstructor.
  - etype.
    + eapply ccmeta_conv.
      * ertype. eapply ccmeta_conv. 1: ertype.
        cbn. reflexivity.
      * cbn. reflexivity.
    + econstructor.
      * etype.
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
    + econstructor.
      * etype.
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
    + econstructor.
      * {
        etype. eapply ccmeta_conv.
        - ertype.
        - cbn. reflexivity.
      }
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
  - eapply cconv_trans. 1: constructor.
    cbn. rasimpl. econv.
  - ertype. eapply ccmeta_conv.
    + ertype.
    + cbn. reflexivity.
Qed.

Hint Opaque perif : cc_type.
Hint Resolve type_perif : cc_type.

Lemma type_pmif :
  ∀ Γ i be bP Pe PP te tP fe fP,
    Γ ⊢ᶜ be : ebool →
    Γ ⊢ᶜ bP : capp pbool be →
    Γ ⊢ᶜ Pe : ebool ⇒[ cType ] cty i →
    Γ ⊢ᶜ PP : pPi cProp ebool pbool (
      cPi cType (cEl (capp (S ⋅ S ⋅ Pe) (cvar 1))) (cSort cProp 0)
    ) →
    Γ ⊢ᶜ te : cEl (capp Pe etrue) →
    Γ ⊢ᶜ tP : capp (capp (capp PP etrue) ptrue) te →
    Γ ⊢ᶜ fe : cEl (capp Pe efalse) →
    Γ ⊢ᶜ fP : capp (capp (capp PP efalse) pfalse) fe →
    Γ ⊢ᶜ pmif bP Pe PP te tP fe fP :
    capp (capp (capp PP be) bP) (perif be Pe te fe).
Proof.
  intros Γ i be bP Pe PP te tP fe fP hbe hbP hPe hPP hte htP hfe hfP.
  unfold pmif.
  econstructor.
  - ertype.
    + eapply ccmeta_conv.
      * {
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype.
              - cbn. reflexivity.
            }
            * cbn. rasimpl. reflexivity.
          + cbn. rasimpl. reflexivity.
        - eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
      }
      * cbn. reflexivity.
    + econstructor.
      * ertype.
      * apply cconv_sym. unfold plam. eapply cconv_trans.
        1:{ constructor. 2: econv. constructor. }
        cbn. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype.
                    - cbn. rasimpl. reflexivity.
                  }
                  * cbn. rasimpl. reflexivity.
                + cbn. rasimpl. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
            }
            * cbn. unfold pPi. reflexivity.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
    + econstructor.
      * ertype.
      * apply cconv_sym. unfold plam. eapply cconv_trans.
        1:{ constructor. 2: econv. constructor. }
        cbn. eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype.
                    - cbn. rasimpl. reflexivity.
                  }
                  * cbn. rasimpl. reflexivity.
                + cbn. rasimpl. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
            }
            * cbn. unfold pPi. reflexivity.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
  - unfold plam. eapply cconv_trans.
    1:{ constructor. 2: econv. constructor. }
    cbn. eapply cconv_trans. 1: constructor.
    cbn. rasimpl. econv. unfold perif. econv.
  - eapply ccmeta_conv.
    + ertype. eapply ccmeta_conv.
      * {
        ertype. eapply ccmeta_conv.
        - ertype.
        - cbn. rasimpl. reflexivity.
      }
      * cbn. rasimpl. reflexivity.
    + cbn. reflexivity.
Qed.

Hint Opaque pmif : cc_type.
Hint Resolve type_pmif : cc_type.

Lemma type_pmifK :
  ∀ Γ i be bP Pe PP te tP fe fP,
    Γ ⊢ᶜ be : ebool →
    Γ ⊢ᶜ bP : capp pbool be →
    Γ ⊢ᶜ Pe : ebool ⇒[ cType ] cty i →
    Γ ⊢ᶜ PP : pPi cProp ebool pbool (
      cPi cType (cEl (capp (S ⋅ S ⋅ Pe) (cvar 1))) (cSort cType i)
    ) →
    Γ ⊢ᶜ te : cEl (capp Pe etrue) →
    Γ ⊢ᶜ tP : capp (capp (capp PP etrue) ptrue) te →
    Γ ⊢ᶜ fe : cEl (capp Pe efalse) →
    Γ ⊢ᶜ fP : capp (capp (capp PP efalse) pfalse) fe →
    Γ ⊢ᶜ pmifK be bP Pe PP te tP fe fP :
    capp (capp (capp PP be) bP) (perif be Pe te fe).
Proof.
  intros Γ i be bP Pe PP te tP fe fP hbe hbP hPe hPP hte htP hfe hfP.
  unfold pmifK.
  eapply ccmeta_conv.
  - ertype.
    econstructor.
    + ertype.
      * {
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv. 1: ertype.
          reflexivity.
        - cbn. reflexivity.
      }
      * {
        eapply ccmeta_conv.
        - ertype.
          + eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - cbn. reflexivity.
            }
            * cbn. f_equal. rasimpl. reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
        - cbn. reflexivity.
      }
      * {
        econstructor.
        - ertype. eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. econv.
          + rasimpl. econv.
          + apply cconv_irr. all: escope.
            reflexivity.
          + eapply cconv_trans. 1: constructor.
            rasimpl. econv.
        - eapply ccmeta_conv.
          + ertype.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - cbn. reflexivity.
            }
            * {
              cbn. eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - cbn. reflexivity.
                  }
                  * cbn. f_equal. rasimpl. rewrite rinstInst'_cterm.
                    reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - cbn. reflexivity.
            }
          + cbn. reflexivity.
      }
      * {
        econstructor.
        - ertype. eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. econv.
          + rasimpl. econv.
          + apply cconv_irr. all: escope.
            reflexivity.
          + eapply cconv_trans. 1: constructor.
            rasimpl. econv.
        - eapply ccmeta_conv.
          + ertype.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - cbn. reflexivity.
            }
            * {
              cbn. eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - cbn. reflexivity.
                  }
                  * cbn. f_equal. rasimpl. rewrite rinstInst'_cterm.
                    reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - cbn. reflexivity.
            }
          + cbn. reflexivity.
      }
      * {
        econstructor.
        - ertype.
          + eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + cbn. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * ertype. eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  * cbn. reflexivity.
                + cbn. f_equal. rasimpl. rewrite rinstInst'_cterm. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
            }
            * cbn. reflexivity.
          + unfold pbool_bool_err_inv.
            econstructor.
            * {
              ertype.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + cbn. reflexivity.
              - econstructor.
                + {
                  ertype.
                  - eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                  - econstructor.
                    + ertype.
                    + apply cconv_sym. eapply cconv_trans. 1: constructor.
                      cbn. econv.
                    + eapply ccmeta_conv.
                      * ertype.
                      * reflexivity.
                  - econstructor.
                    + ertype.
                    + apply cconv_sym. eapply cconv_trans. 1: constructor.
                      cbn. econv.
                    + eapply ccmeta_conv.
                      * ertype.
                      * reflexivity.
                  - econstructor.
                    + ertype.
                    + apply cconv_sym. eapply cconv_trans. 1: constructor.
                      cbn. econv.
                    + eapply ccmeta_conv.
                      * ertype.
                      * reflexivity.
                }
                + cbn. constructor.
                + cbn. ertype.
              - econstructor.
                + ertype.
                + apply cconv_sym. eapply cconv_trans.
                  1:{
                    econstructor. 2: econv.
                    constructor.
                  }
                  cbn. eapply cconv_trans. 1: constructor.
                  cbn. constructor.
                + econstructor.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype.
                      + eapply ccmeta_conv.
                        * ertype. eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                        * cbn. reflexivity.
                      + eapply ccmeta_conv. 1: ertype.
                        reflexivity.
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * {
                          eapply ccmeta_conv.
                          - ertype.
                          - reflexivity.
                        }
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                    - cbn. reflexivity.
                  }
                  * cbn. eapply cconv_trans. 1: constructor.
                    cbn. econv.
                  * ertype.
              - econstructor.
                + ertype.
                + apply cconv_sym. eapply cconv_trans.
                  1:{
                    econstructor. 2: econv.
                    constructor.
                  }
                  cbn. eapply cconv_trans. 1: constructor.
                  cbn. constructor.
                + econstructor.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype.
                      + eapply ccmeta_conv.
                        * ertype. eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                        * cbn. reflexivity.
                      + eapply ccmeta_conv. 1: ertype.
                        reflexivity.
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * {
                          eapply ccmeta_conv.
                          - ertype.
                          - reflexivity.
                        }
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                      + econstructor.
                        * ertype.
                        * apply cconv_sym. constructor.
                        * eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                    - cbn. reflexivity.
                  }
                  * cbn. eapply cconv_trans. 1: constructor.
                    cbn. econv.
                  * ertype.
            }
            * {
              eapply cconv_trans.
              1:{
                econstructor. 2: econv.
                constructor.
              }
              cbn. eapply cconv_trans. 1: constructor.
              cbn. constructor.
            }
            * ertype.
        - apply cconv_sym. eapply cconv_trans. 1: constructor.
          cbn. econv.
          + rasimpl. rewrite rinstInst'_cterm. econv.
          + unfold perif. eapply cconv_trans. 1: constructor.
            apply cconv_sym. eapply cconv_trans. 1: constructor.
            econv. rasimpl. rewrite rinstInst'_cterm. econv.
        - eapply ccmeta_conv.
          + ertype.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - cbn. reflexivity.
            }
            * {
              cbn. eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    ertype. eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - cbn. reflexivity.
                  }
                  * cbn. f_equal. f_equal. rasimpl.
                    rewrite rinstInst'_cterm. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - cbn. reflexivity.
            }
          + cbn. reflexivity.
      }
    + eapply cconv_trans. 1: constructor.
      cbn. rasimpl. econv.
    + ertype.
      * eapply ccmeta_conv. 1: ertype.
        reflexivity.
      * {
        eapply ccmeta_conv.
        - ertype.
          + econstructor.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - cbn. reflexivity.
            }
            * cbn. rasimpl. econstructor. 2: econv.
              apply cconv_sym. eapply cconv_trans. 1: econstructor.
              cbn. rasimpl. rewrite rinstInst'_cterm. econv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * ertype. eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  * cbn. reflexivity.
                + eapply ccmeta_conv.
                  * ertype.
                  * reflexivity.
              - cbn. reflexivity.
            }
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + eapply ccmeta_conv.
            * ertype. eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * cbn. reflexivity.
          + econstructor.
            * ertype.
            * apply cconv_sym. eapply cconv_trans. 1: constructor.
              cbn. rasimpl. rewrite rinstInst'_cterm. econv.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                + reflexivity.
              - reflexivity.
            }
          + econstructor.
            * ertype.
            * apply cconv_sym. eapply cconv_trans. 1: constructor.
              cbn. rasimpl. rewrite rinstInst'_cterm. econv.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                + reflexivity.
              - reflexivity.
            }
          + econstructor.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - cbn. reflexivity.
            }
            * apply cconv_sym. eapply cconv_trans. 1: constructor.
              cbn. rasimpl. rewrite rinstInst'_cterm. econv.
            * {
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                + reflexivity.
              - reflexivity.
            }
        - cbn. reflexivity.
      }
  - cbn. rasimpl. unfold perif. reflexivity.
Qed.

Hint Opaque pmifK : cc_type.
Hint Resolve type_pmifK : cc_type.

Lemma type_pKind :
  ∀ Γ i,
    Γ ⊢ᶜ pKind i : cPi cType (cty i) (cSort cType (S i)).
Proof.
  intros Γ i.
  unfold pKind. ertype.
  cbn. eapply ccmeta_conv.
  - ertype. eapply ccmeta_conv. 1: ertype.
    cbn. reflexivity.
  - cbn. f_equal. lia.
Qed.

Hint Opaque pKind : cc_type.
Hint Resolve type_pKind : cc_type.

(* Note, the S is not necessary, but it aligns better *)
Lemma type_pType :
  ∀ Γ i,
    Γ ⊢ᶜ pType i : cPi cType (cty i) (cSort cType (S i)).
Proof.
  intros Γ i.
  unfold pType. ertype.
  cbn. eapply ccmeta_conv.
  - econstructor. 2: eapply ctype_cumul with (j := S i). 1,2: ertype.
    + ertype. eapply ccmeta_conv. 1: ertype.
      cbn. reflexivity.
    + cbn. lia.
  - cbn. f_equal. lia.
Qed.

Hint Opaque pType : cc_type.
Hint Resolve type_pType : cc_type.

Lemma type_pProp :
  ∀ Γ,
    Γ ⊢ᶜ pProp : cPi cType cunit (cSort cType 0).
Proof.
  intros Γ.
  unfold pProp. ertype.
Qed.

Hint Opaque pProp : cc_type.
Hint Resolve type_pProp : cc_type.

Lemma type_pmPiNP :
  ∀ Γ i j m mx A B,
    isProp m = false →
    cscoping Γ A mKind →
    cscoping (Γ,, (mx, A)) B mKind →
    Γ ⊢ A : Sort mx i →
    Γ ,, (mx, A) ⊢ B : Sort m j →
    let Γp := ⟦ Γ ⟧p in
    let Te := ⟦ sc Γ | Pi i j m mx A B ⟧pε in
    let Ae := ⟦ sc Γ | A ⟧pε in
    let Ap := ⟦ sc Γ | A ⟧p in
    let Be := ⟦ mx :: sc Γ | B ⟧pε in
    let Bp := ⟦ mx :: sc Γ | B ⟧p in
    Γp ⊢ᶜ Ap : capp (if isKind mx then pKind i else if isProp mx then pProp else pType i) Ae →
    let Γp' :=
      if isProp mx then
        None :: Some (cProp, Ap) :: Γp
      else if isKind mx then
        Some (cType, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γp
      else
        Some (cProp, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γp
    in
    Γp' ⊢ᶜ Bp : capp ((if isKind m then pKind else pType) j) Be →
    Γp ⊢ᶜ pmPiNP mx m (cEl Te) (cEl Ae) Ap Bp :
    capp ((if isKind m then pKind else pType) (umax mx m i j)) Te.
Proof.
  intros Γ i j m mx A B hm hcA hcB hA hB Γp Te Ae Ap Be Bp hAp Γ'p hBp.
  unfold pmPiNP.
  assert (hTe : Γp ⊢ᶜ Te : cty (umax mx m i j)).
  {
    subst Te. econstructor.
    - ertype. constructor. all: assumption.
    - cbn. rewrite hm. rewrite epm_lift_eq. cbn.
      constructor.
    - ertype.
  }
  assert (hBe : Γ'p ⊢ᶜ Be : cty j).
  {
    subst Be. econstructor.
    - eapply type_epm_lift_eq. 1: ertype.
      cbn. subst Γ'p. destruct_ifs. all: reflexivity.
    - cbn. rewrite hm. rewrite epm_lift_eq. cbn.
      constructor.
    - ertype.
  }
  subst Γ'p.
  econstructor.
  - ertype. instantiate (1 := if isProp mx then _ else _).
    destruct_if e.
    + mode_eqs. cbn in hAp.
      apply param_pProp in hAp.
      eapply ccmeta_conv.
      * {
        ertype.
        - eapply ccmeta_conv. 1: ertype.
          cbn. reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            econstructor.
            * ertype. apply crtyping_shift. apply crtyping_S.
            * {
              cbn. unfold Te. cbn.
              rewrite andb_false_r. rewrite hm.
              change (epm_lift ?t) with (vreg ⋅ t). cbn.
              eapply cconv_trans.
              2:{
                eapply ccong_Pi. 2: econv.
                apply cconv_sym. constructor.
              }
              instantiate (1 := if isKind m then _ else _).
              destruct_if e1.
              - cbn. eapply cconv_trans. 1: constructor.
                cbn. econv. apply ccmeta_refl.
                unfold close. unfold Be.
                change (epm_lift ?t) with (vreg ⋅ t).
                change (λ n, S (S n)) with (S >> S). rasimpl.
                eapply ext_cterm_scoped. 1: apply erase_scoping.
                intros [] hx. 1: discriminate.
                cbn. rasimpl. reflexivity.
              - cbn. eapply cconv_trans. 1: constructor.
                cbn. econv. apply ccmeta_refl.
                unfold close. unfold Be.
                change (epm_lift ?t) with (vreg ⋅ t).
                change (λ n, S (S n)) with (S >> S). rasimpl.
                eapply ext_cterm_scoped. 1: apply erase_scoping.
                intros [] hx. 1: discriminate.
                cbn. rasimpl. reflexivity.
            }
            * {
              cbn. ertype.
              - change (λ n, S (S n)) with (S >> S).
                eapply ccmeta_conv. 1: ertype.
                cbn. reflexivity.
              - instantiate (1 := if isKind m then _ else _).
                destruct_if e. all: ertype.
            }
          + instantiate (2 := if isKind m then _ else _).
            instantiate (1 := if isKind m then _ else _).
            destruct_if e. all: cbn. all: reflexivity.
      }
      * reflexivity.
    + cbn. ertype.
      * {
        econstructor.
        - ertype.
        - cbn. rewrite epm_lift_eq. cbn. rewrite e. cbn. constructor.
        - ertype.
      }
      * {
        econstructor.
        - ertype.
        - cbn. instantiate (1 := if isKind mx then _ else _).
          destruct_if ek.
          + cbn. eapply cconv_trans. 1: constructor.
            cbn. econv.
          + cbn. eapply cconv_trans. 1: constructor.
            cbn. econv.
        - cbn. ertype.
          econstructor.
          + ertype.
          + cbn. rewrite e. rewrite epm_lift_eq. cbn. constructor.
          + ertype.
      }
      * {
        eapply ccmeta_conv.
        - ertype.
          + econstructor.
            * ertype. destruct_if ek.
              all: eapply crtyping_shift_eq.
              1,3: eapply crtyping_shift ; apply crtyping_S.
              all: cbn. all: f_equal.
              all: rasimpl. all: reflexivity.
            * {
              cbn. instantiate (1 := if isKind m then _ else _).
              destruct (isKind m) eqn:ek.
              - cbn. eapply cconv_trans. 1: constructor.
                cbn. econv.
              - cbn. eapply cconv_trans. 1: constructor.
                cbn. econv.
            }
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype.
                  destruct_if emx.
                  * eapply crtyping_shift_eq with (A := capp (S ⋅ Ap) (cvar 0)).
                    1:{ eapply crtyping_shift with (A := cEl Ae). apply crtyping_S. }
                    cbn. f_equal. rasimpl. reflexivity.
                  * eapply crtyping_shift_eq with (A := capp (S ⋅ Ap) (cvar 0)).
                    1:{ eapply crtyping_shift with (A := cEl Ae). apply crtyping_S. }
                    cbn. f_equal. rasimpl. reflexivity.
                + cbn. reflexivity.
              - instantiate (2 := if isKind m then _ else _).
                instantiate (1 := if isKind m then _ else _).
                destruct (isKind m). all: ertype.
            }
          + destruct (isGhost mx && relm m) eqn:ee.
            * {
              apply andb_prop in ee. destruct ee as [emx rm]. mode_eqs.
              cbn. cbn in hBp. cbn in hAp. cbn in hBe.
              apply param_pGhost in hAp. 2,3: assumption.
              econstructor.
              - ertype.
              - cbn. change (λ n, S (S (S n))) with (S >> S >> S).
                unfold Te, Be. cbn. rewrite hm.
                destruct (isGhost m) eqn:eg.
                1:{ mode_eqs. discriminate. }
                cbn. rewrite epm_lift_eq. cbn.
                eapply cconv_trans. 1: constructor.
                apply ccmeta_refl. f_equal.
                change (epm_lift ?t) with (vreg ⋅ t).
                ssimpl. rewrite rinstInst'_cterm.
                eapply ext_cterm_scoped. 1: apply erase_scoping.
                intros [] hx. 1: discriminate.
                cbn. reflexivity.
              - ertype. eapply ccmeta_conv. 1: ertype. 2: reflexivity.
                eapply crtyping_shift_eq with (A := capp (S ⋅ Ap) (cvar 0)).
                1:{ eapply crtyping_shift with (A := cEl Ae). apply crtyping_S. }
                cbn. f_equal. rasimpl. reflexivity.
            }
            * {
              eapply ccmeta_conv.
              - ertype. econstructor.
                + ertype.
                + cbn. unfold Te, Ae. cbn. rewrite hm.
                  change (epm_lift ?t) with (vreg ⋅ t).
                  destruct (relm mx) eqn:emx.
                  2: destruct (isGhost m && isGhost mx) eqn:eg.
                  * cbn. eapply cconv_trans. 1: constructor.
                    econstructor.
                    1:{ apply ccmeta_refl. rasimpl. reflexivity. }
                    econv.
                  * cbn. eapply cconv_trans. 1: constructor.
                    econstructor.
                    1:{ apply ccmeta_refl. rasimpl. reflexivity. }
                    apply ccmeta_refl. rasimpl.
                    rewrite rinstInst'_cterm. f_equal.
                    eapply ext_cterm_scoped. 1: apply erase_scoping.
                    intros [] hx.
                    1:{ cbn in hx. rewrite emx in hx. discriminate. }
                    cbn. reflexivity.
                  * destruct mx. all: try discriminate.
                    destruct m. all: discriminate.
                + cbn. change (λ n, (S (S n))) with (S >> S). ertype.
                  * {
                    econstructor.
                    - ertype.
                    - cbn. rewrite epm_lift_eq. cbn. rewrite e. cbn.
                      constructor.
                    - ertype.
                  }
                  * {
                    econstructor.
                    - ertype.
                      + eapply crtyping_shift_eq with (A := cEl Ae).
                        * change (λ n, S (S (S n))) with (S >> S >> S).
                          ertype. all: shelve.
                        * f_equal. f_equal. f_equal.
                          change (λ n, S (S (S n))) with (S >> S >> S).
                          rasimpl. reflexivity.
                      + cbn.
                        destruct (relm mx) eqn:emx.
                        * eapply crtyping_shift_eq.
                          1: apply typing_er_sub_param.
                          reflexivity.
                        * eapply crtyping_upren_none.
                          apply typing_er_sub_param.
                    - cbn. rewrite hm. cbn. constructor.
                    - ertype.
                  }
              - cbn. unfold Be. change (epm_lift ?t) with (vreg ⋅ t).
                ssimpl. f_equal. rewrite rinstInst'_cterm.
                ssimpl. eapply ext_cterm_scoped. 1: apply erase_scoping.
                intros [] hx. 1: reflexivity.
                rasimpl. change (vreg (S ?x)) with (S (S (vreg x))).
                cbn. rasimpl. reflexivity.
            }
        - instantiate (2 := if isKind m then _ else _).
          instantiate (1 := if isKind m then _ else _).
          destruct (isKind m) eqn:ekm.
          + cbn. reflexivity.
          + cbn. reflexivity.
      }
  - apply cconv_sym.
    destruct_if e.
    + mode_eqs.
      unfold pKind. eapply cconv_trans. 1: constructor.
      cbn. econv. destruct_if ep. 1: econv.
      apply ccmeta_refl. f_equal.
      destruct (isKind mx) eqn:emx. all: cbn.
      all: lia.
    + unfold pType. eapply cconv_trans. 1: constructor.
      cbn. econv. destruct_if ep. all: econv.
  - eapply ccmeta_conv.
    + ertype. eapply ccmeta_conv.
      * instantiate (1 := if isKind m then _ else _).
        destruct_if e. all: ertype.
      * instantiate (1 := if isKind m then _ else _).
        destruct_if e. all: reflexivity.
    + instantiate (1 := if isKind m then _ else _).
      destruct_if e. all: reflexivity.
Qed.

Lemma type_pmPiNP_eq :
  ∀ Γ i j m mx A B Te',
    isProp m = false →
    cscoping Γ A mKind →
    cscoping (Γ,, (mx, A)) B mKind →
    Γ ⊢ A : Sort mx i →
    Γ ,, (mx, A) ⊢ B : Sort m j →
    let Γp := ⟦ Γ ⟧p in
    let Te := ⟦ sc Γ | Pi i j m mx A B ⟧pε in
    let Ae := ⟦ sc Γ | A ⟧pε in
    let Ap := ⟦ sc Γ | A ⟧p in
    let Be := ⟦ mx :: sc Γ | B ⟧pε in
    let Bp := ⟦ mx :: sc Γ | B ⟧p in
    Γp ⊢ᶜ Ap : capp (if isKind mx then pKind i else if isProp mx then pProp else pType i) Ae →
    let Γp' :=
      if isProp mx then
        None :: Some (cProp, Ap) :: Γp
      else if isKind mx then
        Some (cType, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γp
      else
        Some (cProp, capp (S ⋅ Ap) (cvar 0)) :: Some (cType, cEl Ae) :: Γp
    in
    Γp' ⊢ᶜ Bp : capp ((if isKind m then pKind else pType) j) Be →
    Te' = cEl Te →
    Γp ⊢ᶜ pmPiNP mx m Te' (cEl Ae) Ap Bp :
    capp ((if isKind m then pKind else pType) (umax mx m i j)) Te.
Proof.
  intros Γ i j m mx A B ? hm hcA hcB hA hB Γp Te Ae Ap Be Bp hAp Γ'p hBp ->.
  apply type_pmPiNP. all: assumption.
Qed.

(* Hint Resolve type_pmPiP : cc_type. *)
Hint Opaque pmPiP pmPiNP pmPi : cc_type.

Lemma type_to_rev_eq :
  ∀ Γ Γ' Γ'' t A,
    Γ'' ⊢ᶜ t : A →
    Γ'' = ⟦ Γ ⟧ε →
    Γ' = ⟦ Γ ⟧v →
    Γ' ⊢ᶜ t : A.
Proof.
  intros Γ ?? u v h -> ->.
  apply type_to_rev. assumption.
Qed.

Lemma cmeta_ctx_conv :
  ∀ Γ Δ t A,
    Γ ⊢ᶜ t : A →
    Γ = Δ →
    Δ ⊢ᶜ t : A.
Proof.
  intros Γ ? t A h ->.
  assumption.
Qed.

Lemma param_erase_typing_eq :
  ∀ Γ sΓ Γp t A,
    Γ ⊢ t : A →
    relm (mdc Γ t) = true →
    Γp = ⟦ Γ ⟧p →
    sΓ = sc Γ →
    Γp ⊢ᶜ ⟦ sΓ | t ⟧pε : ⟦ sΓ | A ⟧pτ.
Proof.
  intros Γ ? ? t A h e -> ->.
  apply param_erase_typing. all: assumption.
Qed.

Lemma psubst_SS_id :
  ∀ mx Γ u n,
    inscope (param_sc (mx :: Γ)) (S (S n)) = true →
    cvar n = psubst (mx :: Γ) Γ (u .: var) (S (S n)).
Proof.
  intros mx Γ u n hx.
  cbn in hx.
  assert (h :
    inscope (
      (if isProp mx then None else Some (if isKind mx then cType else cProp)) ::
      Some cType :: param_sc Γ
    ) (S (S n)) = true
  ).
  { destruct_ifs. all: assumption. }
  clear hx.
  unfold inscope in h. cbn in h.
  unfold psubst. rewrite div2_SS. cbn.
  rewrite PeanoNat.Nat.odd_succ. rewrite PeanoNat.Nat.even_succ.
  destruct (vreg_vpar_dec n) as [e | e].
  - set (p := Nat.div2 n) in *.
    rewrite e in h. rewrite nth_error_param_vpar in h.
    destruct (nth_error _ p) as [mp|] eqn:ep. 2: discriminate.
    cbn in h.
    destruct (isProp mp) eqn:epp. 1: discriminate.
    rewrite e. rewrite odd_vpar.
    destruct (relm mp) eqn:erp.
    + reflexivity.
    + destruct mp. all: try discriminate.
      cbn. reflexivity.
  - set (p := Nat.div2 n) in *.
    rewrite e in h. rewrite nth_error_param_vreg in h.
    destruct (nth_error _ p) as [mp|] eqn:ep. 2: discriminate.
    cbn in h.
    rewrite e. rewrite odd_vreg.
    destruct (relm mp) eqn:erp. 2: destruct (isGhost mp) eqn:egp.
    + unfold relv. rewrite ep. rewrite erp. reflexivity.
    + unfold ghv. rewrite ep. rewrite egp. reflexivity.
    + destruct mp. all: try discriminate.
      cbn. reflexivity.
Qed.

Ltac hide_ctx C :=
  lazymatch goal with
  | |- ?G ⊢ᶜ _ ≡ _ => set (C := G)
  end.

Ltac lhs_ssimpl' :=
  let G := fresh "G" in
  hide_ctx G ; lhs_ssimpl ; subst G.

Ltac lhs_hnf :=
  lazymatch goal with
  | |- _ ⊢ᶜ ?t ≡ _ => let t' := eval hnf in t in change t with t'
  | |- ?t = _ => let t' := eval hnf in t in change t with t'
  end.

Theorem param_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | t ⟧p : ptype Γ t A.
Proof.
  intros Γ t A h.
  induction h.
  - cbn.
    unfold ptype. cbn.
    unfold relv, ghv, sc.
    rewrite nth_error_map. rewrite H. cbn.
    erewrite nth_error_nth.
    2:{ erewrite nth_error_map. rewrite H. reflexivity. }
    cbn.
    destruct_if e.
    + mode_eqs. cbn.
      eapply ccmeta_conv.
      * econstructor. eapply param_ctx_vreg. eassumption.
      * erewrite param_ren.
        2:{ intros y my ey.
          erewrite <- nth_error_skipn with (x := S x) in ey.
          exact ey.
        }
        2:{ intros y ey. rewrite <- nth_error_skipn in ey. assumption. }
        rasimpl. eapply extRen_cterm. intro n.
        rewrite pren_comp_S. rewrite pren_plus.
        unfold vreg. lia.
    + eapply ccmeta_conv.
      * econstructor. eapply param_ctx_vpar. all: eassumption.
      * erewrite param_ren.
        2:{ intros y my ey.
          erewrite <- nth_error_skipn with (x := S x) in ey.
          exact ey.
        }
        2:{ intros y ey. rewrite <- nth_error_skipn in ey. assumption. }
        destruct_ifs.
        -- rasimpl. f_equal.
          ++ eapply extRen_cterm. intro. rasimpl.
            rewrite pren_comp_S. rewrite pren_plus.
            unfold vpar. unfold shift, funcomp. lia.
          ++ rewrite epm_lift_eq. cbn. f_equal. unfold vpar, vreg. lia.
        -- rasimpl. f_equal.
          ++ eapply extRen_cterm. intro. rasimpl.
            rewrite pren_comp_S. rewrite pren_plus.
            unfold vpar. unfold shift, funcomp. lia.
          ++ rewrite epm_lift_eq. cbn. f_equal. unfold vpar, vreg. lia.
        -- destruct m. all: discriminate.
  - cbn. destruct_ifs. all: mode_eqs. all: try discriminate.
    + cbn. rewrite epm_lift_eq. cbn.
      econstructor.
      * etype.
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. econv.
      * eapply ccmeta_conv. 1: etype.
        reflexivity.
    + cbn. rewrite epm_lift_eq. cbn.
      econstructor. 1: etype.
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. econv.
      * eapply ccmeta_conv. 1: etype.
        reflexivity.
    + rewrite epm_lift_eq. cbn.
      econstructor.
      * ertype.
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. econv. apply ccmeta_refl. f_equal. unfold usup. rewrite e0.
        reflexivity.
      * eapply ccmeta_conv. 1: etype. 2: reflexivity.
        eapply ccmeta_conv. 1: etype.
        unfold usup. rewrite e0. reflexivity.
  - (* Preprocessing *)
    unfold ptype in IHh1. cbn in IHh1. remd in IHh1.
    cbn in IHh1.
    unfold ptype in IHh2. cbn in IHh2. remd in IHh2.
    cbn in IHh2.
    (* End *)
    unfold ptype. cbn - [pmPi].
    set (rm := relm m). set (rmx := relm mx). simpl. (* subst rm rmx. *)
    unfold pmPi. destruct (isProp m) eqn:em.
    + subst rm. mode_eqs. simpl. simpl in IHh2.
      rewrite andb_false_r.
      eapply param_pProp in IHh2.
      econstructor.
      * eapply type_pmPiP. 2,3: eassumption. 2: reflexivity.
        {
          intro emx.
          econstructor.
          - ertype.
          - cbn. rewrite emx. rewrite epm_lift_eq. cbn. constructor.
          - ertype.
        }
      * apply cconv_sym. eapply cconv_trans. 1: constructor.
        cbn. econv.
      * change (epm_lift ctt) with ctt.
        eapply ccmeta_conv. 1: ertype.
        cbn. reflexivity.
    + subst rm rmx.
      eapply ccmeta_conv.
      * {
        rewrite param_erase_ty_tm in IHh2.
        eapply type_pmPiNP_eq. all: try eassumption.
        - destruct (isKind m). all: eassumption.
        - cbn. rewrite em. reflexivity.
      }
      * cbn. rewrite em. destruct (isKind m). all: reflexivity.
  - (* Preprocessing *)
    unfold ptype in IHh1. cbn in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. cbn in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh3. cbn in IHh3. remd in IHh3.
    (* End *)
    unfold ptype. cbn - [pmPiP pmPiNP]. remd.
    unfold pmPi.
    set (rm := relm m). set (rmx := relm mx).
    destruct (isProp mx) eqn:exp.
    + mode_eqs. subst rmx. simpl.
      simpl in IHh1. apply param_pProp in IHh1.
      econstructor.
      * ertype.
      * {
        subst rm. apply cconv_sym.
        destruct_if e.
        - destruct_if emp. 1:{ mode_eqs. discriminate. }
          rewrite andb_false_r.
          unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
          cbn. ssimpl. econv.
          + apply ccmeta_refl. eapply ext_cterm.
            intros [| []]. all: reflexivity.
          + apply ccmeta_refl.
            change (epm_lift ?t) with (vreg ⋅ t). ssimpl.
            eapply ext_cterm_scoped. 1: apply erase_scoping.
            intros [] hx. 1: discriminate.
            rasimpl. change (vreg (S ?x)) with (S (S (vreg x))).
            rasimpl. reflexivity.
        - destruct_if eg.
          + mode_eqs. cbn. eapply cconv_trans. 1: constructor.
            cbn. ssimpl. econv.
            * apply ccmeta_refl. eapply ext_cterm.
              intros [| []]. all: reflexivity.
            * apply ccmeta_refl.
              change (rpm_lift ?t) with (vreg ⋅ t). ssimpl.
              eapply ext_cterm_scoped. 1: apply revive_scoping.
              intros [] hx. 1: discriminate.
              rasimpl. change (vreg (S ?x)) with (S (S (vreg x))).
              rasimpl. reflexivity.
          + destruct_if ep. 2:{ destruct m. all: discriminate. }
            apply cconv_refl.
      }
      * {
        subst rm. instantiate (1 := if relm m then _ else _).
        destruct_if erm.
        - destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
          rewrite andb_false_r.
          eapply ccmeta_conv.
          + ertype.
            * {
              eapply ctype_conv.
              - eapply type_pmPiNP_eq. all: try eassumption.
                + cbn. econstructor.
                  * ertype.
                  * apply cconv_sym. cbn. unfold pProp. constructor.
                  * {
                    eapply ccmeta_conv. 1: ertype. 2: reflexivity.
                    econstructor.
                    - ertype.
                    - cbn. rewrite epm_lift_eq. cbn. constructor.
                    - ertype.
                  }
                + cbn. destruct_if ek. all: eassumption.
                + cbn. rewrite andb_false_r. rewrite ep. reflexivity.
              - cbn. rewrite andb_false_r. rewrite ep.
                instantiate (1 := if isKind m then _ else _).
                destruct_if e.
                + unfold pKind. eapply cconv_trans. 1: constructor.
                  cbn. econv.
                + unfold pType. eapply cconv_trans. 1: constructor.
                  cbn. econv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    apply type_epm_lift. ertype.
                    - econstructor.
                      + ertype.
                      + cbn. rewrite ep. cbn. constructor.
                      + ertype.
                    - reflexivity. (* Could be something else *)
                  }
                  * rewrite epm_lift_eq. cbn. reflexivity.
                + instantiate (1 := if isKind m then _ else _).
                  destruct_if e. all: ertype.
            }
            * {
              change (cEl (epm_lift ?t)) with (epm_lift (cEl t)).
              apply type_epm_lift.
              econstructor.
              - ertype. remd. assumption.
              - cbn. apply cconv_sym. eapply cconv_trans. 1: constructor.
                econv.
              - ertype.
                + econstructor.
                  * ertype.
                  * cbn. rewrite ep. cbn. constructor.
                  * ertype.
                + reflexivity. (* Could be something else *)
            }
          + instantiate (2 := if isKind m then _ else _).
            instantiate (1 := if isKind m then _ else _).
            destruct_if e. all: cbn. all: reflexivity.
        - destruct (isKind m) eqn:ekm. 1:{ mode_eqs. discriminate. }
          destruct_if e.
          + mode_eqs. cbn. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ctype_conv.
                + eapply type_pmPiNP_eq. all: try eassumption.
                  * {
                    cbn. econstructor.
                    - ertype.
                    - apply cconv_sym. unfold pProp. constructor.
                    - eapply ccmeta_conv.
                      + ertype. econstructor.
                        * ertype.
                        * cbn. rewrite epm_lift_eq. cbn. constructor.
                        * ertype.
                      + cbn. reflexivity.
                  }
                  * cbn. reflexivity.
                + cbn. unfold pType. eapply cconv_trans. 1: constructor.
                  cbn. econv.
                + ertype. eapply ccmeta_conv.
                  * {
                    eapply type_epm_lift. ertype.
                    - econstructor.
                      + ertype.
                      + cbn. constructor.
                      + ertype.
                    - reflexivity. (* Could be something else *)
                  }
                  * change (epm_lift ?t) with (vreg ⋅ t). cbn. reflexivity.
              - change (cEl (epm_lift ?t)) with (epm_lift (cEl t)).
                apply type_rpm_lift. econstructor.
                + ertype.
                + cbn. apply cconv_sym. constructor.
                + apply type_to_rev.
                  ertype.
                  * {
                    econstructor.
                    - ertype.
                    - cbn. constructor.
                    - ertype.
                  }
                  * reflexivity. (* Could be something else *)
            }
            * cbn. reflexivity.
          + destruct m. all: try discriminate.
            cbn in IHh2. apply param_pProp in IHh2.
            cbn. eapply ccmeta_conv.
            * ertype. eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * cbn. reflexivity.
      }
    + assert (hAe : ⟦ Γ ⟧ε ⊢ᶜ ⟦ (sc Γ) | A ⟧ε : cty i).
      {
        econstructor.
        - ertype.
        - cbn. rewrite exp. constructor.
        - ertype.
      }
      assert (hBe :
        isProp m = false →
        let Γ' :=
          if relm mx then Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
          else None :: ⟦ Γ ⟧ε
        in
        Γ' ⊢ᶜ ⟦ mx :: sc Γ | B ⟧ε : cty j
      ).
      {
        intro ep.
        econstructor.
        - eapply erase_typing_eq.
          + eassumption.
          + remd. reflexivity.
          + cbn. reflexivity.
          + reflexivity.
        - cbn. rewrite ep. constructor.
        - ertype.
      }
      cbn zeta in hBe.
      assert (hte :
        relm m = true →
        let Γ' :=
          if relm mx then Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
          else None :: ⟦ Γ ⟧ε
        in
        Γ' ⊢ᶜ ⟦ mx :: sc Γ | t ⟧ε : ⟦ mx :: sc Γ | B ⟧τ
      ).
      {
        intro er.
        eapply erase_typing_eq.
        - eassumption.
        - remd. assumption.
        - cbn. reflexivity.
        - reflexivity.
      }
      cbn zeta in hte.
      econstructor.
      * {
        ertype.
        - econstructor.
          + ertype.
          + cbn. instantiate (1 := if isKind mx then _ else _).
            destruct_if e. all: unfold pKind, pType.
            all: cbn. all: eapply cconv_trans. 1,3: constructor.
            all: cbn. all: apply cconv_refl.
          + cbn. ertype.
        - instantiate (1 := if isKind mx then _ else _).
          destruct_if e. all: ertype.
      }
      * {
        subst rm. destruct (relm m) eqn: erm.
        - destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
          destruct (isGhost m) eqn:eg. 1:{ mode_eqs. discriminate. }
          simpl. unfold pmPiNP. rewrite erm. rewrite exp. apply cconv_sym.
          eapply cconv_trans. 1: constructor.
          unfold pPi. cbn. ssimpl.
          rewrite <- rinstInst'_cterm. econv.
          eapply cconv_trans.
          2:{ destruct_if ekx. all: econv. }
          econv.
          + apply ccmeta_refl.
            rewrite <- rinstId'_cterm. rewrite rinstInst'_cterm.
            eapply ext_cterm. intros [| []]. all: reflexivity.
          + destruct (isGhost mx) eqn:egx.
            * mode_eqs. cbn. apply ccmeta_refl. unfold close.
              change (epm_lift ?t) with (vreg ⋅ t).
              rasimpl. rewrite rinstInst'_cterm.
              eapply ext_cterm_scoped. 1: apply erase_scoping.
              intros [] hx. 1: discriminate.
              cbn. rasimpl. reflexivity.
            * subst rmx. destruct (relm mx) eqn: emx.
              2:{ destruct mx. all: discriminate. }
              cbn. change (epm_lift ?t) with (vreg ⋅ t).
              cbn. eapply cconv_trans. 1: constructor.
              apply ccmeta_refl. rasimpl. rewrite rinstInst'_cterm.
              eapply ext_cterm_scoped. 1: apply erase_scoping.
              intros [] hx. 1: reflexivity.
              rasimpl. reflexivity.
        - destruct (isGhost m) eqn: eg.
          + mode_eqs. simpl. unfold pmPiNP. rewrite exp.
            apply cconv_sym. eapply cconv_trans. 1: constructor.
            simpl. rewrite andb_false_r.
            cbn. unfold pPi. ssimpl.
            rewrite <- rinstInst'_cterm. econv.
            eapply cconv_trans.
            2:{ destruct_if ekx. all: econv. }
            econv.
            * apply ccmeta_refl.
              rewrite <- rinstId'_cterm. rewrite rinstInst'_cterm.
              eapply ext_cterm. intros [| []]. all: reflexivity.
            * change (rpm_lift ?t) with (vreg ⋅ t). cbn.
              eapply cconv_trans. 1: constructor.
              apply ccmeta_refl. rasimpl. rewrite rinstInst'_cterm.
              eapply ext_cterm_scoped. 1: apply revive_scoping.
              intros [] hx. 1: reflexivity.
              rasimpl. reflexivity.
          + destruct m. all: try discriminate.
            cbn. unfold pmPiP. rewrite exp.
            destruct_if e.
            all: econv.
      }
      * {
        instantiate (1 := if rm then _ else _).
        subst rm. destruct (relm m) eqn: erm.
        - destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
          destruct (isGhost m) eqn:eg. 1:{ mode_eqs. discriminate. }
          simpl.
          eapply ccmeta_conv.
          + ertype.
            * {
              eapply ctype_conv.
              - eapply type_pmPiNP_eq. all: try eassumption.
                + rewrite exp. assumption.
                + rewrite exp. eapply ccmeta_conv.
                  * destruct_if e. all: eassumption.
                  * destruct_if e. all: reflexivity.
                + cbn. rewrite ep. rewrite eg. cbn.
                  change (cEl (epm_lift ?t)) with (epm_lift (cEl t)).
                  reflexivity.
              - cbn. rewrite ep. rewrite eg. cbn.
                instantiate (1 := if isKind m then _ else _).
                destruct_if ek.
                + unfold pKind. eapply cconv_trans. 1: constructor.
                  cbn. econv.
                + unfold pType. eapply cconv_trans. 1: constructor.
                  cbn. econv.
              - ertype.
                + eapply ccmeta_conv.
                  * {
                    apply type_epm_lift.
                    instantiate (1 := if relm mx then _ else _).
                    destruct (relm mx) eqn: erx.
                    - cbn. ertype. all: reflexivity.
                    - cbn. destruct mx. all: try discriminate.
                      cbn in *.
                      ertype.
                      + eapply ccmeta_conv. 1: ertype.
                        cbn. reflexivity.
                      + reflexivity. (* Could be something else *)
                  }
                  * rewrite epm_lift_eq.
                    instantiate (1 := if relm mx then _ else _).
                    destruct_if e. all: cbn. all: reflexivity.
                + instantiate (1 := if isKind m then _ else _).
                  destruct (isKind m). all: ertype.
            }
            * {
              change (cEl (epm_lift ?t)) with (epm_lift (cEl t)).
              apply type_epm_lift. subst rmx.
              destruct (relm mx) eqn: erx.
              - cbn. econstructor.
                + ertype. reflexivity.
                + apply cconv_sym. constructor.
                + ertype. all: reflexivity.
              - cbn. econstructor.
                + ertype. reflexivity.
                + apply cconv_sym. constructor.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - ertype. reflexivity.
                    - cbn. reflexivity.
                  }
                  * reflexivity. (* Could be something else *)
            }
          + instantiate (2 := if isKind m then _ else _).
            instantiate (1 := if isKind m then _ else _).
            destruct (isKind m). all: cbn. all: reflexivity.
        - instantiate (1 := if isGhost m then _ else _).
          destruct (isGhost m) eqn: eg.
          + mode_eqs. cbn in IHh2. simpl.
            eapply ccmeta_conv.
            * {
              ertype.
              - eapply ctype_conv.
                + eapply type_pmPiNP_eq. all: try eassumption.
                  * rewrite exp. assumption.
                  * rewrite exp.
                    eapply ccmeta_conv.
                    -- destruct_if e. all: eassumption.
                    -- cbn. reflexivity.
                  * cbn.
                    change (cEl (epm_lift ?t)) with (epm_lift (cEl t)).
                    reflexivity.
                + cbn. rewrite exp. subst rmx.
                  destruct (relm mx) eqn:erx. 2: destruct (isGhost mx) eqn:egx.
                  * cbn.
                    change (epm_lift (ctyval ?mk ?u ?v))
                    with (ctyval mk (epm_lift u) (epm_lift v)).
                    unfold pType.
                    eapply cconv_trans. 1: constructor.
                    cbn. econv.
                  * {
                    cbn.
                    change (epm_lift (ctyval ?mk ?u ?v))
                    with (ctyval mk (epm_lift u) (epm_lift v)).
                    unfold pType.
                    eapply cconv_trans. 1: constructor.
                    cbn. rasimpl. change (epm_lift ?t) with (vreg ⋅ t).
                    cbn. rasimpl. econv.
                    - apply ccmeta_refl. rewrite rinstInst'_cterm.
                      eapply ext_cterm_scoped. 1: apply erase_scoping.
                      intros [] hx.
                      + cbn in hx. rewrite erx in hx.
                        discriminate.
                      + rasimpl. reflexivity.
                    - apply ccmeta_refl. rewrite rinstInst'_cterm.
                      eapply ext_cterm_scoped. 1: apply erase_scoping.
                      intros [] hx.
                      + cbn in hx. rewrite erx in hx.
                        discriminate.
                      + rasimpl. reflexivity.
                  }
                  * destruct mx. all: discriminate.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - apply type_rpm_lift. ertype.
                      + apply type_to_rev. ertype.
                      + eapply type_to_rev_eq.
                        * ertype.
                        * instantiate (1 := Γ ,, (mx, A)).
                          cbn. reflexivity.
                        * cbn. rewrite exp. reflexivity.
                    - rewrite epm_lift_eq. cbn. reflexivity.
                  }
                  * {
                    apply type_rpm_lift. ertype.
                    - apply type_to_rev. ertype.
                    - eapply type_to_rev_eq.
                      + ertype.
                      + instantiate (1 := Γ ,, (mx, A)).
                        cbn. reflexivity.
                      + cbn. rewrite exp. reflexivity.
                  }
              - econstructor.
                + apply type_rpm_lift. ertype.
                  * apply type_to_rev. ertype.
                  * {
                    eapply revive_typing_eq.
                    - eassumption.
                    - remd. reflexivity.
                    - cbn. rewrite exp. reflexivity.
                    - cbn. reflexivity.
                  }
                + apply cconv_sym. constructor.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - apply type_rpm_lift. ertype.
                      + apply type_to_rev. ertype.
                      + eapply type_to_rev_eq.
                        * ertype.
                        * instantiate (1 := Γ ,, (mx, A)).
                          cbn. reflexivity.
                        * cbn. rewrite exp. reflexivity.
                    - cbn. rewrite epm_lift_eq. cbn. reflexivity.
                  }
                  * {
                    apply type_rpm_lift. ertype.
                    - apply type_to_rev. ertype.
                    - eapply type_to_rev_eq.
                      + ertype.
                      + instantiate (1 := Γ ,, (mx, A)).
                        cbn. reflexivity.
                      + cbn. rewrite exp. reflexivity.
                  }
            }
            * cbn. reflexivity.
          + destruct m. all: try discriminate.
            simpl. eapply type_pmPiP.
            2:{ rewrite exp. eassumption. }
            2:{
              rewrite exp. cbn in IHh2. apply param_pProp in IHh2.
              assumption.
            }
            2: reflexivity.
            intro. eapply ccmeta_conv.
            * apply type_epm_lift. ertype.
            * reflexivity.
      }
  - (* Preprocessing *)
    unfold ptype in IHh1. cbn - [pmPi] in IHh1. remd in IHh1.
    unfold ptype in IHh2. remd in IHh2.
    unfold ptype in IHh3. cbn in IHh3. remd in IHh3. cbn in IHh3.
    unfold ptype in IHh4. cbn in IHh4. remd in IHh4. cbn in IHh4.
    unfold ptype. cbn. remd.
    set (rm := relm m) in *.
    assert (hAe : isProp mx = false → ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧pε : cty i).
    {
      intro epx.
      econstructor.
      - ertype.
      - cbn. rewrite epx. rewrite epm_lift_eq. cbn. constructor.
      - ertype.
    }
    assert (hBe :
      isProp m = false →
      let Γ' :=
        if isProp mx then None :: Some (cProp, ⟦ sc Γ | A ⟧p) :: ⟦ Γ ⟧p
        else if isKind mx then
          Some (cType, capp (S ⋅ ⟦ (sc Γ) | A ⟧p) (cvar 0)) ::
          Some (cType, ⟦ (sc Γ) | A ⟧pτ) :: ⟦ Γ ⟧p
        else
          Some (cProp, capp (S ⋅ ⟦ (sc Γ) | A ⟧p) (cvar 0)) ::
          Some (cType, ⟦ (sc Γ) | A ⟧pτ) :: ⟦ Γ ⟧p
      in
      Γ' ⊢ᶜ ⟦ mx :: sc Γ | B ⟧pε : cty j
    ).
    {
      intro ep.
      cbn zeta.
      econstructor.
      - eapply param_erase_typing_eq.
        + eassumption.
        + remd. reflexivity.
        + cbn. reflexivity.
        + cbn. reflexivity.
      - cbn. rewrite ep. change (epm_lift ?t) with (vreg ⋅ t). cbn. constructor.
      - ertype.
    }
    eapply ctype_conv in IHh3 as hAp.
    2:{
      instantiate (1 :=
        if isProp mx then _
        else cPi _ _ (if isKind mx then _ else _)
      ).
      destruct (isKind mx) eqn: ekx. 2: destruct (isProp mx) eqn: epx.
      - destruct (isProp mx) eqn: epx. 1:{ mode_eqs. discriminate. }
        unfold pKind. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - unfold pProp. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - unfold pType. eapply cconv_trans. 1: constructor.
        cbn. econv.
    }
    2:{
      instantiate (1 := if isProp mx then _ else if isKind mx then _ else _).
      destruct (isProp mx) eqn: epx.
      - mode_eqs. cbn. ertype.
      - eapply ccmeta_conv.
        + ertype. 1: reflexivity.
          instantiate (1 := if isKind mx then _ else _).
          destruct_if e. all: ertype.
        + cbn. f_equal. destruct_if e.
          * instantiate (1 := S i). lia.
          * instantiate (1 := i). lia.
    }
    eapply ctype_conv in IHh4 as hBp.
    2:{
      instantiate (1 := if isKind m then _ else _).
      destruct (isKind m) eqn:ek.
      - unfold pKind. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - instantiate (1 := if isProp m then _ else _).
        destruct (isProp m) eqn: epm.
        + unfold pProp. eapply cconv_trans. 1: constructor.
          cbn. econv.
        + unfold pType. eapply cconv_trans. 1: constructor.
          cbn. econv.
    }
    2:{
      instantiate (1 := if isKind m then _ else if isProp m then _ else _).
      destruct (isKind m) eqn:ek. 2: destruct (isProp m) eqn:ep.
      - mode_eqs. ertype.
      - ertype.
      - ertype. reflexivity.
    }
    eapply ctype_conv in IHh1 as htp.
    2:{
      set (rmx := relm mx) in *.
      instantiate (1 := if rm then _ else _).
      subst rm.
      destruct_if er.
      - unfold pmPi.
        destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
        destruct (isGhost m) eqn:eg. 1:{ mode_eqs. discriminate. }
        simpl. unfold pmPiNP. rewrite er.
        eapply cconv_trans. 1: constructor.
        instantiate (1 := if isProp mx then _ else _).
        destruct_if epx.
        + cbn. lhs_ssimpl. econv.
        + cbn. lhs_ssimpl. rewrite <- rinstInst'_cterm.
          econstructor. 1: econv.
          econstructor. 1: econv.
          econstructor. 1: econv.
          instantiate (1 := if isGhost mx then _ else _).
          destruct (isGhost mx) eqn:egx.
          * cbn. econv.
          * cbn. econv.
      - instantiate (1 := if isGhost m then _ else _).
        destruct (isGhost m) eqn:eg.
        + mode_eqs. unfold pmPi. simpl. unfold pmPiNP.
          eapply cconv_trans. 1: constructor.
          simpl.
          instantiate (1 := if isProp mx then _ else _).
          destruct (isProp mx) eqn:epx.
          * mode_eqs. cbn. rasimpl. econv.
          * unfold pPi. cbn. lhs_ssimpl.
            rewrite andb_false_r. cbn.
            rewrite <- rinstInst'_cterm. econv.
        + destruct m. all: try discriminate.
          unfold pmPi. cbn. econv.
    }
    2:{
      instantiate (1 := if rm then _ else _).
      destruct rm eqn:er.
      - destruct (isProp m) eqn:ep. { mode_eqs. discriminate. }
        destruct (isGhost m) eqn:eg. { mode_eqs. discriminate. }
        instantiate (1 := if isProp mx then _ else _).
        destruct (isProp mx) eqn:epx.
        + mode_eqs. eapply ccmeta_conv.
          * {
            ertype. eapply ccmeta_conv.
            - ertype. 2:{ remd. assumption. }
              instantiate (1 := if isKind m then _ else _).
              destruct (isKind m) eqn:ek.
              + mode_eqs. econstructor.
                * {
                  eapply ctyping_subst. 2: eassumption.
                  constructor.
                  - rasimpl. constructor.
                    + rasimpl. apply crtyping_typing.
                      apply crtyping_S.
                    + cbn. split.
                      * constructor. reflexivity.
                      * rasimpl. ertype.
                  - cbn. constructor.
                }
                * cbn. change (epm_lift ?t) with (vreg ⋅ t). cbn.
                  econstructor. 2: econv.
                  apply cconv_sym. eapply cconv_trans. 1: constructor.
                  econv. apply ccmeta_refl. ssimpl.
                  eapply ext_cterm_scoped. 1: apply erase_scoping.
                  intros [| []] hx. 1: discriminate. all: reflexivity.
                * {
                  ertype. eapply ccmeta_conv.
                  - ertype. eapply type_epm_lift.
                    eapply erase_typing_El.
                    + eapply erase_typing.
                      * econstructor. all: eassumption.
                      * reflexivity.
                    + reflexivity.
                  - change (epm_lift ?t) with (vreg ⋅ t). cbn. reflexivity.
                }
              + destruct m. all: try discriminate.
                econstructor.
                * {
                  eapply ctyping_subst. 2: eassumption.
                  constructor.
                  - rasimpl. constructor.
                    + rasimpl. apply crtyping_typing.
                      apply crtyping_S.
                    + cbn. split.
                      * constructor. reflexivity.
                      * rasimpl. ertype.
                  - cbn. constructor.
                }
                * cbn. econstructor. 2: econv.
                  change (epm_lift ?t) with (vreg ⋅ t). cbn.
                  apply cconv_sym. eapply cconv_trans. 1: constructor.
                  econv. apply ccmeta_refl. ssimpl.
                  eapply ext_cterm_scoped. 1: apply erase_scoping.
                  intros [| []] hx. 1: discriminate. all: reflexivity.
                * {
                  ertype. eapply ccmeta_conv.
                  - ertype. eapply type_epm_lift.
                    eapply erase_typing_El.
                    + eapply erase_typing.
                      * econstructor. all: eassumption.
                      * reflexivity.
                    + reflexivity.
                  - change (epm_lift ?t) with (vreg ⋅ t). cbn. reflexivity.
                }
            - instantiate (2 := if isKind m then _ else _).
              instantiate (1 := if isKind m then _ else _).
              destruct (isKind m) eqn:ek. all: cbn. all: reflexivity.
          }
          * reflexivity.
        + ertype.
          * {
            eapply ccmeta_conv.
            - ertype. eapply ccmeta_conv.
              + ertype.
              + cbn. reflexivity.
            - lhs_ssimpl. instantiate (1 := if isKind mx then _ else _).
              destruct (isKind mx) eqn:ek. all: reflexivity.
          }
          * {
            instantiate (1 := if isKind m then _ else _).
            eapply ccmeta_conv.
            - ertype.
              + eapply ccmeta_conv.
                * {
                  eapply ctyping_subst. 2: eassumption.
                  destruct (isKind mx) eqn:ek.
                  - constructor. 1: rasimpl. 1: constructor. 1: rasimpl.
                    + rewrite <- !funcomp_assoc.
                      apply crtyping_typing. ertype.
                    + cbn. split.
                      * ertype.
                      * eapply ccmeta_conv. 1: ertype.
                        cbn. change (λ n, S (S n)) with (S >> S).
                        rasimpl. rewrite rinstInst'_cterm. reflexivity.
                    + cbn. split.
                      * ertype.
                      * eapply ccmeta_conv. 1: ertype.
                        cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
                  - constructor. 1: rasimpl. 1: constructor. 1: rasimpl.
                    + rewrite <- !funcomp_assoc.
                      apply crtyping_typing. ertype.
                    + cbn. split.
                      * ertype.
                      * eapply ccmeta_conv. 1: ertype.
                        cbn. change (λ n, S (S n)) with (S >> S).
                        rasimpl. rewrite rinstInst'_cterm. reflexivity.
                    + cbn. split.
                      * ertype.
                      * eapply ccmeta_conv. 1: ertype.
                        cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
                }
                * instantiate (1 := if isKind m then _ else _).
                  destruct (isKind m) eqn:ek. all: cbn. all: reflexivity.
              + destruct (isGhost mx) eqn:egx.
                * {
                  mode_eqs. cbn.
                  econstructor.
                  - ertype. remd. assumption.
                  - cbn. rewrite eg. cbn. rewrite ep.
                    change (epm_lift ?t) with (vreg ⋅ t).
                    cbn. eapply cconv_trans. 1: constructor.
                    econv. apply ccmeta_refl.
                    ssimpl. eapply ext_cterm_scoped. 1: apply erase_scoping.
                    intros [| []] hx. 1: discriminate. all: reflexivity.
                  - ertype. eapply ccmeta_conv.
                    + eapply ctyping_subst. 2: ertype.
                      cbn. constructor. 1: rasimpl. 1: constructor. 1: rasimpl.
                      * rewrite <- !funcomp_assoc.
                        apply crtyping_typing. ertype.
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. change (λ n, S (S n)) with (S >> S).
                          rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                    + cbn. reflexivity.
                }
                * {
                  destruct (relm mx) eqn:erx.
                  2:{ destruct mx. all: discriminate. }
                  eapply ccmeta_conv.
                  - ertype. econstructor.
                    + ertype. remd. assumption.
                    + cbn. rewrite ep. rewrite erx.
                      cbn. change (epm_lift ?t) with (vreg ⋅ t). cbn.
                      eapply cconv_trans. 1: constructor.
                      econv.
                    + ertype.
                      * eapply ccmeta_conv. 1: ertype.
                        cbn. reflexivity.
                      * {
                        econstructor.
                        - ertype.
                          + eapply crtyping_shift.
                            cbn. change (λ n, S (S n)) with (S >> S).
                            ertype.
                          + cbn. rewrite erx.
                            eapply crtyping_shift_eq.
                            * apply typing_er_sub_param.
                            * cbn. reflexivity.
                        - cbn. rewrite ep. cbn. constructor.
                        - ertype.
                      }
                  - cbn. f_equal. change (epm_lift ?t) with (vreg ⋅ t).
                    rasimpl. eapply ext_cterm_scoped. 1: apply erase_scoping.
                    intros [| []] hx. all: reflexivity.
                }
            - destruct (isKind m) eqn:ek. all: cbn. all: reflexivity.
          }
      - destruct (isKind m) eqn:ek. 1:{ mode_eqs. discriminate. }
        destruct (isGhost m) eqn:eg.
        + mode_eqs. destruct (isProp mx) eqn:epx.
          * {
            mode_eqs. ertype. eapply ccmeta_conv.
            - ertype. econstructor.
              + eapply ctyping_subst. 2: ertype.
                constructor.
                * ssimpl. apply crtyping_typing. ertype.
                * cbn. split. 1: ertype.
                  eapply ccmeta_conv. 1: ertype.
                  cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
              + cbn. apply cconv_sym. change (epm_lift ?t) with (vreg ⋅ t).
                cbn. econstructor. 2: econv.
                eapply cconv_trans. 1: constructor.
                econv. apply ccmeta_refl. ssimpl.
                eapply ext_cterm_scoped. 1: apply erase_scoping.
                intros [| []] hx. 1: discriminate. all: reflexivity.
              + ertype. eapply ccmeta_conv.
                * {
                  ertype. eapply type_epm_lift.
                  eapply erase_typing_El.
                  - eapply erase_typing.
                    + econstructor. all: eassumption.
                    + reflexivity.
                  - reflexivity.
                }
                * change (epm_lift ?t) with (vreg ⋅ t). cbn. reflexivity.
            - cbn. reflexivity.
          }
          * {
            cbn. eapply ccmeta_conv.
            - ertype.
              + eapply ccmeta_conv.
                * ertype. eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                * instantiate (1 := if isKind mx then _ else _).
                  destruct (isKind mx). all: cbn. all: reflexivity.
              + eapply ccmeta_conv.
                * {
                  ertype.
                  2:{
                    econstructor.
                    - ertype.
                    - cbn.
                      instantiate (1 := if relm mx then _ else _).
                      destruct (relm mx) eqn:erx.
                      + cbn. change (epm_lift ?t) with (vreg ⋅ t).
                        cbn. eapply cconv_trans. 1: constructor.
                        econv.
                      + destruct mx. all: try discriminate.
                        cbn. change (epm_lift ?t) with (vreg ⋅ t).
                        cbn. eapply cconv_trans. 1: constructor.
                        econv.
                    - ertype.
                      + eapply ccmeta_conv.
                        * ertype.
                        * cbn. reflexivity.
                      + destruct (relm mx) eqn:erx.
                        * {
                          ertype. econstructor.
                          - ertype.
                            + eapply crtyping_shift. ertype.
                            + cbn. rewrite erx.
                              eapply crtyping_shift_eq.
                              * apply typing_er_sub_param.
                              * reflexivity.
                          - cbn. constructor.
                          - ertype.
                        }
                        * {
                          ertype. econstructor.
                          - ertype.
                            + eapply crtyping_shift. ertype.
                            + eapply crtyping_shift_eq.
                              * apply typing_er_sub_param.
                              * reflexivity.
                            + eapply erase_typing_eq.
                              * eassumption.
                              * remd. reflexivity.
                              * cbn. rewrite erx. reflexivity.
                              * reflexivity.
                          - cbn. constructor.
                          - ertype.
                        }
                  }
                  eapply ccmeta_conv.
                  - eapply ctyping_subst. 2: ertype.
                    destruct (isKind mx) eqn:ekx.
                    + constructor. 1: rasimpl. 1: constructor. 1: rasimpl.
                      * rewrite <- !funcomp_assoc.
                        apply crtyping_typing. ertype.
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. change (λ n, S (S n)) with (S >> S).
                          rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                    + constructor. 1: rasimpl. 1: constructor. 1: rasimpl.
                      * rewrite <- !funcomp_assoc.
                        apply crtyping_typing. ertype.
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. change (λ n, S (S n)) with (S >> S).
                          rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                      * {
                        cbn. split.
                        - ertype.
                        - eapply ccmeta_conv. 1: ertype.
                          cbn. rasimpl. rewrite rinstInst'_cterm. reflexivity.
                      }
                  - cbn. f_equal.
                    change (epm_lift ?t) with (vreg ⋅ t).
                    destruct (relm mx) eqn:erx.
                    + rasimpl. f_equal.
                      eapply ext_cterm_scoped. 1: apply erase_scoping.
                      intros [| []] hx. all: reflexivity.
                    + rasimpl. f_equal.
                      eapply ext_cterm_scoped. 1: apply erase_scoping.
                      intros [| []] hx. 2,3: reflexivity.
                      cbn in hx. rewrite erx in hx. discriminate.
                }
                * cbn. reflexivity.
            - cbn. reflexivity.
          }
        + destruct m. all: try discriminate.
          cbn. eapply type_pmPiP.
          * eapply hAe.
          * eassumption.
          * eapply hBp.
          * reflexivity.
    }
    (* End *)
    destruct (relm mx) eqn: erx. 2: destruct (isGhost mx) eqn: egx.
    + destruct (isGhost mx) eqn: egx. { mode_eqs. discriminate. }
      destruct (isProp mx) eqn: epx. { mode_eqs. discriminate. }
      eapply ccmeta_conv.
      * {
        ertype. eapply ccmeta_conv.
        - ertype. 2:{ remd. assumption. }
          eapply ccmeta_conv. 1: ertype.
          instantiate (1 := if rm then _ else _).
          destruct rm eqn:er.
          + reflexivity.
          + instantiate (1 := if isGhost m then _ else _).
            destruct (isGhost m) eqn:eg.
            * reflexivity.
            * unfold pmPiP. rewrite epx.
              instantiate (1 := if isKind mx then _ else _).
              destruct (isKind mx) eqn:ekx. all: reflexivity.
        - instantiate (2 := if isKind mx then _ else _).
          instantiate (1 := if rm then _ else _).
          destruct rm eqn:er.
          + cbn. lhs_ssimpl. reflexivity.
          + instantiate (1 := if isGhost m then _ else _).
            destruct (isGhost m) eqn:eg.
            * cbn. lhs_ssimpl. reflexivity.
            * {
              destruct (isKind mx) eqn:ekx.
              - cbn. lhs_ssimpl. reflexivity.
              - cbn. rasimpl. reflexivity.
            }
      }
      * {
        destruct rm eqn:erm.
        - rasimpl. f_equal.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn.
          + rewrite erx. reflexivity.
          + rewrite erx. rasimpl. reflexivity.
          + apply psubst_SS_id. assumption.
        - destruct (isGhost m) eqn:egm.
          + mode_eqs. rasimpl. f_equal.
            erewrite param_subst.
            2:{ apply sscoping_one. escope. }
            2: apply sscoping_comp_one.
            eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
            intros [| []] hx. all: cbn.
            * rewrite erx. reflexivity.
            * rewrite erx. rasimpl. reflexivity.
            * apply psubst_SS_id. assumption.
          + destruct m. all: try discriminate.
            rasimpl.
            erewrite param_subst.
            2:{ apply sscoping_one. escope. }
            2: apply sscoping_comp_one.
            eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
            intros [| []] hx. all: cbn.
            * rewrite erx. reflexivity.
            * rewrite erx. reflexivity.
            * apply psubst_SS_id. assumption.
      }
    + mode_eqs.
      eapply ccmeta_conv.
      * {
        ertype. eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype.
          + simpl.
            instantiate (1 := if rm then _ else _).
            destruct rm eqn:er.
            * reflexivity.
            * {
              instantiate (1 := if isGhost m then _ else _).
              destruct (isGhost m) eqn:eg.
              - mode_eqs. reflexivity.
              - destruct m. all: try discriminate.
                reflexivity.
            }
        - instantiate (1 := if rm then _ else if isGhost m then _ else _).
          destruct rm eqn:er. 2: destruct (isGhost m) eqn:eg.
          + cbn. f_equal. rasimpl. reflexivity.
          + cbn. f_equal. rasimpl. reflexivity.
          + destruct m. all: try discriminate.
            cbn. f_equal. rasimpl. reflexivity.
      }
      * {
        destruct rm eqn:er. 2: destruct (isGhost m) eqn:eg.
        - cbn. rasimpl. f_equal.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn.
          + reflexivity.
          + ssimpl. reflexivity.
          + apply psubst_SS_id. assumption.
        - mode_eqs. cbn. ssimpl. f_equal.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn. 1,2: reflexivity.
          apply psubst_SS_id. assumption.
        - destruct m. all: try discriminate.
          rasimpl.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn. 1,2: reflexivity.
          apply psubst_SS_id. assumption.
      }
    + destruct mx. all: try discriminate.
      eapply ccmeta_conv.
      * {
        ertype. eapply ccmeta_conv.
        - ertype.
        - simpl.
          instantiate (1 := if rm then _ else if isGhost m then _ else _).
          destruct rm eqn:er. 2: destruct (isGhost m) eqn:eg.
          + reflexivity.
          + mode_eqs. reflexivity.
          + destruct m. all: try discriminate.
            reflexivity.
      }
      * {
        destruct rm eqn:er. 2: destruct (isGhost m) eqn:eg.
        - cbn. rasimpl. f_equal.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn.
          + cbn in hx. discriminate.
          + reflexivity.
          + apply psubst_SS_id. assumption.
        - mode_eqs. cbn. ssimpl. f_equal.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn.
          + discriminate.
          + reflexivity.
          + apply psubst_SS_id. assumption.
        - destruct m. all: try discriminate.
          ssimpl.
          erewrite param_subst.
          2:{ apply sscoping_one. escope. }
          2: apply sscoping_comp_one.
          eapply ext_cterm_scoped. 1:{ apply param_scoping. eassumption. }
          intros [| []] hx. all: cbn.
          + discriminate.
          + reflexivity.
          + apply psubst_SS_id. assumption.
      }
  - unfold ptype in *. cbn in *.
    remd. remd in IHh.
    cbn in *. assumption.
  - unfold ptype in *. cbn in *.
    remd. remd in IHh1. remd in IHh2.
    cbn in *. rewrite rpm_lift_eq. rewrite <- epm_lift_eq. assumption.
  - (* Preprocessing hypotheses *)
    unfold ptype in IHh4. remd in IHh4. cbn in IHh4.
    eapply param_pType in IHh4. 2,3: eauto.
    unfold ptype in IHh2. cbn in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh1. cbn in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh3. cbn in IHh3.
    erewrite md_ren in IHh3.
    2: eapply rscoping_S.
    2: eapply rscoping_comp_S.
    remd in IHh3.
    (* End *)
    unfold ptype. cbn. remd.
    cbn in H3.
    destruct m. all: try intuition discriminate.
    + cbn in *.
      (* Preprocessing hypotheses *)
      eapply ctype_conv in IHh2.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. econstructor.
        - lhs_ssimpl. econv.
        - lhs_ssimpl. econstructor.
          1:{ rewrite <- rinstInst'_cterm. econv. }
          eapply cconv_trans. 1: constructor.
          cbn. econstructor. 2: econv.
          instantiate (1 := (S >> S) ⋅ ⟦ sc Γ | P ⟧pτ).
          apply ccmeta_refl. reflexivity.
      }
      2:{
        etype.
        - eapply ccmeta_conv.
          + etype. eapply ccmeta_conv.
            * eapply ctyping_ren. 1: apply crtyping_S.
              etype.
            * cbn. reflexivity.
          + cbn. reflexivity.
        - eapply ccmeta_conv.
          + eapply ctyping_ren. 1: etype.
            rewrite param_erase_ty_tm. etype.
            econstructor.
            * etype.
            * cbn. rewrite epm_lift_eq. cbn.
              eapply cconv_trans. 1: constructor.
              constructor.
            * etype.
          + reflexivity.
      }
      eapply ctype_conv in IHh3.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. econstructor.
        - lhs_ssimpl. econv.
        - lhs_ssimpl. econstructor.
          + rewrite <- rinstInst'_cterm. econv.
          + econstructor. 2: econv.
            econstructor. 2: econv.
            econstructor. all: apply ccmeta_refl.
            * hide_rhs rhs. erewrite param_ren.
              2: apply rscoping_S.
              2: apply rscoping_comp_S.
              rasimpl. rewrite pren_S_pw. rasimpl.
              unfold rhs. reflexivity.
            * hide_rhs rhs.
              rewrite rpm_lift_eq. cbn.
              unfold rhs. reflexivity.
      }
      2:{
        etype.
        - eapply ccmeta_conv.
          + etype. eapply ccmeta_conv.
            * eapply ctyping_ren. 1: apply crtyping_S.
              etype.
            * cbn. reflexivity.
          + cbn. reflexivity.
        - eapply ccmeta_conv.
          + etype.
            2:{
              econstructor.
              - eapply ctyping_ren. 1: etype.
                etype.
              - cbn.
                erewrite md_ren. 2: apply rscoping_S. 2: apply rscoping_comp_S.
                remd. cbn.
                change (epm_lift (cEl ?t)) with (vreg ⋅ (cEl t)). cbn.
                eapply cconv_trans. 1: constructor.
                econv.
              - cbn. etype.
                + eapply ccmeta_conv.
                  * eapply ctyping_ren. 1: etype.
                    etype.
                  * cbn. reflexivity.
                + rasimpl.
                  erewrite erase_ren.
                  2: apply rscoping_S. 2: apply rscoping_comp_S.
                  rasimpl.
                  econstructor.
                  * eapply ctyping_ren.
                    1:{
                      eapply crtyping_comp. 1: etype.
                      apply typing_er_sub_param.
                    }
                    etype.
                  * cbn. eapply cconv_trans. 1: constructor.
                    constructor.
                  * etype.
            }
            {
              eapply ccmeta_conv.
              - etype. eapply ccmeta_conv.
                + etype. eapply ccmeta_conv.
                  * eapply ctyping_ren. 1: etype.
                    etype.
                  * cbn. reflexivity.
                + cbn. f_equal. rasimpl. reflexivity.
              - cbn. f_equal. rasimpl.
                rewrite param_erase_ty_tm. cbn.
                erewrite erase_ren.
                2: apply rscoping_S. 2: apply rscoping_comp_S.
                rasimpl. rewrite epm_lift_eq. rasimpl. reflexivity.
            }
          + cbn. reflexivity.
      }
      (* End *)
      eapply ccmeta_conv.
      * {
        etype. eapply ccmeta_conv.
        - etype. eapply ccmeta_conv.
          + etype.
          + reflexivity.
        - cbn. f_equal. rasimpl. reflexivity.
      }
      * cbn. rasimpl. reflexivity.
    + cbn in *.
      (* Preprocessing hypotheses *)
      eapply ctype_conv in IHh2.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. econstructor.
        - lhs_ssimpl. econv.
        - lhs_ssimpl. econstructor.
          1:{ rewrite <- rinstInst'_cterm. econv. }
          eapply cconv_trans. 1: constructor.
          cbn. econv.
      }
      2:{
        etype.
        eapply ccmeta_conv.
        - etype. eapply ccmeta_conv.
          + eapply ctyping_ren. 1: apply crtyping_S.
            etype.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
      unfold pPi in IHh3.
      eapply ccmeta_conv in IHh3.
      2:{
        erewrite param_ren.
        2: apply rscoping_S.
        2: apply rscoping_comp_S.
        lhs_ssimpl. rewrite pren_S_pw.
        change (rpm_lift (cvar 0)) with (vreg ⋅ (cvar 0)).
        cbn. reflexivity.
      }
      (* End *)
      eapply ccmeta_conv.
      * {
        etype.
        eapply ccmeta_conv.
        - etype. eapply ccmeta_conv.
          + etype.
          + reflexivity.
        - cbn. f_equal. rasimpl. reflexivity.
      }
      * cbn. rasimpl. reflexivity.
  - unfold ptype. cbn.
    remd. cbn. change (epm_lift ctt) with ctt.
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    econstructor.
    + etype. eapply ccmeta_conv.
      * {
        etype. econstructor.
        - etype.
        - eapply cconv_trans. 1: constructor.
          cbn. econv. rasimpl. econv.
        - etype.
          + cbn. etype.
          + eapply ccmeta_conv.
            * {
              etype.
              econstructor.
              - eapply ctyping_subst.
                1:{
                  eapply cstyping_shift_eq with (A := S ⋅ ⟦ sc Γ | Erased A ⟧pτ).
                  - eapply cstyping_one.
                    + escope.
                    + etype.
                  - f_equal. f_equal. f_equal. rasimpl. reflexivity.
                }
                eapply ctyping_ren. 1: eapply crtyping_S.
                eapply ctyping_ren. 1: eapply crtyping_S.
                etype.
              - cbn. unfold ptype. remd. cbn.
                eapply cconv_trans. 1: constructor.
                cbn. econv. rewrite param_erase_ty_tm.
                rasimpl. rewrite rinstInst'_cterm. econv.
              - etype. eapply ccmeta_conv.
                + eapply ctyping_ren. 1: eapply crtyping_S.
                  cbn. etype.
                + cbn. reflexivity.
            }
            * cbn. reflexivity.
          + eapply ccmeta_conv.
            * {
              etype. econstructor.
              - etype.
                econstructor.
                + eapply ctyping_ren. 1: eapply crtyping_S.
                  eapply ctyping_ren. 1: eapply crtyping_S.
                  etype.
                + cbn. change (epm_lift (cEl ?A)) with (vreg ⋅ (cEl A)).
                  cbn. eapply cconv_trans. 1: constructor.
                  econv. rasimpl. econv.
                + etype. eapply ccmeta_conv.
                  * eapply ctyping_ren. 1: etype.
                    cbn. etype.
                  * cbn. reflexivity.
              - cbn. constructor.
              - etype.
            }
            * cbn. reflexivity.
      }
      * cbn. f_equal. rasimpl. reflexivity.
    + cbn. eapply cconv_trans. 1: constructor.
      cbn. apply cconv_sym. eapply cconv_trans. 1: constructor.
      cbn. econv.
    + eapply ccmeta_conv.
      * etype.
      * cbn. reflexivity.
  - unfold ptype in IHh3 |- *.
    cbn in *.
    remd. cbn.
    remd in IHh3. cbn in IHh3.
    assumption.
  - unfold ptype in IHh3 |- *.
    cbn in *.
    remd. cbn.
    remd in IHh3. cbn in IHh3.
    assumption.
  - unfold ptype. cbn.
    change (epm_lift ctt) with ctt.
    econstructor.
    + etype.
    + apply cconv_sym. constructor.
    + eapply ccmeta_conv.
      * etype.
      * cbn. reflexivity.
  - unfold ptype. cbn.
    etype.
  - unfold ptype. cbn.
    remd. cbn.
    (* Hyp preprocessing *)
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh3. remd in IHh3. cbn in IHh3.
    unfold ptype in IHh4. remd in IHh4. cbn in IHh4.
    unfold ptype in IHh5. remd in IHh5. cbn in IHh5.
    unfold ptype in IHh6. remd in IHh6.
    eapply ctype_conv in IHh1.
    2:{
      unfold pType. eapply cconv_trans. 1: constructor.
      cbn. econstructor. 2: econv.
      rewrite <- param_erase_ty_tm. econv.
    }
    2: etype.
    (* END *)
    destruct m. 1: contradiction.
    + (* Preprocessing *)
      cbn in IHh5.
      eapply ctype_conv in IHh5.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. lhs_ssimpl. rewrite <- rinstInst'_cterm.
        econstructor. 1: econv.
        econstructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        cbn. econv.
      }
      2:{
        etype.
        - eapply ccmeta_conv.
          + etype. eapply ccmeta_conv.
            * eapply ctyping_ren. all: etype.
            * cbn. lhs_ssimpl. reflexivity.
          + cbn. reflexivity.
        - econstructor.
          + eapply ctyping_ren. all: etype.
          + cbn. change (epm_lift (cEl ?t)) with (vreg ⋅ (cEl t)).
            cbn. eapply cconv_trans. 1: constructor.
            constructor.
          + etype.
      }
      cbn in IHh6. remd in IHh6. cbn in IHh6.
      (* End *)
      cbn.
      eapply type_pcastTG. all: eauto. all: etype.
      * {
        econstructor.
        - etype.
        - cbn. rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
          constructor.
        - etype.
      }
      * eapply ccmeta_conv. 1: etype.
        cbn. remd. cbn. reflexivity.
      * eapply param_scoping in H1. cbn in H1.
        rewrite csc_param_ctx. assumption.
    + (* Preprocessing *)
      cbn in IHh5.
      eapply ctype_conv in IHh5.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. lhs_ssimpl. rewrite <- rinstInst'_cterm.
        econstructor. 1: econv.
        econstructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        cbn. econstructor. 2: econv.
        apply ccmeta_refl.
        reflexivity.
      }
      2:{
        etype.
        - eapply ccmeta_conv.
          + etype. eapply ccmeta_conv.
            * eapply ctyping_ren. all: etype.
            * cbn. lhs_ssimpl. reflexivity.
          + cbn. reflexivity.
        - econstructor.
          + eapply ctyping_ren. all: etype.
          + cbn. change (epm_lift (cEl ?t)) with (vreg ⋅ (cEl t)).
            cbn. eapply cconv_trans. 1: constructor.
            constructor.
          + etype.
      }
      cbn in IHh6. remd in IHh6. cbn in IHh6.
      (* End *)
      cbn.
      eapply type_pcastTG. all: eauto. all: etype.
      * {
        econstructor.
        - etype.
        - cbn. rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
          constructor.
        - etype.
      }
      * eapply ccmeta_conv. 1: etype.
        cbn. remd. cbn. reflexivity.
      * eapply param_scoping in H1. cbn in H1.
        rewrite csc_param_ctx. assumption.
    + (* Preprocessing *)
      cbn in IHh6. remd in IHh6. cbn in IHh6.
      cbn in IHh5.
      eapply ctype_conv in IHh5.
      2:{
        eapply cconv_trans. 1: constructor.
        cbn. lhs_ssimpl. rewrite <- rinstInst'_cterm.
        econstructor. 1: econv.
        econstructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        cbn. econv.
      }
      2:{
        etype. eapply ccmeta_conv.
        - etype. eapply ccmeta_conv.
          + eapply ctyping_ren. 1: apply crtyping_S.
            etype.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
      (* End *)
      cbn. unfold pcastP. cbn. rasimpl.
      change (λ m, S (S (S m))) with (S >> S >> S). rasimpl.
      econstructor.
      * {
        etype.
        - cbn. eapply ccmeta_conv.
          + etype.
            * {
              eapply ccmeta_conv.
              - etype.
                + eapply ccmeta_conv.
                  * eapply ctyping_ren. 1: apply crtyping_S.
                    etype.
                  * cbn. rasimpl. reflexivity.
                + eapply ctyping_ren. 1: apply crtyping_S.
                  etype.
              - cbn. rasimpl. reflexivity.
            }
            * {
              eapply ccmeta_conv.
              - eapply ctyping_ren. 1: apply crtyping_S.
                etype.
              - cbn. rasimpl. reflexivity.
            }
          + cbn. reflexivity.
        - econstructor.
          + etype.
            * {
              econstructor.
              - etype.
                + eapply ccmeta_conv.
                  * etype.
                  * cbn. rasimpl. reflexivity.
                + eapply ccmeta_conv.
                  * eapply ctyping_ren. 1: apply crtyping_S.
                    etype.
                  * cbn. reflexivity.
                + eapply ccmeta_conv.
                  * {
                    etype.
                    - eapply ccmeta_conv.
                      + eapply ctyping_ren. 1: etype.
                        etype.
                      + cbn. reflexivity.
                    - eapply ctyping_ren. 1: etype.
                      etype.
                    - eapply ccmeta_conv.
                      + etype.
                      + cbn. rasimpl. reflexivity.
                    - eapply ccmeta_conv.
                      + etype. eapply ccmeta_conv.
                        * eapply ctyping_ren. 1: etype.
                          etype.
                        * cbn. f_equal. rasimpl. reflexivity.
                      + cbn. reflexivity.
                    - eapply ccmeta_conv.
                      + etype. eapply ccmeta_conv.
                        * {
                          etype. eapply ccmeta_conv.
                          - eapply ctyping_ren. 1: etype.
                            etype.
                          - cbn. f_equal. rasimpl. reflexivity.
                        }
                        * cbn. f_equal. rasimpl. reflexivity.
                      + cbn. reflexivity.
                  }
                  * cbn. f_equal. rasimpl. reflexivity.
                + econstructor.
                  * {
                    etype.
                    - eapply ccmeta_conv.
                      + etype.
                        * {
                          eapply ccmeta_conv.
                          - eapply ctyping_ren. 1: etype.
                            etype.
                          - cbn. reflexivity.
                        }
                        * eapply ctyping_ren. 1: etype.
                          etype.
                      + cbn. reflexivity.
                    - eapply ctyping_ren. 1: etype.
                      etype.
                  }
                  * cbn. apply cconv_sym. eapply cconv_trans.
                    1:{
                      econstructor. 2: econv.
                      constructor.
                    }
                    cbn. eapply cconv_trans. 1: constructor.
                    cbn. rasimpl.
                    rewrite !rinstInst'_cterm.
                    econv.
                    apply cconv_irr.
                    -- escope. reflexivity.
                    --
                      rewrite <- !rinstInst'_cterm. cbn.
                      eapply cscoping_ren.
                      1:{
                        eapply crscoping_comp. all: apply crscoping_S.
                      }
                      eapply param_scoping in H1. cbn in H1.
                      rewrite csc_param_ctx. assumption.
                  * {
                    eapply ccmeta_conv.
                    - etype.
                      + eapply ccmeta_conv.
                        * {
                          etype.
                          - eapply ccmeta_conv.
                            + eapply ctyping_ren. all: etype.
                            + cbn. reflexivity.
                          - eapply ccmeta_conv.
                            + eapply ctyping_ren. all: etype.
                            + cbn. reflexivity.
                          - eapply ctyping_ren. all: etype.
                          - eapply ccmeta_conv.
                            + etype.
                            + cbn. rasimpl. reflexivity.
                          - eapply ccmeta_conv.
                            + etype.
                              eapply ccmeta_conv.
                              * eapply ctyping_ren. all: etype.
                              * cbn. f_equal. rasimpl. reflexivity.
                            + cbn. reflexivity.
                          - eapply ccmeta_conv.
                            + etype.
                              eapply ccmeta_conv.
                              * etype.
                                eapply ccmeta_conv.
                                -- eapply ctyping_ren. all: etype.
                                -- cbn. f_equal. rasimpl. reflexivity.
                              * cbn. f_equal. rasimpl.
                                rewrite rinstInst'_cterm. rasimpl. reflexivity.
                            + cbn. reflexivity.
                          - eapply ctyping_ren. all: etype.
                        }
                        * cbn. f_equal. rasimpl. reflexivity.
                      + eapply ccmeta_conv.
                        * eapply ctyping_ren. all: etype.
                        * cbn. reflexivity.
                      + eapply ctyping_ren. all: etype.
                    - cbn. reflexivity.
                  }
              - eapply cconv_trans.
                1:{
                  constructor. 2: econv.
                  constructor.
                }
                cbn. eapply cconv_trans. 1: constructor.
                rasimpl. econv.
              - etype.
                + eapply ccmeta_conv.
                  * {
                    etype.
                    - eapply ccmeta_conv.
                      + eapply ctyping_ren. all: etype.
                      + cbn. reflexivity.
                    - eapply ctyping_ren. all: etype.
                  }
                  * cbn. reflexivity.
                + eapply ccmeta_conv.
                  * {
                    etype. eapply ccmeta_conv.
                    - etype.
                      + eapply ccmeta_conv.
                        * eapply ctyping_ren. all: etype.
                        * cbn. rasimpl. reflexivity.
                      + eapply ctyping_ren. all: etype.
                    - cbn. f_equal. rasimpl. rewrite !rinstInst'_cterm.
                      reflexivity.
                  }
                  * cbn. reflexivity.
            }
            * {
              eapply ccmeta_conv.
              - eapply ctyping_ren. all: etype.
              - cbn. reflexivity.
            }
          + cbn. rasimpl. apply cconv_sym. eapply cconv_trans. 1: constructor.
            cbn. rasimpl. econv.
          + rasimpl. eapply ccmeta_conv.
            * {
              etype.
              - eapply ccmeta_conv.
                + eapply ctyping_ren. all: etype.
                + cbn. reflexivity.
              - eapply ctyping_ren. all: etype.
              - eapply ctyping_ren. all: etype.
              - eapply ccmeta_conv.
                + etype.
                  * {
                    eapply ccmeta_conv.
                    - eapply ctyping_ren. all: etype.
                    - cbn. rasimpl. reflexivity.
                  }
                  * eapply ctyping_ren. all: etype.
                + cbn. rasimpl. reflexivity.
              - eapply ccmeta_conv.
                + eapply ctyping_ren. all: etype.
                + cbn. reflexivity.
              - eapply ccmeta_conv.
                + etype.
                + cbn. reflexivity.
              - eapply ccmeta_conv.
                + eapply ctyping_ren. all: etype.
                + cbn. reflexivity.
              - eapply ctyping_ren. all: etype.
              - eapply ctyping_ren. all: etype.
            }
            * cbn. reflexivity.
      }
      * eapply cconv_trans. 1: constructor.
        cbn. rasimpl. econv.
      * {
        eapply ccmeta_conv.
        - etype.
          eapply ccmeta_conv.
          + etype.
          + cbn. rasimpl. reflexivity.
        - cbn. reflexivity.
      }
  - cbn. change (epm_lift ?t) with t.
    econstructor.
    + ertype.
    + cbn. apply cconv_sym. unfold pType. eapply cconv_trans. 1: constructor.
      cbn. econv.
    + eapply ccmeta_conv.
      * ertype.
      * reflexivity.
  - cbn. change (epm_lift ?t) with t. ertype.
  - cbn. change (epm_lift ?t) with t. ertype.
  - unfold ptype. cbn. remd.
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh3. remd in IHh3. cbn in IHh3.
    unfold ptype in IHh4. remd in IHh4. cbn in IHh4.
    set (rm := relm m) in *. simpl. simpl in IHh3. simpl in IHh4.
    eapply ctype_conv in IHh2.
    2:{
      unfold pmPiNP. eapply cconv_trans. 1: constructor.
      cbn. rasimpl. econstructor.
      - rewrite epm_lift_eq. cbn. constructor.
      - econstructor. 1: econv.
        instantiate (1 := if isProp m then _ else cPi _ _ (if isKind m then _ else _)).
        destruct (isKind m) eqn:ek. 2: destruct (isProp m) eqn:ep.
        + mode_eqs. cbn.
          cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
        + cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
        + cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
    }
    2:{
      ertype.
      - eapply ccmeta_conv.
        + ertype. eapply ccmeta_conv. 1: ertype.
          reflexivity.
        + cbn. reflexivity.
      - instantiate (2 := if isProp m then _ else _).
        instantiate (1 := if isProp m then _ else _).
        destruct (isProp m) eqn:ep.
        + ertype.
        + ertype.
          * {
            eapply ccmeta_conv.
            - ertype. econstructor.
              + ertype.
              + cbn. change (epm_lift ?t) with (vreg ⋅ t). cbn.
                eapply cconv_trans. 1: constructor.
                econstructor. 1: econv.
                rewrite ep. cbn. constructor.
              + cbn. ertype.
            - cbn. reflexivity.
          }
          * instantiate (1 := if isKind m then _ else _).
            destruct (isKind m). all: ertype.
    }
    change (epm_lift etrue) with etrue in IHh3.
    change (epm_lift efalse) with efalse in IHh4.
    eapply param_erase_typing in h1 as hbe. 2: ertype.
    cbn in hbe. eapply ctype_conv in hbe.
    2:{
      rewrite epm_lift_eq. cbn. constructor.
    }
    2:{ ertype. }
    eapply param_erase_typing in h2 as hPe. 2: ertype.
    cbn in hPe. eapply ctype_conv in hPe.
    2:{
      rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
      constructor.
      - constructor.
      - instantiate (1 := if isProp m then _ else _).
        destruct_if e.
        + cbn. constructor.
        + cbn. constructor.
    }
    2:{
      ertype. instantiate (1 := if isProp m then _ else _). destruct_if e.
      - ertype.
      - ertype.
    }
    subst rm. destruct m.
    + cbn in *.
      eapply param_erase_typing in h3 as hte. 2: ertype.
      cbn in hte. remd in hte. cbn in hte.
      eapply ccmeta_conv in hte.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply param_erase_typing in h4 as hfe. 2: ertype.
      cbn in hfe. remd in hfe. cbn in hfe.
      eapply ccmeta_conv in hfe.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply ccmeta_conv.
      * ertype.
        unfold pPi. cbn. rasimpl. assumption.
      * f_equal. unfold perif. change (epm_lift ?t) with (vreg ⋅ t).
        cbn. f_equal. f_equal. f_equal. f_equal. rasimpl. reflexivity.
    + cbn in *.
      eapply param_erase_typing in h3 as hte. 2: ertype.
      cbn in hte. remd in hte. cbn in hte.
      eapply ccmeta_conv in hte.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply param_erase_typing in h4 as hfe. 2: ertype.
      cbn in hfe. remd in hfe. cbn in hfe.
      eapply ccmeta_conv in hfe.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply ccmeta_conv.
      * ertype.
        unfold pPi. cbn. rasimpl. assumption.
      * f_equal. unfold perif. change (epm_lift ?t) with (vreg ⋅ t).
        cbn. f_equal. f_equal. f_equal. f_equal. rasimpl. reflexivity.
    + cbn in *.
      eapply param_revive_typing in h3 as hte. 2: ertype.
      cbn in hte. remd in hte. cbn in hte.
      eapply ccmeta_conv in hte.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply param_revive_typing in h4 as hfe. 2: ertype.
      cbn in hfe. remd in hfe. cbn in hfe.
      eapply ccmeta_conv in hfe.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply ccmeta_conv.
      * ertype.
        unfold pPi. cbn. rasimpl. assumption.
      * f_equal. unfold perif. change (rpm_lift ?t) with (vreg ⋅ t).
        change (epm_lift ?t) with (vreg ⋅ t).
        cbn. f_equal. f_equal. f_equal. f_equal. rasimpl. reflexivity.
    + cbn in *. ertype.
  - cbn. rewrite epm_lift_eq. cbn.
    econstructor.
    + ertype.
    + apply cconv_sym. unfold pType. constructor.
    + eapply ccmeta_conv.
      * ertype.
      * reflexivity.
  - cbn. rewrite epm_lift_eq. cbn.
    ertype.
  - cbn. rewrite epm_lift_eq. cbn. change (vreg ⋅ ?t) with (epm_lift t).
    unfold ptype in IHh. remd in IHh. cbn in IHh.
    ertype.
  - unfold ptype. cbn. remd.
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh3. remd in IHh3. cbn in IHh3.
    unfold ptype in IHh4. remd in IHh4.
    set (rm := relm m) in *. simpl. simpl in IHh3.
    eapply ctype_conv in IHh2.
    2:{
      unfold pmPiNP. eapply cconv_trans. 1: constructor.
      cbn. lhs_ssimpl. econstructor.
      - rewrite epm_lift_eq. cbn. econv.
      - econstructor. 1: econv.
        instantiate (1 := if isProp m then _ else cPi _ _ (if isKind m then _ else _)).
        destruct (isKind m) eqn:ek. 2: destruct (isProp m) eqn:ep.
        + mode_eqs. cbn.
          eapply cconv_trans. 1: constructor.
          cbn. econv.
        + cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
        + cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
    }
    2:{
      ertype.
      - eapply ccmeta_conv.
        + ertype. eapply ccmeta_conv. 1: ertype.
          reflexivity.
        + cbn. reflexivity.
      - instantiate (2 := if isProp m then _ else _).
        instantiate (1 := if isProp m then _ else _).
        destruct (isProp m) eqn:ep.
        + ertype.
        + ertype.
          * {
            eapply ccmeta_conv.
            - ertype. econstructor.
              + ertype.
              + cbn. change (epm_lift ?t) with (vreg ⋅ t). cbn.
                eapply cconv_trans. 1: constructor.
                econstructor. 1: econv.
                rewrite ep. cbn. constructor.
              + cbn. ertype.
            - cbn. reflexivity.
          }
          * instantiate (1 := if isKind m then _ else _).
            destruct (isKind m). all: ertype.
    }
    change (epm_lift ezero) with ezero in IHh3.
    eapply param_erase_typing in h1 as hbe. 2: ertype.
    cbn in hbe. change (epm_lift (cEl ?t)) with (cEl t) in hbe.
    eapply param_erase_typing in h2 as hPe. 2: ertype.
    cbn in hPe. eapply ctype_conv in hPe.
    2:{
      rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
      constructor.
      - econv.
      - instantiate (1 := if isProp m then _ else _).
        destruct_if e.
        + cbn. constructor.
        + cbn. constructor.
    }
    2:{
      ertype. instantiate (1 := if isProp m then _ else _). destruct_if e.
      - ertype.
      - ertype.
    }
    subst rm. destruct m.
    + contradiction.
    + change (relm mType) with true in IHh4. cbn iota in IHh4.
      cbn in IHh4.
      erewrite !md_ren in IHh4. 2-7: eauto using rscoping_S, rscoping_comp_S.
      remd in IHh4.
      cbn in *.
      eapply ctype_conv in IHh4.
      2:{
        clear.
        unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
        cbn. constructor.
        1:{ lhs_ssimpl. rewrite epm_lift_eq. cbn. econv. }
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        cbn. constructor.
        1:{
          lhs_ssimpl. change (epm_lift ?t) with (vreg ⋅ t).
          cbn. erewrite erase_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. constructor. constructor. 2: econv.
          apply ccmeta_refl. etransitivity.
          - eapply ext_cterm_scoped with (θ := vreg >> S >> S >> cvar).
            1: apply erase_scoping.
            clear. intros [|] hx.
            + ssimpl. unfold vreg. cbn. ssimpl. reflexivity.
            + ssimpl. change (vreg (S ?x)) with (S (S (vreg x))).
              change (vreg (S ?x)) with (S (S (vreg x))).
              cbn. reflexivity.
          - rewrite <- rinstInst'_cterm.
            rewrite <- renRen_cterm. rewrite <- renRen_cterm.
            rewrite <- epm_lift_eq. lhs_ssimpl. reflexivity.
        }
        constructor.
        1:{
          lhs_ssimpl'. change (epm_lift (cvar 0)) with (cvar 1).
          erewrite param_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl'. constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          apply ccmeta_refl. rewrite pren_S_pw. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        }
        constructor. 2: econv.
        constructor. 2: econv.
        constructor.
        - erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
          rewrite !pren_S_pw. apply ccmeta_refl.
          lhs_ssimpl. rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        - apply ccmeta_refl.
          change (epm_lift ?t) with (vreg ⋅ t). cbn.
          reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype.
                + cbn. rasimpl. reflexivity.
              - cbn. reflexivity.
            }
            * cbn. rasimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            2:{
              eapply ccmeta_conv.
              - ertype. econstructor.
                + ertype.
                + cbn. erewrite !md_ren.
                  2-7: eauto using rscoping_S, rscoping_comp_S.
                  remd. cbn. change (epm_lift ?t) with (vreg ⋅ t).
                  cbn. eapply cconv_trans. 1: constructor.
                  constructor. 1: econv.
                  eapply cconv_trans. 1: constructor.
                  constructor.
                  * apply ccmeta_refl.
                    erewrite erase_ren.
                    2,3: eauto using rscoping_S, rscoping_comp_S.
                    lhs_ssimpl. rewrite <- renRen_cterm.
                    rewrite <- epm_lift_eq. reflexivity.
                  * apply ccmeta_refl.
                    erewrite !erase_ren.
                    2-5: eauto using rscoping_S, rscoping_comp_S.
                    lhs_ssimpl. rewrite <- renRen_cterm.
                    rewrite <- epm_lift_eq. reflexivity.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv.
                      + ertype.
                      + cbn. reflexivity.
                    - reflexivity.
                  }
                  * {
                    eapply ccmeta_conv.
                    - ertype.
                      + eapply ccmeta_conv.
                        * ertype.
                        * cbn. reflexivity.
                      + eapply ccmeta_conv.
                        * ertype.
                        * cbn. reflexivity.
                    - reflexivity.
                  }
              - cbn. f_equal. ssimpl. rewrite <- !funcomp_assoc.
                rewrite <- rinstInst'_cterm. reflexivity.
            }
            cbn. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - ertype.
                    - cbn. lhs_ssimpl. reflexivity.
                  }
                  * eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                + cbn. lhs_ssimpl. rewrite <- !funcomp_assoc.
                  rewrite <- rinstInst'_cterm. reflexivity.
              - eapply ccmeta_conv.
                + ertype.
                + reflexivity.
            }
            * cbn. f_equal. rasimpl. reflexivity.
          + cbn. reflexivity.
      }
      eapply param_erase_typing in h3 as hze. 2: ertype.
      cbn in hze. remd in hze. cbn in hze.
      eapply ccmeta_conv in hze.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply param_erase_typing in h4 as hse. 2: ertype.
      cbn in hse.
      erewrite !md_ren in hse. 2-7: eauto using rscoping_S, rscoping_comp_S.
      remd in hse. cbn in hse.
      eapply ctype_conv in hse.
      2:{
        rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        apply cconv_sym. apply ccong_Pi.
        1:{
          apply cconv_sym. erewrite erase_ren.
          2-3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- renRen_cterm. rewrite <- epm_lift_eq.
          econv.
        }
        apply cconv_sym. constructor. constructor.
        2:{ lhs_ssimpl. econv. }
        apply ccmeta_refl.
        erewrite !erase_ren.
          2-5: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- renRen_cterm. rewrite <- epm_lift_eq.
          reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
          + reflexivity.
      }
      eapply ccmeta_conv.
      * ertype. eapply ccmeta_conv. 1: eassumption.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        f_equal. rasimpl. reflexivity.
      * reflexivity.
    + change (relm mGhost) with false in IHh4. cbn iota in IHh4.
      change (isGhost mGhost) with true in IHh4. cbn iota in IHh4.
      cbn in IHh4.
      erewrite !md_ren in IHh4. 2-7: eauto using rscoping_S, rscoping_comp_S.
      remd in IHh4.
      cbn in *.
      eapply ctype_conv in IHh4.
      2:{
        clear.
        unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
        cbn. apply cconv_sym. apply ccong_Pi.
        1:{ apply cconv_sym. lhs_ssimpl. rewrite epm_lift_eq. cbn. econv. }
        apply ccong_Pi. 1: econv.
        apply cconv_sym.
        eapply cconv_trans. 1: constructor.
        cbn. apply cconv_sym. apply ccong_Pi.
        1:{
          apply cconv_sym.
          lhs_ssimpl. change (epm_lift ?t) with (vreg ⋅ t).
          cbn. erewrite erase_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. constructor. constructor. 2: econv.
          apply ccmeta_refl. etransitivity.
          - eapply ext_cterm_scoped with (θ := vreg >> S >> S >> cvar).
            1: apply erase_scoping.
            clear. intros [|] hx.
            + ssimpl. unfold vreg. cbn. ssimpl. reflexivity.
            + ssimpl. change (vreg (S ?x)) with (S (S (vreg x))).
              change (vreg (S ?x)) with (S (S (vreg x))).
              cbn. reflexivity.
          - rewrite <- rinstInst'_cterm.
            rewrite <- renRen_cterm. rewrite <- renRen_cterm.
            rewrite <- epm_lift_eq. lhs_ssimpl. reflexivity.
        }
        apply ccong_Pi.
        1:{
          apply cconv_sym.
          lhs_ssimpl'. change (epm_lift (cvar 0)) with (cvar 1).
          erewrite param_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl'. rewrite pren_S_pw. constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        }
        apply cconv_sym.
        constructor. 2:{ lhs_ssimpl. econv. }
        constructor. 2: econv.
        constructor.
        - erewrite !param_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
          rewrite !pren_S_pw. apply ccmeta_refl.
          lhs_ssimpl. rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        - apply ccmeta_refl.
          change (epm_lift ?t) with (vreg ⋅ t). cbn.
          reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype.
                + cbn. lhs_ssimpl. reflexivity.
              - cbn. reflexivity.
            }
            * cbn. lhs_ssimpl. f_equal.
              ssimpl. rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
              reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            2:{
              eapply ccmeta_conv.
              - ertype. econstructor.
                + ertype.
                + cbn. erewrite !md_ren.
                  2-7: eauto using rscoping_S, rscoping_comp_S.
                  remd. cbn. change (epm_lift ?t) with (vreg ⋅ t).
                  cbn. eapply cconv_trans. 1: constructor.
                  constructor. 1: econv.
                  eapply cconv_trans. 1: constructor.
                  constructor.
                  * apply ccmeta_refl.
                    erewrite erase_ren.
                    2,3: eauto using rscoping_S, rscoping_comp_S.
                    lhs_ssimpl. rewrite <- renRen_cterm.
                    rewrite <- epm_lift_eq. reflexivity.
                  * apply ccmeta_refl.
                    erewrite !erase_ren.
                    2-5: eauto using rscoping_S, rscoping_comp_S.
                    lhs_ssimpl. rewrite <- !funcomp_assoc.
                    rewrite <- rinstInst'_cterm. rewrite !funcomp_assoc.
                    rewrite <- renRen_cterm.
                    rewrite <- epm_lift_eq. reflexivity.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - ertype. eapply ccmeta_conv.
                      + ertype.
                      + cbn. reflexivity.
                    - reflexivity.
                  }
                  * {
                    eapply ccmeta_conv.
                    - ertype.
                      + eapply ccmeta_conv.
                        * ertype.
                        * cbn. reflexivity.
                      + eapply ccmeta_conv.
                        * ertype.
                        * cbn. reflexivity.
                    - reflexivity.
                  }
              - cbn. f_equal. ssimpl. rewrite <- !funcomp_assoc.
                rewrite <- rinstInst'_cterm. reflexivity.
            }
            cbn. eapply ccmeta_conv.
            * {
              ertype.
              - eapply ccmeta_conv.
                + ertype.
                  * {
                    eapply ccmeta_conv.
                    - ertype.
                    - cbn. lhs_ssimpl. reflexivity.
                  }
                  * eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                + cbn. lhs_ssimpl. rewrite <- !funcomp_assoc.
                  rewrite <- rinstInst'_cterm. reflexivity.
              - eapply ccmeta_conv.
                + ertype.
                + reflexivity.
            }
            * cbn. f_equal. ssimpl. reflexivity.
          + cbn. reflexivity.
      }
      eapply param_revive_typing in h3 as hze. 2: ertype.
      cbn in hze. remd in hze. cbn in hze.
      eapply ccmeta_conv in hze.
      2:{
        rewrite epm_lift_eq. cbn. rewrite <- epm_lift_eq. reflexivity.
      }
      eapply param_revive_typing in h4 as hse. 2: ertype.
      cbn in hse.
      erewrite !md_ren in hse. 2-7: eauto using rscoping_S, rscoping_comp_S.
      remd in hse. cbn in hse.
      eapply ctype_conv in hse.
      2:{
        rewrite epm_lift_eq. cbn. eapply cconv_trans. 1: constructor.
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        apply cconv_sym. apply ccong_Pi.
        1:{
          apply cconv_sym. erewrite erase_ren.
          2-3: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- renRen_cterm. rewrite <- epm_lift_eq.
          econv.
        }
        apply cconv_sym. constructor. constructor.
        2:{ lhs_ssimpl. econv. }
        apply ccmeta_refl.
        erewrite !erase_ren.
          2-5: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          rewrite !funcomp_assoc.
          rewrite <- renRen_cterm. rewrite <- epm_lift_eq.
          reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
          + reflexivity.
      }
      eapply ccmeta_conv.
      * ertype.
      * reflexivity.
    + cbn in *.
      eapply ctype_conv in IHh4.
      2:{
        unfold pPi. constructor.
        1:{ rewrite epm_lift_eq. cbn. econv. }
        constructor. 1:{ cbn. econv. }
        cbn. constructor.
        1:{
          change (epm_lift (cvar 0)) with (cvar 1).
          erewrite param_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
          rewrite pren_S_pw. econv.
        }
        constructor. 2: econv.
        constructor.
        - apply ccmeta_refl.
          erewrite !param_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite !pren_S_pw. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        - apply ccmeta_refl. rewrite epm_lift_eq. cbn. reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * ertype. eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * {
              eapply ccmeta_conv.
              - ertype.
                + eapply ccmeta_conv.
                  * ertype.
                  * cbn. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - reflexivity.
            }
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
          + reflexivity.
      }
      ertype.
  - unfold ptype. cbn.
    change (epm_lift ?t) with (vreg ⋅ t). cbn.
    change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    eapply param_pType in IHh1. 2,3: assumption.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    eapply param_erase_typing in h1 as hAe. 2: ertype.
    cbn in hAe.
    eapply ctype_conv in hAe.
    2:{
      rewrite epm_lift_eq. cbn. constructor.
    }
    2: ertype.
    eapply param_revive_typing in h2 as hne. 2: ertype.
    cbn in hne.
    eapply ccmeta_conv in hne.
    2:{
      rewrite epm_lift_eq. cbn. reflexivity.
    }
    econstructor.
    + ertype. assumption.
    + apply cconv_sym. unfold pType. eapply cconv_trans. 1: constructor.
      cbn. econv.
    + eapply ccmeta_conv.
      * ertype.
      * reflexivity.
  - unfold ptype. cbn. change (rpm_lift ?t) with t.
    change (epm_lift ?t) with (vreg ⋅ t). cbn.
    change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
    unfold ptype in IHh. remd in IHh. cbn in IHh.
    eapply param_pType in IHh. 2,3: assumption.
    eapply param_erase_typing in h as hAe. 2: ertype.
    cbn in hAe.
    eapply ctype_conv in hAe.
    2:{
      rewrite epm_lift_eq. cbn. constructor.
    }
    2: ertype.
    ertype.
    assumption.
  - unfold ptype. cbn.
    change (epm_lift ?t) with (vreg ⋅ t). cbn.
    change (rpm_lift ?t) with (vreg ⋅ t). cbn.
    change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
    change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    unfold ptype in IHh3. remd in IHh3. cbn in IHh3.
    unfold ptype in IHh4. remd in IHh4. cbn in IHh4.
    eapply param_pType in IHh4. 2,3: assumption.
    eapply param_erase_typing in h4 as hAe. 2: ertype.
    cbn in hAe.
    eapply ctype_conv in hAe.
    2:{
      rewrite epm_lift_eq. cbn. constructor.
    }
    2: ertype.
    eapply param_erase_typing in h1 as hae. 2: ertype.
    eapply param_revive_typing in h2 as hne. 2: ertype.
    cbn in hne.
    eapply ccmeta_conv in hne.
    2:{
      rewrite epm_lift_eq. cbn. reflexivity.
    }
    eapply param_erase_typing in h3 as hve. 2: ertype.
    cbn in hve. change (epm_lift ?t) with (vreg ⋅ t) in hve. cbn in hve.
    change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε) in hve.
    econstructor.
    + ertype. all: assumption.
    + econv. all: apply cconv_sym. 1: econv.
      unfold plam. eapply cconv_trans.
      1:{ constructor. 2: econv. constructor. }
      cbn. econv.
    + eapply ccmeta_conv.
      * {
        ertype. 1,4: assumption.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - econstructor.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - reflexivity.
            }
            * cbn. reflexivity.
          + cbn. ssimpl. apply cconv_sym. econv.
          + eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - reflexivity.
            }
            * reflexivity.
      }
      * reflexivity.
  - unfold ptype. cbn. remd. cbn.
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh3. remd in IHh3.
    unfold ptype in IHh4. remd in IHh4.
    unfold ptype in IHh5. remd in IHh5. cbn in IHh5.
    unfold ptype in IHh6. remd in IHh6. cbn in IHh6.
    eapply param_pType in IHh6. 2,3: assumption.
    eapply param_erase_typing in h6 as hAe. 2: ertype.
    cbn in hAe.
    eapply ctype_conv in hAe.
    2:{
      rewrite epm_lift_eq. cbn. constructor.
    }
    2: ertype.
    eapply param_erase_typing in h2 as hPe. 2: ertype.
    cbn in hPe.
    eapply ctype_conv in hPe.
    2:{
      rewrite epm_lift_eq. cbn.
      eapply cconv_trans. 1: constructor.
      eapply cconv_trans. 1: constructor.
      constructor.
      1:{
        erewrite erase_ren. 2,3: eauto using rscoping_S, rscoping_comp_S.
        lhs_ssimpl. rewrite <- rinstInst'_cterm.
        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        econv.
      }
      instantiate (1 := if isProp m then _ else _).
      destruct_if e.
      - cbn. constructor.
      - cbn. constructor.
    }
    2:{
      ertype.
      instantiate (2 := if isProp m then _ else _).
      instantiate (1 := if isProp m then _ else _).
      destruct_if e. all: ertype.
    }
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    eapply ctype_conv in IHh2.
    2:{
      clear. unfold pmPiNP. cbn.
      change (epm_lift ?t) with (vreg ⋅ t). cbn.
      erewrite !erase_ren, !param_ren.
      2-5: eauto using rscoping_S, rscoping_comp_S.
      eapply cconv_trans. 1: constructor.
      cbn. constructor. 1: econv.
      constructor. 1: econv.
      eapply cconv_trans. 1: constructor.
      cbn. constructor.
      1:{
        constructor. constructor.
        apply ccmeta_refl.
        lhs_ssimpl.
        rewrite <- !funcomp_assoc.
        change (S >> vreg) with (vreg >> S >> S).
        rewrite !funcomp_assoc.
        rewrite <- renSubst_cterm.
        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        etransitivity.
        1:{
          eapply ext_cterm_scoped with (θ := S >> S >> cvar).
          1:{ eapply scoping_epm_lift. 2: reflexivity. eapply erase_scoping. }
          intros [| []] hx. all: reflexivity.
        }
        rewrite <- rinstInst'_cterm. reflexivity.
      }
      change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
      constructor.
      1:{
        constructor. 2: econv.
        constructor. all: apply ccmeta_refl.
        - lhs_ssimpl.
          rewrite <- !funcomp_assoc.
          change (S >> vreg) with (vreg >> S >> S).
          rewrite !funcomp_assoc.
          rewrite <- renSubst_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          etransitivity.
          1:{
            eapply ext_cterm_scoped with (θ := S >> S >> S >> cvar).
            1:{ eapply scoping_epm_lift. 2: reflexivity. eapply erase_scoping. }
            intros [| []] hx. all: reflexivity.
          }
          rewrite <- rinstInst'_cterm. reflexivity.
        - lhs_ssimpl. rewrite pren_S_pw. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        - lhs_ssimpl. rewrite rpm_lift_eq. cbn. reflexivity.
        - reflexivity.
      }
      instantiate (1 := if isKind m then _ else if isProp m then _ else _).
      destruct_ifs. all: mode_eqs.
      - cbn. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - cbn. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - cbn. eapply cconv_trans. 1: constructor.
        cbn. econv.
    }
    2:{
      ertype.
      - eapply ccmeta_conv.
        + ertype. eapply ccmeta_conv. 1: ertype.
          reflexivity.
        + reflexivity.
      - eapply ccmeta_conv.
        + ertype.
        + reflexivity.
      - eapply ccmeta_conv.
        + ertype.
          * eapply ccmeta_conv. 1: ertype.
            reflexivity.
          * eapply ccmeta_conv. 1: ertype.
            reflexivity.
          * eapply ccmeta_conv. 1: ertype.
            reflexivity.
          * eapply ccmeta_conv. 1: ertype.
            reflexivity.
          * eapply ccmeta_conv. 1: ertype.
            cbn. f_equal. rasimpl. reflexivity.
        + reflexivity.
      - instantiate (2 := if isKind m then _ else if isProp m then _ else _).
        instantiate (1 := if isKind m then _ else if isProp m then _ else _).
        destruct (isKind m) eqn:ekm. 2: destruct (isProp m) eqn:epm.
        all: mode_eqs. all: cbn.
        + ertype. eapply ccmeta_conv.
          * ertype. eapply ccmeta_conv. 1: ertype.
            cbn. f_equal. rasimpl. reflexivity.
          * reflexivity.
        + ertype.
        + ertype. eapply ccmeta_conv.
          * ertype. eapply ccmeta_conv. 1: ertype.
            cbn. f_equal. rasimpl. reflexivity.
          * reflexivity.
    }
    eapply param_revive_typing in h5 as hne. 2: ertype.
    cbn in hne. change (epm_lift ?t) with t in hne.
    eapply param_erase_typing in h1 as hve. 2: ertype.
    cbn in hve.
    eapply ccmeta_conv in hve.
    2:{
      change (epm_lift ?t) with (vreg ⋅ t). cbn.
      change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
      reflexivity.
    }
    destruct m.
    + contradiction.
    + simpl in IHh4. erewrite !md_ren in IHh4.
      2-15: eauto using rscoping_S, rscoping_comp_S.
      remd in IHh4. cbn in IHh4.
      eapply ctype_conv in IHh4.
      2:{
        clear. clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6 IHh1 IHh2 IHh3 IHh5.
        clear IHh6 hAe hPe.
        change (epm_lift ?t) with (vreg ⋅ t). unfold pmPiNP.
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          lhs_ssimpl. rewrite <- rinstInst'_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          econv.
        }
        lhs_hnf. constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl. rewrite <- !rinstInst'_cterm.
          reflexivity.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          eapply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          cbn. econv.
        }
        lhs_hnf. constructor.
        1:{
          cbn. econv.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          eapply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf.
        constructor.
        1:{
          cbn. constructor. constructor.
          lhs_hnf.
          lazymatch goal with
          | |- ?G ⊢ᶜ _ ≡ _ => remember G as C eqn:eC
          end.
          erewrite !erase_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- !funcomp_assoc.
          change ((S >> S) >> vreg) with (vreg >> S >> S >> S >> S).
          rewrite !funcomp_assoc. rewrite <- renSubst_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          econv.
        }
        lhs_hnf.
        constructor.
        1:{
          lhs_hnf. constructor.
          - lhs_hnf. constructor.
            + lhs_hnf. apply ccmeta_refl. cbn.
              erewrite !erase_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
              hide_rhs rhs. asimpl. autosubst_unfold. asimpl.
              repeat unfold_funcomp.
              rewrite ?renRen_cterm. rewrite <- !funcomp_assoc.
              change ((S >> S) >> vreg) with (vreg >> S >> S >> S >> S).
              rewrite !funcomp_assoc. rewrite <- !renRen_cterm.
              change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
              resubst. asimpl. repeat unfold_funcomp.
              ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
              subst rhs. reflexivity.
            + apply ccmeta_refl. cbn.
              change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
              erewrite !param_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
              rewrite !pren_S_pw.
              lhs_ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
              reflexivity.
            + apply ccmeta_refl. cbn. change (rpm_lift ?t) with (vreg ⋅ t).
              cbn. reflexivity.
            + apply ccmeta_refl. cbn. reflexivity.
          - apply ccmeta_refl. cbn. reflexivity.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          apply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          apply ccmeta_refl.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          erewrite !erase_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
          cbn. eapply congr_cEl. eapply congr_capp. 2: reflexivity.
          hide_rhs rhs. asimpl. autosubst_unfold.
          repeat unfold_funcomp.
          rewrite ?renRen_cterm. rewrite <- !funcomp_assoc.
          change (((S >> S) >> S) >> vreg) with (vreg >> S >> S >> S >> S >> S >> S).
          rewrite !funcomp_assoc. rewrite <- !renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          resubst. asimpl. repeat unfold_funcomp.
          ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          subst rhs. reflexivity.
        }
        cbn. constructor.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          2:{
            change (rpm_lift ?t) with (vreg ⋅ t). cbn. econv.
          }
          apply ccmeta_refl.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
          rewrite !pren_S_pw. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        }
        unfold shift. change (var_zero) with 0.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        eapply cconv_trans.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          - apply ccmeta_refl.
            erewrite !param_ren. 2-9: eauto using rscoping_S, rscoping_comp_S.
            rewrite !pren_S_pw.
            change (rpm_lift ?t) with (vreg ⋅ t). cbn.
            lhs_ssimpl.
            rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
            reflexivity.
          - constructor. 2: econv.
            constructor.
        }
        cbn. eapply cconv_trans.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          - constructor. 1: econv.
            constructor.
          - constructor.
        }
        cbn. econv.
      }
      2:{
        clear IHh4.
        cbn. ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * {
              eapply ccmeta_conv.
              - ertype.
              - cbn. reflexivity.
            }
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              cbn. f_equal. f_equal. ssimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * ertype.
            * cbn. f_equal. ssimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * ertype. eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  * cbn. reflexivity.
                + cbn. f_equal. ssimpl.
                  rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
                  reflexivity.
              - cbn. f_equal. f_equal. ssimpl.
                rewrite <- !funcomp_assoc. rewrite <- !rinstInst'_cterm.
                reflexivity.
            }
            * cbn. f_equal. f_equal. f_equal. ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- !rinstInst'_cterm.
              reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            2:{
              eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. econstructor.
                  * ertype.
                  * {
                    cbn. erewrite !md_ren.
                    2-15: eauto using rscoping_S, rscoping_comp_S.
                    remd. cbn.
                    change (epm_lift ?t) with (vreg ⋅ t). cbn.
                    eapply cconv_trans. 1: constructor.
                    constructor.
                    1:{
                      apply ccmeta_refl. ssimpl. reflexivity.
                    }
                    eapply cconv_trans. 1: constructor.
                    eapply cconv_trans. 1: constructor.
                    constructor.
                    - apply ccmeta_refl.
                      erewrite !erase_ren.
                      2-5: eauto using rscoping_S, rscoping_comp_S.
                      lhs_ssimpl. rewrite <- !funcomp_assoc.
                      rewrite <- rinstInst'_cterm.
                      rewrite !funcomp_assoc.
                      rewrite <- renRen_cterm.
                      change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                      reflexivity.
                    - eapply cconv_trans. 1: constructor.
                      apply ccmeta_refl.
                      erewrite !erase_ren.
                      2-15: eauto using rscoping_S, rscoping_comp_S.
                      eapply congr_cPi. 1: reflexivity.
                      + eapply congr_cEl. eapply congr_capp. 2: reflexivity.
                        hide_rhs rhs. asimpl. autosubst_unfold.
                        repeat unfold_funcomp.
                        rewrite ?renRen_cterm, ?renSubst_cterm.
                        ssimpl. rewrite <- !funcomp_assoc.
                        rewrite <- rinstInst'_cterm.
                        rewrite !funcomp_assoc. rewrite <- renRen_cterm.
                        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                        subst rhs. reflexivity.
                      + eapply congr_cEl. eapply congr_capp.
                        2:{
                          lhs_ssimpl. reflexivity.
                        }
                        hide_rhs rhs. asimpl. autosubst_unfold.
                        repeat unfold_funcomp.
                        rewrite ?renRen_cterm, ?renSubst_cterm.
                        ssimpl. rewrite <- !funcomp_assoc.
                        rewrite <- rinstInst'_cterm.
                        rewrite !funcomp_assoc. rewrite <- renRen_cterm.
                        change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                        subst rhs. reflexivity.
                  }
                  * {
                    cbn. ertype.
                    - eapply ccmeta_conv. 1: ertype.
                      reflexivity.
                    - eapply ccmeta_conv. 1: ertype.
                      reflexivity.
                    - eapply ccmeta_conv.
                      + ertype. eapply ccmeta_conv. 1: ertype.
                        cbn. f_equal. f_equal. f_equal.
                        ssimpl. reflexivity.
                      + reflexivity.
                    - eapply ccmeta_conv.
                      + econstructor.
                        * {
                          eapply ccmeta_conv.
                          - ertype.
                          - cbn. reflexivity.
                        }
                        * {
                          eapply ccmeta_conv.
                          - econstructor.
                            * eapply ccmeta_conv. 1: ertype.
                              cbn. reflexivity.
                            * eapply ccmeta_conv. 1: ertype.
                              cbn. f_equal. f_equal. ssimpl. reflexivity.
                            * eapply ccmeta_conv. 1: ertype.
                              reflexivity.
                          - f_equal. f_equal. ssimpl. reflexivity.
                        }
                      + reflexivity.
                  }
                + cbn. f_equal. f_equal. f_equal. ssimpl.
                  rewrite rinstInst'_cterm. reflexivity.
              - cbn. f_equal. f_equal. f_equal.
                ssimpl. rewrite rinstInst'_cterm. reflexivity.
            }
            eapply ccmeta_conv.
            * {
              econstructor.
              - eapply ccmeta_conv.
                + econstructor.
                  * {
                    eapply ccmeta_conv.
                    - econstructor.
                      + eapply ccmeta_conv.
                        * {
                          econstructor.
                          - eapply ccmeta_conv. 1: ertype.
                            cbn. reflexivity.
                          - ertype. eapply ccmeta_conv. 1: ertype.
                            reflexivity.
                        }
                        * {
                          cbn. reflexivity.
                        }
                      + ertype. eapply ccmeta_conv. 1: ertype.
                        reflexivity.
                    - cbn. eapply congr_cPi. 1: reflexivity.
                      + lhs_ssimpl. rewrite <- !funcomp_assoc.
                        rewrite <- rinstInst'_cterm.
                        reflexivity.
                      + reflexivity.
                  }
                  * {
                    econstructor.
                    - eapply ccmeta_conv. 1: ertype.
                      cbn. reflexivity.
                    - eapply ccmeta_conv. 1: ertype.
                      cbn. f_equal. f_equal. rasimpl. reflexivity.
                    - eapply ccmeta_conv. 1: ertype.
                      reflexivity.
                  }
                + cbn. reflexivity.
              - eapply ccmeta_conv.
                + econstructor.
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. lhs_ssimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. unfold var_zero. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. rasimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. f_equal. rasimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  }
                  eapply ccmeta_conv. 1: ertype.
                  reflexivity.
                + f_equal. rasimpl. rewrite !rinstInst'_cterm. reflexivity.
            }
            * cbn. f_equal. f_equal. f_equal.
              rasimpl. reflexivity.
          + reflexivity.
      }
      cbn in *.
      change (epm_lift ?t) with (vreg ⋅ t). cbn.
      change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
      eapply param_erase_typing in h3 as hze. 2: ertype.
      cbn in hze. remd in hze. cbn in hze.
      eapply ccmeta_conv in hze.
      2:{
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        reflexivity.
      }
      eapply param_erase_typing in h4 as hse. 2: ertype.
      cbn in hse. erewrite !md_ren in hse.
      2-15: eauto using rscoping_S, rscoping_comp_S.
      remd in hse. cbn in hse.
      eapply ctype_conv in hse.
      2:{
        clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6 IHh1 IHh2 IHh3 IHh4 IHh5.
        clear IHh6 hAe hPe hze hse.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        eapply cconv_trans. 1: constructor.
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        eapply cconv_trans. 1: constructor.
        erewrite !erase_ren.
        2-19: eauto using rscoping_S, rscoping_comp_S.
        constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        }
        eapply cconv_trans. 1: constructor.
        constructor.
        - constructor. constructor. 2: econv.
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          rewrite !funcomp_assoc. rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        - constructor. constructor.
          + apply ccmeta_refl. lhs_ssimpl.
            rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
            rewrite !funcomp_assoc. rewrite <- renRen_cterm.
            change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
            reflexivity.
          + apply ccmeta_refl. lhs_ssimpl. cbn. reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv. 1: ertype.
          reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. f_equal. f_equal. f_equal. rasimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + econstructor.
            * eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * {
              eapply ccmeta_conv.
              - econstructor.
                + eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  cbn. f_equal. f_equal. rasimpl. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - reflexivity.
            }
          + reflexivity.
      }
      ertype. all: try assumption.
      * eapply ccmeta_conv. 1: eassumption.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        rasimpl. reflexivity.
      * eapply ccmeta_conv. 1: eassumption.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        cbn. f_equal. f_equal. f_equal. f_equal.
        rasimpl. reflexivity.
    + simpl in IHh4. erewrite !md_ren in IHh4.
      2-15: eauto using rscoping_S, rscoping_comp_S.
      remd in IHh4. cbn in IHh4.
      eapply ctype_conv in IHh4.
      2:{
        clear. clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6 IHh1 IHh2 IHh3 IHh5.
        clear IHh6 hAe hPe.
        change (epm_lift ?t) with (vreg ⋅ t). unfold pmPiNP.
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          lhs_ssimpl. rewrite <- rinstInst'_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          econv.
        }
        lhs_hnf. constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl. rewrite <- !rinstInst'_cterm.
          reflexivity.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          eapply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          cbn. econv.
        }
        lhs_hnf. constructor.
        1:{
          cbn. econv.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          eapply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf.
        constructor.
        1:{
          cbn. constructor. constructor.
          lhs_hnf.
          lazymatch goal with
          | |- ?G ⊢ᶜ _ ≡ _ => remember G as C eqn:eC
          end.
          erewrite !erase_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
          lhs_ssimpl. rewrite <- !funcomp_assoc.
          change ((S >> S) >> vreg) with (vreg >> S >> S >> S >> S).
          rewrite !funcomp_assoc. rewrite <- renSubst_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          econv.
        }
        lhs_hnf.
        constructor.
        1:{
          lhs_hnf. constructor.
          - lhs_hnf. constructor.
            + lhs_hnf. apply ccmeta_refl. cbn.
              erewrite !erase_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
              hide_rhs rhs. asimpl. autosubst_unfold. asimpl.
              repeat unfold_funcomp.
              rewrite ?renRen_cterm. rewrite <- !funcomp_assoc.
              change ((S >> S) >> vreg) with (vreg >> S >> S >> S >> S).
              rewrite !funcomp_assoc. rewrite <- !renRen_cterm.
              change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
              resubst. asimpl. repeat unfold_funcomp.
              ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
              subst rhs. reflexivity.
            + apply ccmeta_refl. cbn.
              change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
              erewrite !param_ren. 2-5: eauto using rscoping_S, rscoping_comp_S.
              rewrite !pren_S_pw.
              lhs_ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
              reflexivity.
            + apply ccmeta_refl. cbn. change (rpm_lift ?t) with (vreg ⋅ t).
              cbn. reflexivity.
            + apply ccmeta_refl. cbn. reflexivity.
          - apply ccmeta_refl. cbn. reflexivity.
        }
        lhs_hnf.
        eapply cconv_trans.
        1:{
          apply ccong_app. 2: econv.
          lhs_hnf. econv.
        }
        eapply cconv_trans. 1: constructor.
        lhs_hnf. constructor.
        1:{
          apply ccmeta_refl.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          erewrite !erase_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
          cbn. eapply congr_cEl. eapply congr_capp. 2: reflexivity.
          hide_rhs rhs. asimpl. autosubst_unfold.
          repeat unfold_funcomp.
          rewrite ?renRen_cterm. rewrite <- !funcomp_assoc.
          change (((S >> S) >> S) >> vreg) with (vreg >> S >> S >> S >> S >> S >> S).
          rewrite !funcomp_assoc. rewrite <- !renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          resubst. asimpl. repeat unfold_funcomp.
          ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          subst rhs. reflexivity.
        }
        cbn. constructor.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          2:{
            change (rpm_lift ?t) with (vreg ⋅ t). cbn. econv.
          }
          apply ccmeta_refl.
          change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          erewrite !param_ren. 2-7: eauto using rscoping_S, rscoping_comp_S.
          rewrite !pren_S_pw. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        }
        unfold shift. change (var_zero) with 0.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        eapply cconv_trans.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          - apply ccmeta_refl.
            erewrite !param_ren. 2-9: eauto using rscoping_S, rscoping_comp_S.
            rewrite !pren_S_pw.
            change (rpm_lift ?t) with (vreg ⋅ t). cbn.
            lhs_ssimpl.
            rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
            reflexivity.
          - constructor. 2: econv.
            constructor.
        }
        cbn. eapply cconv_trans.
        1:{
          constructor. 2: econv.
          constructor. 2: econv.
          constructor. 2: econv.
          constructor.
          - constructor. 1: econv.
            constructor.
          - constructor.
        }
        cbn. econv.
      }
      2:{
        clear IHh4.
        cbn. ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * {
              eapply ccmeta_conv.
              - ertype.
              - cbn. reflexivity.
            }
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              cbn. f_equal. f_equal. rasimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * ertype.
            * cbn. f_equal. rasimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * ertype. eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  * cbn. reflexivity.
                + cbn. f_equal. ssimpl.
                  rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
                  reflexivity.
              - cbn. f_equal. f_equal. ssimpl.
                rewrite <- !funcomp_assoc. rewrite <- !rinstInst'_cterm.
                reflexivity.
            }
            * cbn. f_equal. f_equal. f_equal. ssimpl.
              rewrite <- !funcomp_assoc. rewrite <- !rinstInst'_cterm.
              reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + econstructor.
            * {
              eapply ccmeta_conv.
              - econstructor.
                + eapply ccmeta_conv.
                  * {
                    econstructor.
                    - eapply ccmeta_conv.
                      + econstructor.
                        * {
                          eapply ccmeta_conv.
                          - econstructor.
                            + eapply ccmeta_conv. 1: ertype.
                              cbn. reflexivity.
                            + ertype. eapply ccmeta_conv. 1: ertype.
                              reflexivity.
                          - cbn. reflexivity.
                        }
                        * ertype. eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                      + cbn. eapply congr_cPi. 1,3: reflexivity.
                        lhs_ssimpl. rewrite <- !funcomp_assoc.
                        rewrite <- rinstInst'_cterm. reflexivity.
                    - econstructor.
                      + eapply ccmeta_conv. 1: ertype.
                        cbn. reflexivity.
                      + eapply ccmeta_conv. 1: ertype.
                        cbn. f_equal. ssimpl. reflexivity.
                      + eapply ccmeta_conv. 1: ertype.
                        reflexivity.
                  }
                  * cbn. eapply congr_cPi. 1,3: reflexivity.
                    lhs_ssimpl. rewrite <- !funcomp_assoc.
                    rewrite <- !rinstInst'_cterm. reflexivity.
                + econstructor.
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. lhs_ssimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. unfold var_zero. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. rasimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. f_equal. rasimpl. reflexivity.
                  }
                  1:{
                    eapply ccmeta_conv. 1: ertype.
                    cbn. reflexivity.
                  }
                  eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - cbn. eapply congr_cPi. 1,3: reflexivity.
                lhs_ssimpl. rewrite <- !funcomp_assoc.
                rewrite <- !rinstInst'_cterm. reflexivity.
            }
            * {
              eapply ccmeta_conv.
              - eapply ccmeta_conv.
                + econstructor.
                  * {
                    eapply ccmeta_conv.
                    - econstructor.
                      + eapply ccmeta_conv.
                        * {
                          econstructor.
                          - eapply ccmeta_conv.
                            + econstructor.
                              * {
                                econstructor.
                                - ertype.
                                - cbn. change (epm_lift ?t) with (vreg ⋅ t).
                                  erewrite !md_ren.
                                  2-15: eauto using rscoping_S, rscoping_comp_S.
                                  lhs_hnf.
                                  eapply cconv_trans.
                                  1:{
                                    apply ccmeta_refl. eapply congr_cEl.
                                    lhs_hnf.
                                    reflexivity.
                                  }
                                  eapply cconv_trans. 1: constructor.
                                  lhs_hnf.
                                  constructor.
                                  1:{
                                    apply ccmeta_refl. cbn.
                                    lhs_ssimpl.
                                    rewrite <- renRen_cterm.
                                    change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                                    reflexivity.
                                  }
                                  lhs_hnf.
                                  eapply cconv_trans.
                                  1:{
                                    apply ccmeta_refl. eapply congr_cEl.
                                    lhs_hnf.
                                    reflexivity.
                                  }
                                  eapply cconv_trans. 1: constructor.
                                  lhs_hnf.
                                  constructor.
                                  1:{
                                    apply ccmeta_refl. cbn. reflexivity.
                                  }
                                  lhs_hnf.
                                  eapply cconv_trans.
                                  1:{
                                    apply ccmeta_refl. eapply congr_cEl.
                                    lhs_hnf.
                                    reflexivity.
                                  }
                                  eapply cconv_trans. 1: constructor.
                                  lhs_hnf. constructor.
                                  1:{
                                    apply ccmeta_refl. lhs_hnf.
                                    eapply congr_cEl. lhs_hnf.
                                    eapply congr_evec.
                                    erewrite !erase_ren.
                                    2-5: eauto using rscoping_S, rscoping_comp_S.
                                    lhs_ssimpl.
                                    rewrite <- !funcomp_assoc.
                                    rewrite <- rinstInst'_cterm.
                                    rewrite !funcomp_assoc.
                                    rewrite <- renRen_cterm.
                                    change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                                    reflexivity.
                                  }
                                  lhs_hnf.
                                  eapply cconv_trans.
                                  1:{
                                    apply ccmeta_refl. eapply congr_cEl.
                                    lhs_hnf.
                                    reflexivity.
                                  }
                                  eapply cconv_trans. 1: constructor.
                                  lhs_hnf. constructor.
                                  1:{
                                    remd. cbn. constructor.
                                    constructor. 2: econv.
                                    apply ccmeta_refl.
                                    erewrite !erase_ren.
                                    2-7: eauto using rscoping_S, rscoping_comp_S.
                                    lhs_ssimpl.
                                    rewrite <- !funcomp_assoc.
                                    rewrite <- rinstInst'_cterm.
                                    rewrite !funcomp_assoc.
                                    rewrite <- renRen_cterm.
                                    change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                                    reflexivity.
                                  }
                                  remd.
                                  erewrite !erase_ren.
                                  2-19: eauto using rscoping_S, rscoping_comp_S.
                                  cbn.
                                  constructor.
                                  constructor. all: apply ccmeta_refl.
                                  + clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6.
                                    clear IHh1 IHh2 IHh3 IHh5 IHh6 hAe hPe hne hve.
                                    hide_rhs rhs. autosubst_unfold. resubst.
                                    fsimpl. repeat unfold_funcomp.
                                    unfold up_ren.
                                    subst rhs.
                                    etransitivity.
                                    1:{
                                      eapply ext_cterm_scoped with (θ := vreg >> S >> S >> S >> S >> S >> S >> S >> S >> S >> S >> S >> S >> cvar).
                                      1: apply erase_scoping.
                                      intros x hx.
                                      cbn. unfold vreg.
                                      ssimpl. reflexivity.
                                    }
                                    rewrite <- rinstInst'_cterm.
                                    rewrite !funcomp_assoc.
                                    rewrite <- renRen_cterm.
                                    change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
                                    reflexivity.
                                  + lhs_ssimpl. reflexivity.
                                - ertype.
                                  + eapply ccmeta_conv. 1: ertype.
                                    reflexivity.
                                  + eapply ccmeta_conv. 1: ertype.
                                    reflexivity.
                                  + eapply ccmeta_conv.
                                    * {
                                      econstructor.
                                      - eapply ccmeta_conv. 1: ertype.
                                        cbn. reflexivity.
                                      - eapply ccmeta_conv. 1: ertype.
                                        cbn. f_equal. f_equal.
                                        rasimpl. reflexivity.
                                    }
                                    * reflexivity.
                                  + eapply ccmeta_conv.
                                    * {
                                      econstructor.
                                      - eapply ccmeta_conv. 1: ertype.
                                        cbn. reflexivity.
                                      - econstructor.
                                        + eapply ccmeta_conv. 1: ertype.
                                          cbn. f_equal. rasimpl. reflexivity.
                                        + eapply ccmeta_conv. 1: ertype.
                                          cbn. f_equal. rasimpl. reflexivity.
                                        + eapply ccmeta_conv. 1: ertype.
                                          reflexivity.
                                    }
                                    * reflexivity.
                              }
                              * eapply ccmeta_conv. 1: ertype.
                                cbn. reflexivity.
                            + cbn. reflexivity.
                          - eapply ccmeta_conv. 1: ertype.
                            reflexivity.
                        }
                        * {
                          cbn. reflexivity.
                        }
                      + ertype. eapply ccmeta_conv. 1: ertype.
                        cbn. f_equal. f_equal. ssimpl.
                        rewrite rinstInst'_cterm. reflexivity.
                    - cbn. eapply congr_cPi. 1,3: reflexivity.
                      lhs_ssimpl. rewrite <- !funcomp_assoc.
                      rewrite <- rinstInst'_cterm.
                      reflexivity.
                  }
                  * {
                    eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. f_equal. rasimpl. reflexivity.
                  }
                + cbn. reflexivity.
              - f_equal. f_equal.
                rasimpl. rewrite rinstInst'_cterm. reflexivity.
            }
          + reflexivity.
      }
      cbn in *.
      change (rpm_lift ?t) with (vreg ⋅ t). cbn.
      change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
      change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
      eapply param_revive_typing in h3 as hze. 2: ertype.
      cbn in hze. remd in hze. cbn in hze.
      eapply ccmeta_conv in hze.
      2:{
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        reflexivity.
      }
      eapply param_revive_typing in h4 as hse. 2: ertype.
      cbn in hse. erewrite !md_ren in hse.
      2-15: eauto using rscoping_S, rscoping_comp_S.
      remd in hse. cbn in hse.
      eapply ctype_conv in hse.
      2:{
        clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6 IHh1 IHh2 IHh3 IHh4 IHh5.
        clear IHh6 hAe hPe hze hse hne hve.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        change (vreg ⋅ ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
        eapply cconv_trans. 1: constructor.
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        constructor. 1: econv.
        eapply cconv_trans. 1: constructor.
        erewrite !erase_ren.
        2-19: eauto using rscoping_S, rscoping_comp_S.
        constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          rewrite !funcomp_assoc.
          rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        }
        eapply cconv_trans. 1: constructor.
        constructor.
        - constructor. constructor. 2: econv.
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          rewrite !funcomp_assoc. rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        - constructor. constructor.
          + apply ccmeta_refl. lhs_ssimpl.
            rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
            rewrite !funcomp_assoc. rewrite <- renRen_cterm.
            change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
            reflexivity.
          + apply ccmeta_refl. lhs_ssimpl. cbn. reflexivity.
      }
      2:{
        ertype.
        - eapply ccmeta_conv. 1: ertype.
          reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. f_equal. f_equal. f_equal. rasimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + econstructor.
            * eapply ccmeta_conv. 1: ertype.
              cbn. reflexivity.
            * {
              eapply ccmeta_conv.
              - econstructor.
                + eapply ccmeta_conv. 1: ertype.
                  cbn. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  cbn. f_equal. f_equal. rasimpl. reflexivity.
                + eapply ccmeta_conv. 1: ertype.
                  reflexivity.
              - reflexivity.
            }
          + reflexivity.
      }
      unfold shift in *. unfold var_zero in *.
      eapply ccmeta_conv.
      2:{
        symmetry. eapply congr_capp. 1: reflexivity.
        eapply congr_evec_elim. 1-3: reflexivity.
        eapply congr_clam. 1-2: reflexivity.
        eapply congr_clam. 1: reflexivity.
        1:{
          lhs_ssimpl. rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        }
        eapply congr_capp. 2: reflexivity.
        eapply congr_capp.
        - lhs_ssimpl. rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧v) with (⟦ G | t ⟧pv).
          reflexivity.
        - eapply congr_evec_elim. 1,3: reflexivity.
          1:{
            lhs_ssimpl. rewrite <- renRen_cterm.
            change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
            reflexivity.
          }
          eapply congr_clam. 1: reflexivity.
          1:{
            lhs_ssimpl. rewrite <- renRen_cterm.
            change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
            reflexivity.
          }
          eapply congr_clam. 1: reflexivity.
          1:{
            lhs_ssimpl. rewrite <- renRen_cterm.
            change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
            reflexivity.
          }
          reflexivity.
      }
      eapply ccmeta_conv. 1: ertype.
      all: try assumption.
      * eapply ccmeta_conv. 1: eassumption.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        rasimpl. reflexivity.
      * eapply ccmeta_conv. 1: eassumption.
        unfold capps.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        f_equal. f_equal. f_equal. f_equal. f_equal.
        rasimpl. reflexivity.
      * unfold elength. cbn. f_equal. f_equal. f_equal. f_equal.
        f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
        rasimpl. reflexivity.
    + simpl in IHh4. erewrite !md_ren in IHh4.
      2-7: eauto using rscoping_S, rscoping_comp_S.
      remd in IHh4. cbn in IHh4.
      eapply ctype_conv in IHh4.
      2:{
        clear. clear H H0 H1 H2 H3 H4 H5 h1 h2 h3 h4 h5 h6 IHh1 IHh2 IHh3 IHh5.
        clear IHh6 hAe hPe.
        unfold pPi. cbn.
        change (epm_lift ?t) with (vreg ⋅ t). cbn.
        change (rpm_lift ?t) with (vreg ⋅ t). cbn.
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        erewrite !erase_ren, !param_ren.
        2-23: eauto using rscoping_S, rscoping_comp_S.
        change (epm_lift ?t) with (vreg ⋅ t).
        change (vreg ⋅ ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
        constructor. 1: econv.
        constructor. 1: econv.
        constructor. 1: econv.
        constructor. 1: econv.
        constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl.
          change (S >> vreg) with (vreg >> S >> S).
          rewrite <- !funcomp_assoc.
          change (S >> vreg) with (vreg >> S >> S).
          rewrite !funcomp_assoc.
          rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          reflexivity.
        }
        rewrite !pren_S_pw.
        constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc.
          change ((S >> S) >> vreg) with (vreg >> S >> S >> S >> S).
          rewrite !funcomp_assoc.
          rewrite <- renRen_cterm.
          change (ren_cterm vreg ⟦ ?G | ?t ⟧ε) with (⟦ G | t ⟧pε).
          unfold vreg. cbn. reflexivity.
        }
        constructor.
        1:{
          apply ccmeta_refl. lhs_ssimpl.
          unfold vreg. cbn. reflexivity.
        }
        constructor. 2: econv.
        constructor. 2: econv.
        constructor.
        2:{
          eapply cconv_trans.
          1:{
            constructor. 2: econv.
            constructor.
          }
          cbn. eapply cconv_trans. 1: constructor.
          cbn. econv.
        }
        constructor.
        - apply ccmeta_refl. lhs_ssimpl.
          rewrite <- !funcomp_assoc. rewrite <- rinstInst'_cterm.
          reflexivity.
        - eapply cconv_trans. 1: constructor.
          cbn. econv.
      }
      2:{
        ertype.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv. 1: ertype.
            cbn. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              reflexivity.
            * eapply ccmeta_conv. 1: ertype.
              cbn. f_equal. f_equal. lhs_ssimpl. reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + ertype. eapply ccmeta_conv.
            * {
              ertype. eapply ccmeta_conv.
              - ertype. eapply ccmeta_conv.
                + ertype. eapply ccmeta_conv.
                  * ertype.
                  * cbn. reflexivity.
                + cbn. reflexivity.
              - cbn. eapply congr_cPi. 1,3: reflexivity.
                f_equal. f_equal. rasimpl.
                rewrite rinstInst'_cterm. reflexivity.
            }
            * cbn. f_equal. f_equal. rasimpl. rewrite !rinstInst'_cterm.
              reflexivity.
          + reflexivity.
        - eapply ccmeta_conv.
          + econstructor.
            * {
              eapply ccmeta_conv.
              - econstructor.
                + eapply ccmeta_conv.
                  * {
                    econstructor.
                    - eapply ccmeta_conv.
                      + econstructor.
                        * eapply ccmeta_conv. 1: ertype.
                          cbn. reflexivity.
                        * ertype. eapply ccmeta_conv. 1: ertype.
                          reflexivity.
                      + cbn. reflexivity.
                    - ertype. eapply ccmeta_conv. 1: ertype.
                      reflexivity.
                  }
                  * cbn. eapply congr_cPi. 1,3: reflexivity.
                    lhs_ssimpl. rewrite <- !funcomp_assoc.
                    rewrite <- rinstInst'_cterm. reflexivity.
                + ertype.
                  * eapply ccmeta_conv. 1: ertype.
                    reflexivity.
                  * eapply ccmeta_conv. 1: ertype.
                    cbn. f_equal. f_equal. rasimpl. reflexivity.
                  * eapply ccmeta_conv. 1: ertype.
                    reflexivity.
              - cbn. eapply congr_cPi. 1,3: reflexivity.
                lhs_ssimpl. rewrite <- !funcomp_assoc.
                rewrite <- !rinstInst'_cterm.
                reflexivity.
            }
            * {
              econstructor.
              - eapply ccmeta_conv. 1: ertype.
                cbn. f_equal. rasimpl. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                cbn. f_equal. rasimpl. reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                cbn. f_equal. f_equal. rasimpl.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
              - eapply ccmeta_conv. 1: ertype.
                reflexivity.
            }
          + reflexivity.
      }
      cbn in *.
      unfold shift in *. unfold var_zero in *.
      ertype. all: assumption.
  - unfold ptype. cbn.
    change (epm_lift ctt) with ctt.
    econstructor.
    + etype.
    + apply cconv_sym. constructor.
    + eapply ccmeta_conv.
      * etype.
      * cbn. reflexivity.
  - unfold ptype. cbn.
    unfold ptype in IHh1. remd in IHh1. cbn in IHh1.
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    destruct m. all: cbn in *.
    + etype. eapply ccmeta_conv.
      * {
        etype.
        econstructor.
        - etype.
        - eapply cconv_trans. 1: constructor.
          cbn. apply cconv_refl.
        - etype.
      }
      * cbn. reflexivity.
    + etype. eapply ccmeta_conv.
      * {
        etype. econstructor.
        - etype.
        - eapply cconv_trans. 1: constructor.
          cbn. apply cconv_refl.
        - etype.
      }
      * reflexivity.
    + eapply ccmeta_conv.
      * {
        etype. eapply ccmeta_conv.
        - etype. econstructor.
          + etype.
          + eapply cconv_trans. 1: constructor.
            cbn. apply cconv_refl.
          + etype.
        - reflexivity.
      }
      * reflexivity.
    + eapply ccmeta_conv.
      * {
        etype. econstructor.
        - etype.
        - eapply cconv_trans. 1: constructor.
          cbn. apply cconv_refl.
        - etype.
      }
      * reflexivity.
  - assert (hBe : isProp m = false → ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | B ⟧pε : cty i).
    { intro ep.
      econstructor.
      - ertype.
      - cbn. rewrite ep. rewrite epm_lift_eq. cbn. constructor.
      - ertype.
    }
    unfold ptype in IHh2. remd in IHh2. cbn in IHh2.
    eapply ctype_conv in IHh2.
    2:{
      instantiate (1 := if isKind m then _ else if isProp m then _ else _).
      destruct (isKind m) eqn:ek. 2: destruct (isProp m) eqn:ep.
      - unfold pKind. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - unfold pProp. eapply cconv_trans. 1: constructor.
        cbn. econv.
      - unfold pType. eapply cconv_trans. 1: constructor.
        cbn. econv.
    }
    2:{
      instantiate (1 := if isKind m then _ else if isProp m then _ else _).
      destruct (isKind m) eqn:ek. 2: destruct (isProp m) eqn:ep.
      - mode_eqs. ertype.
      - mode_eqs. ertype.
      - ertype. reflexivity.
    }
    econstructor.
    + eassumption.
    + unfold ptype. remd.
      destruct (relm m) eqn:er. 2: destruct (isGhost m) eqn:eg.
      * econv. eapply param_castrm_conv. all: eassumption.
      * econv. eapply param_castrm_conv. all: eassumption.
      * eapply param_castrm_conv. all: eassumption.
    + unfold ptype. remd.
      instantiate (1 := if relm m then _ else if isGhost m then _ else _).
      destruct (relm m) eqn:er. 2: destruct (isGhost m) eqn:eg.
      * {
        destruct (isProp m) eqn:ep. 1:{ mode_eqs. discriminate. }
        eapply ccmeta_conv.
        - econstructor.
          + eapply ccmeta_conv. 1: ertype.
            instantiate (1 := if isKind m then _ else _).
            destruct (isKind m) eqn:ek. all: reflexivity.
          + econstructor.
            * ertype. remd. assumption.
            * rewrite param_erase_ty_tm. econstructor.
              eapply ccong_epm_lift. 2: reflexivity.
              apply erase_castrm_conv. assumption.
            * ertype. reflexivity.
        - instantiate (2 := if isKind m then _ else _).
          instantiate (1 := if isKind m then _ else _).
          destruct (isKind m) eqn:ek. all: cbn. all: reflexivity.
      }
      * {
        mode_eqs. cbn. cbn in IHh2.
        eapply ccmeta_conv.
        - econstructor.
          + eapply ccmeta_conv. 1: ertype.
            reflexivity.
          + econstructor.
            * ertype.
            * rewrite param_erase_ty_tm. econstructor.
              eapply ccong_epm_lift. 2: reflexivity.
              apply erase_castrm_conv. assumption.
            * ertype.
        - cbn. reflexivity.
      }
      * {
        destruct m. all: try discriminate.
        cbn. cbn in IHh2. eassumption.
      }
Qed.

Lemma param_pTypeGhost :
  ∀ Γ A i,
    cscoping Γ A mKind →
    (Γ ⊢ A : Sort mType i ∨ Γ ⊢ A : Sort mGhost i) →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : capp (pType i) ⟦ sc Γ | A ⟧pε →
    ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧p : ⟦ sc Γ | A ⟧pτ ⇒[ cType ] cSort cProp 0.
Proof.
  intros Γ A i hmA [hA | hA] h.
  - eapply param_pType. all: eassumption.
  - eapply param_pGhost. all: eassumption.
Qed.

Corollary param_context :
  ∀ Γ,
    wf Γ →
    cwf ⟦ Γ ⟧p.
Proof.
  intros Γ h.
  induction h.
  - constructor.
  - eapply param_typing in H0 as hp. unfold ptype in hp.
    remd in hp. cbn in hp.
    assert (hpe : isProp m = false → ⟦ Γ ⟧p ⊢ᶜ ⟦ sc Γ | A ⟧pτ : cSort cType i).
    { intro ep. ertype. }
    cbn. destruct_ifs.
    + mode_eqs. cbn in hp. apply param_pProp in hp.
      constructor. 2: constructor.
      constructor. 1: assumption.
      cbn. exists 0. assumption.
    + mode_eqs. apply param_pKind in hp. 2,3: ertype.
      constructor. 1: constructor. 1: assumption.
      * cbn. exists i. eauto.
      * {
        cbn. eexists.
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
    + eapply param_pTypeGhost in hp. 2: assumption.
      2:{ destruct m. all: try discriminate. all: intuition eauto. }
      constructor. 1: constructor. 1: assumption.
      * cbn. exists i. eauto.
      * {
        cbn. eexists.
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv.
          + ertype.
          + cbn. reflexivity.
        - cbn. reflexivity.
      }
Qed.

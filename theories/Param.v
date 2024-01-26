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

(** Parametricity translation

  We start by defining useful shorthands.

**)

Definition pKind i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cType i).

Definition pType i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cProp 0).

Definition pProp i :=
  clam cType (cty i) (cSort cProp 0).

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
          (S ⋅ (clam cProp (capp AP uv) tP)))
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
          (S ⋅ (clam cProp (capp AP uv) tP)))
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
    else if isProp m then pProp i
    else pType i ;
  ⟦ Γ | Pi i j m mx A B ⟧p :=
    let Te := ⟦ Γ | Pi i j m mx A B ⟧ε in
    let Ae := ⟦ Γ | A ⟧ε in
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
        | mProp => (S ⋅ Ap) ⇒[ cProp ] capp (S ⋅ Bp) (cvar 0)
        end
      )
    | mType =>
      clam cProp (capp (pKind k) Te) (
        match mx with
        | mKind => pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mType => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mGhost => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (cvar 2))
        | mProp => (S ⋅ Ap) ⇒[ cProp ] capp (S ⋅ Bp) (cvar 0)
        end
      )
    | mGhost =>
      clam cProp (capp (pKind k) Te) (
        if isKind mx then pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        else if isProp mx then cPi cProp Ap (capp Bp (cvar 1))
        else pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
      )
    | mProp =>
      if isProp mx then cPi cProp Ap (close Bp)
      else if isKind mx then pPi cType Ae Ap Bp
      else pPi cProp Ae Ap Bp
    end ;
  ⟦ Γ | lam mx A B t ⟧p :=
    if isProp mx then clam cProp ⟦ Γ | A ⟧p (close ⟦ mx :: Γ | t ⟧p)
    else if isKind mx then plam cType ⟦ Γ | A ⟧ε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p
    else plam cProp ⟦ Γ | A ⟧ε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p ;
  ⟦ Γ | app u v ⟧p :=
    if relm (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧ε) ⟦ Γ | v ⟧p
    else if isGhost (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧v) ⟦ Γ | v ⟧p
    else capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧p
  ;
  ⟦ Γ | Erased A ⟧p :=
    if isKind (md Γ A) then ⟦ Γ | A ⟧p else cDummy ;
  ⟦ Γ | hide t ⟧p :=
    if isType (md Γ t) then ⟦ Γ | t ⟧p else cDummy ;
  ⟦ Γ | reveal t P p ⟧p :=
    if relm (md Γ p) then cDummy
    else capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧v) ⟦ Γ | t ⟧p ;
  ⟦ Γ | revealP t p ⟧p :=
    if isKind (md Γ p) then cDummy
    else capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧v) ⟦ Γ | t ⟧p ;
  ⟦ Γ | gheq A u v ⟧p := squash (teq ⟦ Γ | A ⟧ε ⟦ Γ | u ⟧v ⟦ Γ | v ⟧v) ;
  ⟦ Γ | ghrefl A u ⟧p := sq (trefl ⟦ Γ | A ⟧ε ⟦ Γ | u ⟧v) ;
  ⟦ Γ | ghcast A u v e P t ⟧p :=
    let eP := ⟦ Γ | e ⟧p in
    let PP := ⟦ Γ | P ⟧p in
    let uv := ⟦ Γ | u ⟧v in
    let vv := ⟦ Γ | v ⟧v in
    let vP := ⟦ Γ | v ⟧p in
    let Ae := ⟦ Γ | A ⟧ε in
    let AP := ⟦ Γ | A ⟧p in
    let te := ⟦ Γ | t ⟧ε in
    let tv := ⟦ Γ | t ⟧v in
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
    else if isKind m then cbot_elim cType (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧∅) ⟦ Γ | p ⟧p
    else cbot_elim cProp (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧∅) ⟦ Γ | p ⟧p
}
where "⟦ G | u '⟧p'" := (param_term G u).

Reserved Notation "⟦ G '⟧p'" (at level 9, G at next level).

Equations param_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧p := [] ;
  ⟦ Γ ,, (mx, A) ⟧p :=
    if isProp mx then None :: Some (cProp, ⟦ sc Γ | A ⟧p) :: ⟦ Γ ⟧p
    else if isKind mx then
      Some (cType, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧p
    else
      Some (cProp, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧p
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

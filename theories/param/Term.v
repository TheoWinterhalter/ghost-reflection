(*** Parametricity ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl
  CTyping TermMode Typing CCMetaTheory Erasure Revival.

Import ListNotations.

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


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
  Variables are then either even and regular or odd and correspond to
  parametricity.

**)

Definition vreg x := 2 * x.
Definition vpar x := 2 * x + 1.

(** Parametricity translation **)

Reserved Notation "⟦ G | u '⟧p'" (at level 9, G, u at next level).

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
    (* let Be := ⟦ mx :: Γ | B ⟧ε in *)
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
  ⟦ Γ | ghcast e P t ⟧p := cDummy ; (* TODO *)
  ⟦ Γ | bot ⟧p := cbot ;
  ⟦ Γ | bot_elim m A p ⟧p :=
    if isProp m then cbot_elim cProp ⟦ Γ | A ⟧p ⟦ Γ | p ⟧p
    else if isKind m then cbot_elim cType (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧∅) ⟦ Γ | p ⟧p
    else cbot_elim cProp (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧∅) ⟦ Γ | p ⟧p
}
where "⟦ G | u '⟧p'" := (param_term G u).

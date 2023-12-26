From Coq Require Import Utf8 List Bool.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping Scoping
  CTyping TermMode Typing.

Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Definition cDummy := cvar 0.

(* TODO MOVE to utils *)
Section Inb.

  Context {A} (eqb : A → A → bool).

  Definition inb (a : A) (l : list A) :=
    existsb (eqb a) l.

  Definition inclb (l l' : list A) : bool :=
    forallb (λ x, inb x l') l.

End Inb.

(* TODO MOVE *)
Definition mode_eqb (m m' : mode) : bool :=
  match m, m' with
  | mProp, mProp
  | mGhost, mGhost
  | mType, mType
  | mKind, mKind => true
  | _,_ => false
  end.

Definition mode_inb := inb mode_eqb.
Definition mode_inclb := inclb mode_eqb.

Fixpoint erase (Γ : scope) (t : term) : cterm :=
  match t with
  | var x => cvar x
  | Sort mProp i => ctyval ctop cstar (* Need Box from Prop to Type (S i) *)
  (* But if I need to have η for it then I'm screwed... We'll see
  what's needed… *)
  | Sort _m i => ctyval (cty i) ctyerr
  | Pi i j m mx A B =>
    if mode_inb mx [ mType ; mKind ] && negb (mode_eqb m mProp)
    then
      let A' := cEl (erase Γ A) in
      let cB' := erase (mx :: Γ) B in
      let B' := cEl cB' in
      let Be :=cErr cB' in
      ctyval (cPi cType A' B') (clam cType A' Be)
    else cDummy
  | _ => cDummy
  end.


From Coq Require Import Utf8 List.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping Scoping
  CTyping TermMode Typing.

Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Definition cDummy := cvar 0.

Fixpoint erase (Γ : scope) (t : term) : cterm :=
  match t with
  | var x => cvar x
  | Sort mProp i => ctyval ctop cstar (* Need Box from Prop to Type (S i) *)
  | Sort m i => ctyval (cty i) ctyerr
  | _ => cDummy
  end.


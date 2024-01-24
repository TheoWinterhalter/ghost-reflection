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
    if isGhost (md Γ t)
    then
      if isProp mx
      then clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧v
      else close ⟦ mx :: Γ | t ⟧v
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

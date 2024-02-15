(*** Translation from GRTT to GTT ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing RTyping Potential.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Theorem elim_reflection :
  ∀ Γ t A Γ',
    Γ ⊢ˣ t : A →
    tr_ctx Γ Γ' →
    ∑ t' A', Γ' ⊨ t' : A' ∈ ⟦ t : A ⟧x.
Proof.
  intros Γ t A Γ' h hctx.
  induction h in Γ', hctx |- *.
Abort.

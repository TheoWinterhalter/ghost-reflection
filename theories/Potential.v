(*** Potential translations from GRTT to GTT and their properties ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing RTyping.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Definition rmctx (Γ : context) :=
  map (λ '(m, A), (m, ε|A|)) Γ.

Definition tr_ctx Γ Γ' :=
  Γ = rmctx Γ' ∧ wf Γ'.

(* Notation "D ∈ ⟦ G ⟧x" :=
  (tr_ctx G D)
  (at level 8, G at next level). *)

Definition tr_ty t A Γ' t' A' :=
  t = ε|t'| ∧ A = ε|A'| ∧ Γ' ⊢ t' : A'.

Notation "D ⊢ⁱ t : A ∈ ⟦ u | B ⟧x" :=
  (tr_ty u B D t A)
  (at level 8, t, A, u, B at next level).

Lemma tr_choice :
  ∀ t A Γ' t' A' A'' m i,
    Γ' ⊢ⁱ t' : A' ∈ ⟦ t | A ⟧x →
    Γ' ⊢ⁱ A'' : Sort m i ∈ ⟦ A | Sort m i ⟧x →
    Γ' ⊢ⁱ t' : A'' ∈ ⟦ t | A ⟧x.
Proof.
Abort.

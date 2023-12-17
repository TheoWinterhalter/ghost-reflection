(** Basic meta-theory before building the model **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Typing.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Inductive mds (Γ : scope) (σ : nat → term) : scope → Prop :=
| mds_nil : mds Γ σ []
| mds_cons :
    ∀ Δ m,
      mds Γ (↑ >> σ) Δ →
      md Γ (σ var_zero) = m →
      mds Γ σ (m :: Δ).

Lemma md_subst :
  ∀ Γ Δ σ t,
    mds Γ σ Δ →
    md Γ (σ ⋅ t) = md Δ t.
Proof.
  intros Γ Δ σ t h.
  induction t in Γ, Δ, σ, h |- *. all: try reflexivity.
  - simpl. asimpl.
    induction h as [| Δ m h h0 ih].
    + destruct n.
      * simpl. asimpl. (* ??? *) give_up.
      * give_up.
    + give_up.
  - asimpl. unfold action. unfold ActionSubst1. asimpl.
    unfold ">>". asimpl. unfold ">>". simpl.
    apply IHt2.
    (* I don't understand what's happening with autosubst at all! *)
    (* Is it really saving me time? It's seems the opposite. *)
Abort.

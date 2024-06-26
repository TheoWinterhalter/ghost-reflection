(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.wrapping Require Export Core.

Import ListNotations.
Set Default Goal Selector "!".

Ltac ttinv_destruct h HN:=
  ttinv h HN; destruct_exists HN;
  let rec destruct_conj HN :=
  lazymatch type of HN with 
  | _ ∧ _ => let H := fresh "H" in 
      destruct HN as [H HN]; destruct_conj HN
  |_ => idtac end
  in destruct_conj HN.

Lemma scoping_box {Γ : scope} {m : mode } {u : term} {C: □_term} :
  Γ ⊨ C □ u∷m → [|Γ|] □ C ⊨ u∷md ([|Γ|] □ C) u.
Proof.
  intros scope_Cu.
  destruct C as [C|C].
  all: destruct C; cbn in *.
  all: inversion scope_Cu.
  all: erewrite scoping_md.
  all: eauto.
Qed.

Lemma scoping_change_box {Γ : scope} {m : mode } {u u': term} {C: □_term} :
  Γ ⊨ C □ u∷m → [|Γ|] □ C ⊨ u'∷md ([|Γ|] □ C) u → Γ ⊨ C □ u'∷m.
Proof.
  intros scope_Cu scope_u'.
  destruct C as [C|C].
  all: destruct C; cbn in *.
  all: inversion scope_Cu.
  all: try (gscope; erewrite <- scoping_md; eauto).
Qed.

Lemma typing_box {Γ : context} {u A: term} {C: □_term} :
  Γ ⊢ C □ u : A → ∃ B, [Γ] □ C ⊢ u : B.
Proof.
  intro type_Cu.
  destruct C as [C|C].
  all: destruct C; cbn in *.
  all: ttinv_destruct type_Cu type_Cu.
  all: eauto.
Qed.

Lemma sc_scope_box_term {Γ : context} {C: □_term} :
  [| sc Γ |] □ C = sc ([ Γ ] □ C).
Proof.
  destruct C as [C|[C|C]]; reflexivity.
Qed.

(*
Lemma type_conv_urm {Γ : context} {i : level} {m : mode} {A B t : term}:
  Γ⊢A∷𝕂 → Γ⊢B∷𝕂 → Γ⊢t∷m → Γ ⊢ t : A → Γ ⊢ A ≈ B → Γ ⊢ B : Sort m i → Γ ⊢ t : B.
Proof.
  intros scope_A scope_B scope_t type_A conv_urm_A type_B.
  induction conv_urm_A.
  type_conv.

Lemma typing_change_box {Γ : context} {A B u u': term} {C: □_term} (wfΓ : wf Γ):
  Γ ⊢ C □ u:A → [Γ] □ C ⊢ u :B → 
  [Γ] □ C ⊢ u'∷mdc ([Γ] □ C) u →
  [Γ] □ C ⊢ u':B → Γ ⊢ C □ u':A.
Proof.
  intros type_Cu type_u scope_u' type_u'.
  specialize (validity Γ _ _ wfΓ type_Cu) as [scope_Cu [i_u type_A]].
  specialize (scoping_box scope_Cu) as scope_u.
  remember (mdc Γ (C □ u)) as md_t eqn:e_t.
  rewrite sc_scope_box_term in *.
  remember ([Γ] □ C) as Δ eqn:e_Δ.
  remember (mdc Δ u) as md_u eqn:e_u.
  specialize (scoping_type wfΓ type_Cu) as scope_A.
  assert (Γ⊢C □ u'∷md_t) as scope_Cu'.
  { eapply scoping_change_box; eauto.
  rewrite sc_scope_box_term.
  subst; assumption. }
  destruct C as [[]|[]]; cbn in *.
  all: ttinv_destruct type_Cu conv_A.
  all: refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A type_A); [gscope| gscope | ]; cbn; eauto using scoping_subst.
  3, 5: admit.
  all: gtype.
  all: try (subst; erewrite scoping_md in scope_u'; eauto).
  * specialize (type_unique type_u H1) as e.
  * admit.
  - gtype.
  * gtype.
    ttinv_destruct H2 H2.
  * typing
  all: inversion scope_Cu.
  all: inversion scope_Cu'.
  all: ttinv_destruct type_Cu conv_A.
  all: refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A type_A); gscope; gtype.
  - gscope.
  - gscope.
  (*
     all: gtype.
     all: try (gscope; erewrite <- scoping_md; eauto).
   Qed.*) Abort. *)

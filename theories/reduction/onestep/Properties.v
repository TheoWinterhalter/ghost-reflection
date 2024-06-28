(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping Typing BasicMetaTheory.
From GhostTT.reduction Require Import Notations Injectivity.
From GhostTT.reduction.wrapping Require Import Properties.
From GhostTT.reduction.onestep Require Export Reduction.

Import ListNotations.
Set Default Goal Selector "!".

Lemma red_scope {Γ : context} {Ω t t': term} :
  wf Γ → Γ ⊢ t:Ω → t ↣ t' → Γ ⊢ t'∷mdc Γ t.
Proof.
  intros wfΓ type_t red_t.
  specialize (validity Γ t Ω wfΓ type_t) as [scope_t _].
  remember (sc Γ) as Γ0 eqn:eΓ.
  induction red_t in Γ, Γ0, eΓ, Ω, t, t', red_t, type_t, scope_t.
  all: try solve [inversion scope_t; gscope].
  - ttinv type_t type_t.
    destruct type_t as [mx' [m [i [j [A0 [B0 type_t]]]]]].
    destruct type_t as [scope_B0 [scope_lam [scope_u [scope_A0 type_t]]]].
    destruct type_t as [type_lam [type_u [type_A0 [type_B0 conv_Ω]]]].
    ttinv type_lam H.
    destruct H as [i0 [j0 [m0 [B H]]]].
    destruct H as [scope_A [scope_B [scope_t0 H]]].
    destruct H as [type_A [type_B [type_t0 conv_pi]]].
    cbn in conv_pi.
    apply injectivity_Pi in conv_pi; gscope; eauto using scoping_castrm.
    destruct conv_pi as [e0 [e1 [conv_A conv_B]]].
    subst. cbn.
    erewrite scoping_md; eauto.
    eapply scoping_subst; eauto.
    exact (sscoping_one (sc Γ) _ _ scope_u).
  - inversion scope_t.
    match goal with H : _ ⊨ hide _∷_ |- _ =>
        inversion H; subst end.
        gscope.
  - inversion scope_t.
    match goal with H : _ ⊨ tsucc _∷_ |- _ =>
        inversion H; subst end.
        gscope.
  - inversion scope_t. 
    match goal with H : _ ⊨ tvcons _ _ _∷_ |- _ =>
        inversion H; subst end.
        gscope; eauto.
        * intro H; inversion H.
        * eapply scoping_ren; eauto using rscoping_S.
        * eapply scoping_ren; eauto using rscoping_S.
          eapply scoping_ren; eauto using rscoping_S.
        * right; left. reflexivity.
  - eapply scoping_change_box; eauto.
    apply typing_box in type_t as [B type_u].
    apply scoping_box in scope_t.
    subst; cbn in *.
    eapply IHred_t; eauto.
    apply sc_scope_box_term.
Qed.

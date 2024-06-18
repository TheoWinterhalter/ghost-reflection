(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.multisteps Require Import Rho Transitivity.
From GhostTT.reduction.multisteps Require Export Reduction.

Import ListNotations.

Set Default Goal Selector "!".

Theorem reduction_diamond (Γ : scope) (t u v: term) : 
  Γ ⊨ t ↣ u → Γ ⊨ t ↣ v → 
  ∃ w, Γ ⊨ u ↣ w ∧ Γ ⊨ v ↣ w.
Proof.
  intros red_tu red_tv.
  exists (ρ Γ t).
  eauto using reduction_triangle.
Qed.

Theorem reduction_local_confluence (Γ : scope) (t u v: term) : 
  Γ ⊨ t ↣ u → Γ ⊨ t ↣ v → 
  ∃ w, Γ ⊨ u ↣* w ∧ Γ ⊨ v ↣* w.
Proof.
  intros red_t0 red_t1.
  exists (ρ Γ t).
  split; apply red_trans_direct; eauto using reduction_triangle.
Qed.

Theorem reduction_confluence (Γ : scope) (t u v: term) : 
  Γ ⊨ t ↣* u → Γ ⊨ t ↣* v → 
  ∃ w, Γ ⊨ u ↣* w ∧ Γ ⊨ v ↣* w.
Proof.
  intros red_tu red_tv.
  induction red_tu as [t u red_tu | t u1 u0 red_tu red_u0 IH] in u, v, red_tu, red_tv |- *.
  - induction red_tv as [t v red_tv | t v1 v0 red_tv red_v0 IH'] in u, v, red_tu, red_tv |- *.
    * subst. exists v; split; constructor; reflexivity.
    * subst t. 
      exists v1.
      split.
      + apply (Trans Γ u v1 v0); assumption.
      + constructor; reflexivity.
  - induction red_tv as [t v red_tv | t v1 v0 red_tv red_v0 IH'] in u0, u1, v, red_tu, red_tv, red_u0, IH |- *.
    * subst t. 
      exists u1.
      split.
      + constructor; reflexivity.
      + apply (Trans Γ v u1 u0); assumption.
    * assert (∃ w, (Γ⊨(ρ Γ t)↣*w) ∧ Γ⊨v1↣*w) as H.
      { eapply IH'; eauto.
      + eauto using reduction_triangle; eauto.
      + constructor; reflexivity.
      + intros.
        eexists. split; [eassumption | apply red_trans_direct; gred]. }
      clear IH'.
      destruct H as [w_v [red_ρt red_v1]].
      specialize (Trans Γ _ w_v _ (reduction_triangle Γ _ _ red_tu) red_ρt) as red_u0'.
      specialize (IH w_v red_u0').
      destruct IH as [w [red_u1' red_v1']].
      exists w; split.
      + assumption.
      + apply (red_trans_trans w_v); assumption.
Qed.

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
    if isGhost (md (mx :: Γ) t)
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

Reserved Notation "⟦ G '⟧v'" (at level 9, G at next level).

Equations revive_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧v := [] ;
  ⟦ Γ ,, (mx, A) ⟧v :=
    if isProp mx
    then None :: ⟦ Γ ⟧v
    else Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧v
}
where "⟦ G '⟧v'" := (revive_ctx G).

Definition revive_sc (Γ : scope) : cscope :=
  map (λ m, if isProp m then None else Some cType) Γ.

(** Revival of non-ghost terms is cDummy **)

Lemma revival_ng :
  ∀ Γ t,
    isGhost (md Γ t) = false →
    ⟦ Γ | t ⟧v = cDummy.
Proof.
  intros Γ t hm.
  induction t in Γ, hm |- *.
  all: try reflexivity.
  all: try discriminate hm.
  - cbn in *. unfold ghv.
    destruct (nth_error _ _) eqn:e. 2: reflexivity.
    erewrite nth_error_nth in hm. 2: eassumption.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    destruct_if e. 2: reflexivity.
    destruct (md Γ _) eqn:e'. all: discriminate.
  - cbn - [mode_inb] in *. eauto.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
Qed.

From Coq Require Import Utf8 List Bool.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping Scoping
  CTyping TermMode Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

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

Reserved Notation "⟦ G | u '⟧ε'" (at level 0, G, u at next level).
Reserved Notation "⟦ G | u '⟧τ'" (at level 0, G, u at next level).
Reserved Notation "⟦ G | u '⟧∅'" (at level 0, G, u at next level).

(* TODO Bad name! Overlaps with the erase constructor! *)
(* Maybe it should be called erasure too? Or erase_term? *)
Equations erase (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧ε := cvar x ;
  ⟦ Γ | Sort mProp i ⟧ε := ctyval ctop cstar ; (* Need Box from Prop to Type (S i) *)
  (* But if I need to have η for it then I'm screwed... We'll see
  what's needed… *)
  ⟦ Γ | Sort _m i ⟧ε := ctyval (cty i) ctyerr ;
  ⟦ Γ | Pi i j m mx A B ⟧ε :=
    if mode_inb mx [ mType ; mKind ] && negb (mode_eqb m mProp)
    then ctyval (cPi cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧τ) (clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧∅)
    else if mode_inclb [ m ; mx ] [ mGhost ]
    then ctyval (⟦ Γ | A ⟧τ ⇒[ cType ] ⟦ mx :: Γ | B ⟧τ) (clam cType ⟦ Γ | A ⟧τ (S ⋅ ⟦ mx :: Γ | B ⟧∅))
    else if mode_eqb m mProp
    then cstar
    else ⟦ mx :: Γ | B ⟧ε ;
  ⟦ Γ | lam mx A B t ⟧ε :=
    if mode_inb mx [ mProp ; mGhost ]
    then ⟦ mx :: Γ | t ⟧ε
    else clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧ε ;
  ⟦ Γ | app u v ⟧ε :=
    if mode_inb (md Γ v) [ mProp ; mGhost ]
    then ⟦ Γ | u ⟧ε
    else capp ⟦ Γ | u ⟧ε ⟦ Γ | v ⟧ε ;
  ⟦ Γ | Erased A ⟧ε := ⟦ Γ | A ⟧ε ;
  ⟦ Γ | revealP t P ⟧ε := cstar ;
  ⟦ Γ | gheq A u v ⟧ε := cstar ;
  ⟦ Γ | ghcast e P t ⟧ε := ⟦ Γ | t ⟧ε ;
  ⟦ Γ | bot ⟧ε := cstar ;
  ⟦ Γ | bot_elim m A p ⟧ε := ⟦ Γ | A ⟧∅ ;
  ⟦ _ | _ ⟧ε := cDummy
}
where "⟦ G | u '⟧ε'" := (erase G u)
where "⟦ G | u '⟧τ'" := (cEl ⟦ G | u ⟧ε)
where "⟦ G | u '⟧∅'" := (cErr ⟦ G | u ⟧ε).

Reserved Notation "⟦ G '⟧ε'" (at level 0, G at next level).

Equations erase_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧ε := [] ;
  ⟦ Γ ,, (mx, A) ⟧ε :=
    if mode_inb mx [ mProp ; mGhost ]
    then ⟦ Γ ⟧ε
    else (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
}
where "⟦ G '⟧ε'" := (erase_ctx G).

(** Erasure commutes with substitution **)

Ltac destruct_if e :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn: e
  end.

(* TODO WRONG, σ should be filtered to remove stuff in Ghost or Prop mode. *)
Lemma erase_subst :
  ∀ Γ Δ σ t,
    ⟦ Γ | t <[ σ ] ⟧ε = ⟦ Δ | t ⟧ε <[ σ >> erase Γ ].
Proof.
  intros Γ Δ σ t.
  funelim (erase Δ t).
  (* induction t in Γ, Δ, σ |- *. *)
  all: try solve [ asimpl ; cbn ; eauto ].
  - (* Not making much progress, should I do the if directly in Equations? *)
  (* - asimpl. cbn. destruct m. all: cbn. all: reflexivity.
  - asimpl. cbn - [mode_inb mode_inclb].
    destruct_if e.
    + cbn. asimpl. repeat unfold_funcomp. f_equal.
      * erewrite IHt1. f_equal.
        erewrite IHt2. f_equal.
        substify. instantiate (1 := m0 :: Δ). asimpl.
        (* eapply subst_term_morphism2. *)
        f_equal. asimpl. unfold_funcomp.
        (* I'm a bit lost... *)
        admit.
      * erewrite IHt1. f_equal.
        erewrite IHt2. f_equal. instantiate (1 := m0 :: Δ).
        asimpl.
        admit.
    + destruct_if e'.
      * cbn. erewrite IHt1. f_equal. all: admit.
      * admit. *)
    admit.
  - admit.
  - cbn - [mode_inb]. destruct (mode_inb (md _ v) _) eqn:e.
    + (* Need scoping information probably *)
      admit.
    + admit.
Abort.

(** Erasure preserves conversion **)

Lemma erase_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | u ⟧ε ≡ ⟦ sc Γ | v ⟧ε.
Proof.
  intros Γ u v h.
  induction h.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    destruct (mode_inb _ _) eqn:e1.
    + (* TODO Need proper erasure subst lemma *) admit.
    + eapply cconv_trans. 1: econstructor.
      admit.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    cbn.
    (* TODO WRONG

      I can see two options:
      - Concluding only on stuff with the right relevance.
      - Producing clever garbage when erasing irrelevant stuff.
        Like erase reveal t P p to capp (erase p) (erase t).

      Maybe having the restriction is better?
      Let's move on to typing instead to get the right expectations.

     *)
Abort.

(* TODO MOVE *)

Lemma ccmeta_conv :
  ∀ Γ t A B,
    Γ ⊢ᶜ t : A →
    A = B →
    Γ ⊢ᶜ t : B.
Proof.
  intros. subst. assumption.
Qed.

(** Erasure preserves typing **)

Theorem erase_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | t ⟧ε : ⟦ sc Γ | A ⟧τ.
Proof.
  intros Γ t A h.
  induction h.
  - cbn. eapply ccmeta_conv.
    + econstructor. (* TODO Need a lemma, but translatin of variables is wrong
      we need to filter for removed variables in the context.
     *)
Abort.

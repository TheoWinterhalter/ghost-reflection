From Coq Require Import Utf8 List Bool.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping Scoping
  CTyping TermMode Typing BasicMetaTheory.
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

Notation irrm m :=
  (mode_inb m [ mProp ; mGhost ]).

(** Test whether a variable is relevant **)

Definition relv (Γ : scope) x :=
  negb (irrm (nth x Γ mType)).

(** Erasure for a variable

  It needs to skip over variables in scope that are erased.
  When the variable is meant to be erased or not in scope, it returns 0
  so that all ill-scoped or irrelevant term are erased to cvar 0 (cDummy).

**)

Fixpoint erase_var (Γ : scope) (x : nat) : nat :=
  match Γ, x with
  | m :: Γ, S x => if irrm m then erase_var Γ x else S (erase_var Γ x)
  | _, _ => 0
  end.

Reserved Notation "⟦ G | u '⟧ε'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧τ'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧∅'" (at level 9, G, u at next level).

Equations erase_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧ε := if relv Γ x then cvar (erase_var Γ x) else cDummy ;
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
    if irrm mx
    then ⟦ mx :: Γ | t ⟧ε
    else if irrm (md (mx :: Γ) t)
    then cDummy
    else clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧ε ;
  ⟦ Γ | app u v ⟧ε :=
    if irrm (md Γ v)
    then ⟦ Γ | u ⟧ε
    else if irrm (md Γ u)
    then cDummy
    else capp ⟦ Γ | u ⟧ε ⟦ Γ | v ⟧ε ;
  ⟦ Γ | Erased A ⟧ε := ⟦ Γ | A ⟧ε ;
  ⟦ Γ | revealP t P ⟧ε := cstar ;
  ⟦ Γ | gheq A u v ⟧ε := cstar ;
  ⟦ Γ | ghcast e P t ⟧ε := ⟦ Γ | t ⟧ε ;
  ⟦ Γ | bot ⟧ε := cstar ;
  ⟦ Γ | bot_elim m A p ⟧ε := if irrm m then cDummy else ⟦ Γ | A ⟧∅ ;
  ⟦ _ | _ ⟧ε := cDummy
}
where "⟦ G | u '⟧ε'" := (erase_term G u)
where "⟦ G | u '⟧τ'" := (cEl ⟦ G | u ⟧ε)
where "⟦ G | u '⟧∅'" := (cErr ⟦ G | u ⟧ε).

Reserved Notation "⟦ G '⟧ε'" (at level 9, G at next level).

Equations erase_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧ε := [] ;
  ⟦ Γ ,, (mx, A) ⟧ε :=
    if irrm mx
    then ⟦ Γ ⟧ε
    else (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
}
where "⟦ G '⟧ε'" := (erase_ctx G).

(* TODO MOVE *)

Ltac destruct_if e :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn: e
  end.

(** Erasure of irrelevant terms is cDummy **)

Lemma erase_irr :
  ∀ Γ t,
    irrm (md Γ t) = true →
    ⟦ Γ | t ⟧ε = cDummy.
Proof.
  intros Γ t hm.
  induction t in Γ, hm |- *.
  all: try reflexivity.
  all: try discriminate hm.
  - cbn - [mode_inb] in *. unfold relv. rewrite hm.
    reflexivity.
  - cbn - [mode_inb] in *.
    destruct_if em. 1: eauto.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    destruct_if em. 1: eauto.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *. eauto.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
Qed.

(** Erasure of context and of variables **)

Lemma erase_ctx_var :
  ∀ Γ x m A,
    nth_error Γ x = Some (m, A) →
    irrm m = false →
    nth_error ⟦ Γ ⟧ε (erase_var (sc Γ) x) =
    Some (cType, ⟦ skipn (S x) (sc Γ) | A ⟧τ).
  intros Γ x m A e hr.
Proof.
  induction Γ as [| [my B] Γ ih ] in x, m, A, e, hr |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn - [mode_inb]. rewrite hr. reflexivity.
  - cbn in e. cbn - [mode_inb skipn]. destruct (mode_inb my _) eqn:ey.
    + erewrite ih. 2,3: eauto. reflexivity.
    + cbn - [mode_inb skipn]. erewrite ih. 2,3: eauto. reflexivity.
Qed.

(** Erasure commutes with weakening **)

Lemma erase_var_weakening :
  ∀ Γ x y mx,
    nth_error Γ x = Some mx →
    irrm mx = false →
    erase_var Γ (S (x + y)) = S (erase_var Γ x + erase_var Γ y).
Proof.
  intros Γ x y mx hx hmx.
  (* cbn - [mode_inb]. destruct Γ as [| m Γ].
  - destruct x, y. all: cbn. all: reflexivity.
  - destruct (irrm m) eqn:e.
    + destruct x.
      1:{ cbn in hx. noconf hx. congruence. }
      cbn in hx. cbn - [mode_inb]. rewrite e.
      destruct y.
      * cbn - [mode_inb]. destruct Γ as [| m' Γ].
        -- destruct x. all: reflexivity.
        -- destruct (irrm m') eqn:e'.
          ++ destruct x.
            ** cbn - [mode_inb]. *) (* Right, so I need more info. *)
            (* **
          ++
      *
    + *)
Abort.

Lemma erase_weakening :
  ∀ Γ t x mx,
    nth_error Γ x = Some mx →
    irrm mx = false →
    ⟦ Γ | (λ m, S (x + m)) ⋅ t ⟧ε = (λ m, S (erase_var Γ x + m)) ⋅ ⟦ Γ | t ⟧ε.
Proof.
  intros Γ t x mx hx hmx.
  funelim (⟦ Γ | t ⟧ε).
  all: try solve [ asimpl ; cbn ; eauto ].
  - asimpl. cbn - [erase_var].
    destruct_if e.
    + destruct_if e'.
      * asimpl. cbn. repeat unfold_funcomp.
        f_equal. (* Now more hyps for the lemma above! *)
        admit.
      * asimpl. cbn. repeat unfold_funcomp.
        f_equal. (* Contradiction in hyps here, so probably wrong destruct *)
        admit.
Abort.

(** Erasure commutes with substitution **)

(* TODO WRONG, σ should be filtered to remove stuff in Ghost or Prop mode. *)
Lemma erase_subst :
  ∀ Γ Δ σ t,
    ⟦ Γ | t <[ σ ] ⟧ε = ⟦ Δ | t ⟧ε <[ σ >> erase_term Γ ].
Proof.
  intros Γ Δ σ t.
  funelim (erase_term Δ t).
  (* induction t in Γ, Δ, σ |- *. *)
  all: try solve [ asimpl ; cbn ; eauto ].
  - admit.
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
    irrm (mdc Γ t) = false →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | t ⟧ε : ⟦ sc Γ | A ⟧τ.
Proof.
  intros Γ t A h hm.
  induction h.
  - cbn. unfold relv. cbn - [mode_inb] in hm. rewrite hm.
    cbn. eapply ccmeta_conv.
    + econstructor. eapply erase_ctx_var. 1: eassumption.
      erewrite nth_error_nth in hm.
      2:{ unfold sc. erewrite nth_error_map. erewrite H. reflexivity. }
      assumption.
    + cbn - [skipn]. f_equal.
      erewrite nth_error_nth in hm.
      2:{ unfold sc. rewrite nth_error_map. rewrite H. reflexivity. }
      cbn - [mode_inb] in hm.
Abort.

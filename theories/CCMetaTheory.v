(** Basic meta-theory of the target CC **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CScoping
  CTyping.
From Coq Require Import Setoid Morphisms Relation_Definitions.

From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Definition crscoping (Γ : cscope) (ρ : nat → nat) (Δ : cscope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some m →
    nth_error Γ (ρ x) = Some m.

Inductive csscoping (Γ : cscope) (σ : nat → cterm) : cscope → Prop :=
| cscope_nil : csscoping Γ σ []
| cscope_cons :
    ∀ Δ om,
      csscoping Γ (↑ >> σ) Δ →
      whenSome (ccscoping Γ (σ 0)) om →
      csscoping Γ σ (om :: Δ).

Lemma crscoping_S :
  ∀ Γ o,
    crscoping (o :: Γ) S Γ.
Proof.
  intros Γ o. intros x mx e.
  cbn. assumption.
Qed.

Lemma crscoping_shift :
  ∀ Γ Δ ρ mx,
    crscoping Γ ρ Δ →
    crscoping (mx :: Γ) (0 .: ρ >> S) (mx :: Δ).
Proof.
  intros ? ? ? mx h' y my e.
  destruct y.
  - simpl in *. assumption.
  - simpl in *. apply h'. assumption.
Qed.

Lemma cscoping_ren :
  ∀ Γ Δ ρ t m,
    crscoping Γ ρ Δ →
    ccscoping Δ t m →
    ccscoping Γ (ρ ⋅ t) m.
Proof.
  intros Γ Δ ρ t m hρ ht.
  pose proof crscoping_shift as lem.
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ asimpl ; econstructor ; eauto ].
Qed.

Lemma csscoping_weak :
  ∀ Γ Δ σ m,
    csscoping Γ σ Δ →
    csscoping (m :: Γ) (σ >> ren_cterm ↑) Δ.
Proof.
  intros Γ Δ σ m h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + destruct om. 2: eauto.
      cbn in *. eapply cscoping_ren. 2: eassumption.
      apply crscoping_S.
Qed.

Lemma cscoping_subst :
  ∀ Γ Δ σ t m,
    csscoping Γ σ Δ →
    ccscoping Δ t m →
    ccscoping Γ (t <[ σ ]) m.
Proof.
  intros Γ Δ σ t m hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ].
  - rename H into hx, Γ0 into Δ.
    asimpl. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
    destruct x.
    + simpl in *. inversion hx. subst. assumption.
    + apply IHhσ. simpl in hx. assumption.
  - asimpl. constructor.
    eapply IHht. constructor.
    + asimpl. apply csscoping_weak. assumption.
    + constructor.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply csscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply csscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
Qed.

Lemma csscoping_shift :
  ∀ Γ Δ mx σ,
    csscoping Γ σ Δ →
    csscoping (mx :: Γ) (cvar 0 .: σ >> ren1 S) (mx :: Δ).
Proof.
  intros Γ Δ mx σ h.
  constructor.
  - asimpl. apply csscoping_weak. assumption.
  - destruct mx. 2: constructor.
    cbn. constructor. reflexivity.
Qed.

(* TODO forall_iff_impl should be moved to utils! *)

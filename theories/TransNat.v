(*** Translation for natural numbers

  Building terms for inductive types and their translations is very
  time consuming so instead we opt for a more synthetic approach where we build
  those terms in Coq in order to justify that we could have built them by hand.

  TODO: Should we keep all the El stuff, not sure what's the best strategy
  here.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory CScoping CTyping
  CCMetaTheory Admissible Erasure Revival Param Model.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.

Transparent close ignore epm_lift rpm_lift.

(** We first define ty and various other types **)

Inductive ty@{i} :=
| tyval (mk : mark) (A : Type@{i}) (a : A)
| tyerr.

Definition El@{i} (T : ty@{i}) : Type@{i} :=
  match T with
  | tyval mk A a => A
  | tyerr => unit
  end.

Definition Err@{i} T : El@{i} T :=
  match T with
  | tyval mk A a => a
  | tyerr => tt
  end.

Definition erase_pi@{i j k} (A : ty@{i}) (B : El A → ty@{j}) : ty@{k} :=
  tyval Any (∀ x, El (B x)) (λ x, Err (B x)).

Definition erase_Type@{i si} :=
  tyval@{si} Any ty@{i} tyerr@{i}.

(** Recall the definition of natural numbers **)

Succeed Inductive nat :=
| O
| S (n : nat).

(** Erasure

  To define erasure of nat, we introduce an inductive type with errors.

**)

Inductive err_nat : Set :=
| err_O
| err_S (n : err_nat)
| nat_err.

Definition erase_nat :=
  tyval@{Set} Any err_nat nat_err.

Definition erase_O : El erase_nat :=
  err_O.

Definition erase_S : El (erase_pi erase_nat (λ _, erase_nat)) :=
  err_S.

Lemma err_nat_elim@{i si} :
  El@{si} (
    erase_pi@{si i si} (erase_pi@{Set si si} erase_nat (λ _, erase_Type@{i si})) (λ P,
      erase_pi@{i i i} (P erase_O) (λ _,
        erase_pi@{i i i} (erase_pi@{Set i i} erase_nat (λ n, erase_pi@{i i i} (P n) (λ _, P (erase_S n)))) (λ _,
          erase_pi@{Set i i} erase_nat (λ n, P n)
        )
      )
    )
  ).
Proof.
  cbn. intros P z s n.
  induction n.
  - assumption.
  - apply s. assumption.
  - apply Err.
Defined.

(** Computation rules **)

Lemma err_nat_elim_O :
  ∀ P z s,
    err_nat_elim P z s erase_O = z.
Proof.
  reflexivity.
Qed.

Lemma err_nat_elim_S :
  ∀ P z s n,
    err_nat_elim P z s (erase_S n) = s n (err_nat_elim P z s n).
Proof.
  reflexivity.
Qed.

(** Parametricity **)

Inductive pm_nat : err_nat → SProp :=
| pm_O : pm_nat err_O
| pm_S : ∀ n, pm_nat n → pm_nat (err_S n).

Lemma pm_nat_elim :
  ∀ (Pe : err_nat → ty) (PP : ∀ n (nP : pm_nat n), El (Pe n) → SProp)
    (ze : El (Pe err_O)) (zP : PP err_O pm_O ze)
    (se : ∀ n, El (Pe n) → El (Pe (err_S n)))
    (sP : ∀ n nP (h : El (Pe n)) (hP : PP n nP h), PP (err_S n) (pm_S n nP) (se _ h))
    n (nP : pm_nat n),
    PP n nP (err_nat_elim Pe ze se n).
Proof.
  intros Pe PP ze zP se sP n nP.
  induction nP.
  - cbn. assumption.
  - cbn. eapply sP. assumption.
Qed.

Lemma pm_nat_elim_Prop :
  ∀ (Pe : err_nat → unit) (PP : ∀ n (nP : pm_nat n), SProp)
    (z : PP err_O pm_O)
    (s : ∀ n nP (h : PP n nP), PP (err_S n) (pm_S n nP))
    n (nP : pm_nat n),
    PP n nP.
Proof.
  intros Pe PP z s n nP.
  induction nP. all: eauto.
Qed.

(** Computation rules are trivial because we are in SProp **)

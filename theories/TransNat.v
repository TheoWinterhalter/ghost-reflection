(*** Translation for natural numbers

  Building terms for inductive types and their translations is very
  time consuming so instead we opt for a more synthetic approach where we build
  those terms in Coq in order to justify that we could have built them by hand.

  We import here the various translations to serve as a guide. (TODO?)

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

Definition Err T : El T :=
  match T with
  | tyval mk A a => a
  | tyerr => tt
  end.

Definition erase_pi A (B : El A → ty) :=
  tyval Any (∀ x, El (B x)) (λ x, Err (B x)).

Definition erase_Type :=
  tyval Any ty tyerr.

(** Recall the definition of natural numbers **)

Succeed Inductive nat :=
| O
| S (n : nat).

(** Erasure

  To define erasure of nat, we introduce an inductive type with errors.

**)

Inductive err_nat :=
| err_O
| err_S (n : err_nat)
| nat_err.

Definition erase_nat :=
  tyval Any err_nat nat_err.

Definition erase_O : El erase_nat :=
  err_O.

Definition erase_S : El (erase_pi erase_nat (λ _, erase_nat)) :=
  err_S.

Lemma err_nat_elim :
  El (
    erase_pi (erase_pi erase_nat (λ _, erase_Type)) (λ P,
      erase_pi (P erase_O) (λ _,
        erase_pi (erase_pi erase_nat (λ n, erase_pi (P n) (λ _, P (erase_S n)))) (λ _,
          erase_pi erase_nat (λ n, P n)
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

(* TODO: We need also the Prop version of the eliminator?
  Or rather no because erasure?
*)

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

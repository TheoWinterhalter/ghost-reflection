(*** Translation for vectors

  We can't really express our vectors with a ghost index in Coq so we're
  going to write it in pseudo-Coq.

  Inducitve vec (A : Type) : erased nat → Type :=
  | vnil : vec A (hide 0)
  | vcons (a : A) (n : erased nat) (v : vec A n) : vec A (gS n).

  Where gS : erased nat → erased nat is the lift of the successor function:
  gS (hide n) := hide (S n)

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory CScoping CTyping
  CCMetaTheory Admissible Erasure Revival Param Model TransNat.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.

Transparent close ignore epm_lift rpm_lift.

(** Erasure **)

Inductive err_vec (A : ty) :=
| err_vnil
| err_vcons (a : El A) (v : err_vec A)
| vec_err.

Arguments err_vnil {A}.
Arguments err_vcons {A}.

Lemma err_vec_elim :
  ∀ (A : ty) (P : err_vec A → ty)
    (z : El (P err_vnil))
    (s : ∀ (a : El A) (v : err_vec A), El (P v) → El (P (err_vcons a v)))
    (v : err_vec A),
    El (P v).
Proof.
  intros A P z s v.
  induction v.
  - assumption.
  - apply s. assumption.
  - apply Err.
Defined.

(** Computation rules **)

Lemma err_vec_elim_vnil :
  ∀ A P z s,
    err_vec_elim A P z s err_vnil = z.
Proof.
  reflexivity.
Qed.

Lemma err_vec_elim_vcons :
  ∀ A P z s a v,
    err_vec_elim A P z s (err_vcons a v) = s a v (err_vec_elim A P z s v).
Proof.
  reflexivity.
Qed.

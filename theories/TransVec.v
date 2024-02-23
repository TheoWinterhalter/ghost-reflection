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

(** Parametricity **)

Inductive pm_vec (A : ty) (AP : El A → SProp) : ∀ n (nP : pm_nat n), err_vec A → SProp :=
| pm_vnil : pm_vec A AP err_O pm_O err_vnil
| pm_vcons a (aP : AP a) n nP v :
    pm_vec A AP n nP v →
    pm_vec A AP (err_S n) (pm_S n nP) (err_vcons a v).

Arguments pm_vnil {A AP}.
Arguments pm_vcons {A AP}.

Lemma pm_vec_elim :
  ∀ A (AP : El A → SProp)
    (Pe : err_vec A → ty)
    (PP : ∀ n nP (v : err_vec A) (vP : pm_vec A AP n nP v), El (Pe v) → SProp)
    (ze : El (Pe err_vnil)) (zP : PP err_O pm_O err_vnil pm_vnil ze)
    (se : ∀ (a : El A) (v : err_vec A), El (Pe v) → El (Pe (err_vcons a v)))
    (sP :
      ∀ a aP n nP v vP (h : El (Pe v)) (hP : PP n nP v vP h),
        PP (err_S n) (pm_S n nP) (err_vcons a v) (pm_vcons a aP n nP v vP) (se a v h)
    )
    n nP v vP,
    PP n nP v vP (err_vec_elim A Pe ze se v).
Proof.
  intros A AP Pe PP ze zP se sP n nP v vP.
  induction vP. all: eauto.
Qed.

Lemma pm_vec_elim_Prop :
  ∀ A (AP : El A → SProp)
    (Pe : err_vec A → unit)
    (PP : ∀ n nP (v : err_vec A) (vP : pm_vec A AP n nP v), SProp)
    (z : PP err_O pm_O err_vnil pm_vnil)
    (s :
      ∀ a aP n nP v vP (h : PP n nP v vP),
        PP (err_S n) (pm_S n nP) (err_vcons a v) (pm_vcons a aP n nP v vP)
    )
    n nP v vP,
    PP n nP v vP.
Proof.
  intros A AP Pe PP z s n nP v vP.
  induction vP. all: eauto.
Qed.

(** Computation rules are trivial because we are in SProp **)

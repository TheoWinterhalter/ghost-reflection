From Coq Require Import Utf8 List.
From Equations Require Import Equations.

From GhostTT.autosubst Require Import GAST.
From GhostTT Require Import Util BasicAST ContextDecl Scoping.

Import ListNotations.

Set Default Goal Selector "!".

(** Reads the mode of a term.

  The mode of a variable comes from the scope.

 **)

Section Mode.

  Let dummy := mType.

  Fixpoint md (Γ : scope) (t : term) : mode :=
    match t with
    | var x => nth x Γ dummy
    | Sort m l => mKind
    | Pi i j m mx A B => mKind
    | lam mx A B t => md (mx :: Γ) t
    | app u v => md Γ u
    | Erased A => mKind
    | hide t => mGhost
    | reveal t P p =>
      match md Γ p with
      | mGhost => mGhost
      | _ => mProp
      end
    | Reveal t p => mKind
    | toRev t p u => mProp
    | fromRev t p u => mProp
    | gheq A u v => mKind
    | ghrefl A u => mProp
    | ghcast A u v e P t => md Γ t
    | tbool => mKind
    | ttrue => mType
    | tfalse => mType
    | tif m b P t f => m
    | bot => mKind
    | bot_elim m A p => m
    end.

End Mode.

(* Handy notation for the mode in a context *)

Notation mdc Γ t := (md (sc Γ) t).

(** Relation with scoping **)

Lemma scoping_md :
  ∀ Γ t m,
    scoping Γ t m →
    md Γ t = m.
Proof.
  intros Γ t m h.
  induction h. all: try reflexivity. all: try solve [ auto ].
  - simpl. eapply nth_error_nth. assumption.
  - simpl. rewrite IHh3. cbn in *. intuition eauto.
    + rewrite <- H0. reflexivity.
    + rewrite <- H. reflexivity.
Qed.

(** Consequence: scoping is functional **)

Lemma scoping_functional :
  ∀ Γ t m m',
    scoping Γ t m →
    scoping Γ t m' →
    m = m'.
Proof.
  intros Γ t m m' h h'.
  eapply scoping_md in h, h'. congruence.
Qed.

(** Useful tools **)

Definition mode_eqb (m m' : mode) : bool :=
  match m, m' with
  | mProp, mProp
  | mGhost, mGhost
  | mType, mType
  | mKind, mKind => true
  | _,_ => false
  end.

Definition isProp m := mode_eqb m mProp.
Definition isGhost m := mode_eqb m mGhost.
Definition isType m := mode_eqb m mType.
Definition isKind m := mode_eqb m mKind.

Lemma isKind_eq :
  ∀ m, isKind m = true → m = mKind.
Proof.
  intros [] e. all: try discriminate.
  reflexivity.
Qed.

Lemma isType_eq :
  ∀ m, isType m = true → m = mType.
Proof.
  intros [] e. all: try discriminate.
  reflexivity.
Qed.

Lemma isGhost_eq :
  ∀ m, isGhost m = true → m = mGhost.
Proof.
  intros [] e. all: try discriminate.
  reflexivity.
Qed.

Lemma isProp_eq :
  ∀ m, isProp m = true → m = mProp.
Proof.
  intros [] e. all: try discriminate.
  reflexivity.
Qed.

Ltac mode_eqs :=
  repeat lazymatch goal with
  | e : isKind ?m = true |- _ => eapply isKind_eq in e ; try subst m
  | e : isType ?m = true |- _ => eapply isType_eq in e ; try subst m
  | e : isGhost ?m = true |- _ => eapply isGhost_eq in e ; try subst m
  | e : isProp ?m = true |- _ => eapply isProp_eq in e ; try subst m
  end.

Definition mode_inb := inb mode_eqb.

Notation relm m :=
  (mode_inb m [ mType ; mKind ]).

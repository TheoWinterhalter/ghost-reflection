From Coq Require Import Utf8 List.
From Equations Require Import Equations.

From GhostTT.autosubst Require Import GAST.
From GhostTT Require Import BasicAST ContextDecl Scoping.

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

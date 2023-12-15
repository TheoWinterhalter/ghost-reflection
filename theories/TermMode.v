From Coq Require Import Utf8 List.
From Equations Require Import Equations.

From GhostTT.autosubst Require Import AST.
From GhostTT Require Import BasicAST ContextDecl.

Set Default Goal Selector "!".

(** Reads the mode of a term.

  The mode of a variable comes from the context, assuming the term is well
  scoped.

 **)

Section Mode.

  Context (Γ : context).

  Let dummy := (mType, var 0).

  Fixpoint md (t : term) : mode :=
    match t with
    | var x => fst (nth x Γ dummy)
    | Sort m l => mKind
    | Pi m mx A B => mKind
    | lam A t => md t
    | app u v => md u
    | Erased A => mKind
    | erase t => mGhost
    | reveal t P p =>
      match md p with
      | mGhost => mGhost
      | _ => mProp
      end
    | revealP t p => mKind
    | gheq A u v => mKind
    | ghrefl A u => mProp
    | ghcast e P t => md t
    | bot => mKind
    | bot_elim m A p => m
    end.

End Mode.

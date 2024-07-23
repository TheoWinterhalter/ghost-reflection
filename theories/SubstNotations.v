(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import core unscoped GAST CCAST.
Import ListNotations.

Notation "a ⋅ x" :=
  (ren1 a x) (at level 20, right associativity) : subst_scope.

Notation "t <[ s ]" :=
  (subst1 s t) (at level 10, right associativity) : subst_scope.

Notation "↑" := (shift) : subst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Ltac autosubst_unfold :=
  unfold Ren_cterm, upRen_cterm_cterm, Subst_cterm, VarInstance_cterm,
    upRen_cterm_cterm, Ren_term, Subst_term, VarInstance_term, upRen_term_term.

Ltac resubst :=
  rewrite ?renRen_cterm, ?renSubst_cterm, ?substRen_cterm, ?substSubst_cterm,
    ?renRen_term, ?renSubst_term, ?substRen_term, ?substSubst_term.

Ltac ssimpl :=
  asimpl ;
  autosubst_unfold ;
  asimpl ;
  repeat unfold_funcomp ;
  resubst ;
  asimpl ;
  repeat unfold_funcomp.

(** Autosubst reflective tactic that should be more efficient than asimpl **)

Inductive quoted_ren :=
| qren_atom (ρ : nat → nat)
| qren_comp (r q : quoted_ren)
| qren_cons (n : nat) (q : quoted_ren)
| qren_id
| qren_shift.

Inductive quoted_subst :=
| qsubst_atom (σ : nat → cterm)
| qsubst_comp (s t : quoted_subst)
| qsubst_cons (t : cterm) (s : quoted_subst)
| qsubst_id.

Inductive quoted_cterm :=
| qatom (t : cterm)
| qren (r : quoted_ren) (t : quoted_cterm)
| qsubst (s : quoted_subst) (t : quoted_cterm).

Fixpoint unquote_ren q :=
  match q with
  | qren_atom ρ => ρ
  | qren_comp r q => funcomp (unquote_ren r) (unquote_ren q)
  | qren_cons n q => scons n (unquote_ren q)
  | qren_id => id
  | qren_shift => shift
  end.

Fixpoint unquote_subst q :=
  match q with
  | qsubst_atom σ => σ
  | qsubst_comp s t => funcomp (subst_cterm (unquote_subst s)) (unquote_subst t)
  | qsubst_cons t s => scons t (unquote_subst s)
  | qsubst_id => ids
  end.

Fixpoint unquote_cterm q :=
  match q with
  | qatom t => t
  | qren r t => ren_cterm (unquote_ren r) (unquote_cterm t)
  | qsubst s t => subst_cterm (unquote_subst s) (unquote_cterm t)
  end.

(** Evaluation **)

Fixpoint eval_ren (r : quoted_ren) :=
  match r with
  | qren_comp r q =>
    let r := eval_ren r in
    let q := eval_ren q in
    match r, q with
    | qren_id, _ => q
    | _, qren_id => r
    | qren_cons n r, qren_shift => r
    | _, qren_comp u v => qren_comp (qren_comp r u) v
    | _, qren_cons n q => qren_cons (unquote_ren r n) (qren_comp r q)
    | _, _ => qren_comp r q
    end
  | qren_cons 0 qren_shift => qren_id
  | _ => r
  end.

Fixpoint eval_subst (s : quoted_subst) : quoted_subst :=
  match s with
  | qsubst_comp u v =>
    let u := eval_subst u in
    let v := eval_subst v in
    match u, v with
    | qsubst_id, _ => v
    | _, qsubst_id => u
    | _, qsubst_comp x y => qsubst_comp (qsubst_comp u x) y
    | _, qsubst_cons t s =>
      qsubst_cons (subst_cterm (unquote_subst s) t) (qsubst_comp u s)
    | _, _ => qsubst_comp u v
    end
  | _ => s
  end.

Fixpoint eval_cterm (t : quoted_cterm) : quoted_cterm :=
  match t with
  | qren r t =>
    let r := eval_ren r in
    let t := eval_cterm t in
    match t with
    | qren r' t => qren (qren_comp r' r) t
    | _ => qren r t
    end
  | qsubst s t =>
    let s := eval_subst s in
    let t := eval_cterm t in
    match t with
    | qsubst s' t => qsubst (qsubst_comp s' s) t
    | _ => qsubst s t
    end
  | _ => t
  end.

(** Correctness **)

Lemma eval_ren_sound :
  ∀ r n,
    unquote_ren r n = unquote_ren (eval_ren r) n.
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  (* TODO Maybe funelim instead *)
Admitted.

Lemma eval_subst_sound :
  ∀ s n,
    unquote_subst s n = unquote_subst (eval_subst s) n.
Proof.
Admitted.

Lemma eval_cterm_sound :
  ∀ t,
    unquote_cterm t = unquote_cterm (eval_cterm t).
Proof.
Admitted.

(** Quoting **)

Ltac quote_ren r :=
  lazymatch r with
  | funcomp ?r ?r' =>
    let q := quote_ren r in
    let q' := quote_ren r' in
    constr:(qren_comp q q')
  | scons ?n ?r =>
    let q := quote_ren r in
    constr:(qren_cons n q)
  | id => constr:(qren_id)
  | shift => constr:(qren_shift)
  | S => constr:(qren_shift)
  | _ => constr:(qren_atom r)
  end.

Ltac quote_subst s :=
  lazymatch s with
  | funcomp (subst_cterm ?s) ?t =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | scons ?t ?s =>
    let q := quote_subst s in
    constr:(qsubst_cons t q)
  | ids => constr:(qsubst_id)
  | _ => constr:(qsubst_atom s)
  end.

Ltac quote_cterm t :=
  lazymatch t with
  | ren1 ?r ?t =>
    let qr := quote_ren r in
    let qt := quote_cterm t in
    constr:(qren qr qt)
  | ren_cterm ?r ?t =>
    let qr := quote_ren r in
    let qt := quote_cterm t in
    constr:(qren qr qt)
  | subst1 ?s ?t =>
    let qs := quote_subst s in
    let qt := quote_cterm t in
    constr:(qsubst qs qt)
  | subst_cterm ?s ?t =>
    let qs := quote_subst s in
    let qt := quote_cterm t in
    constr:(qsubst qs qt)
  | _ => constr:(qatom t)
  end.

(** Main tactic **)

Ltac rasimpl1 :=
  match goal with
  | |- context G[ ?t ] =>
    let q := quote_cterm t in
    change t with (unquote_cterm q) ;
    rewrite eval_cterm_sound ;
    cbn [
      unquote_cterm eval_cterm
      unquote_ren eval_ren
      unquote_subst eval_subst
      ren_cterm subst_cterm
    ]
  end.

Ltac rasimpl :=
  repeat rasimpl1.

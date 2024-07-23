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

(** Autosubst NbE tactic that should be more efficient than asimpl/ssimpl

  We reproduce what asimpl' does first:
  - Make sure each term only has at most one substitution ore renaming applied
    to it, resorting to composition instead.
  - Apply renamings and substitutions to variables.
  - Get rid of identity renamings and substitutions.
  - Calls fsimpl to simplify expressions.

**)

About substSubst_cterm_pointwise.
About substSubst_cterm.
About substRen_cterm_pointwise.
About substRen_cterm.
About renSubst_cterm_pointwise.
About renSubst_cterm.
About renRen'_cterm_pointwise.
About renRen_cterm.
About varLRen'_cterm_pointwise.
About varLRen'_cterm.
About varL'_cterm_pointwise.
About varL'_cterm.
About rinstId'_cterm_pointwise.
About rinstId'_cterm.
About instId'_cterm_pointwise.
About instId'_cterm.

Print up_cterm_cterm.
Print upRen_cterm_cterm.
Print up_ren.

Print funcomp.

Inductive quoted_ren :=
| qren_atom (ρ : nat → nat)
| qren_comp (r q : quoted_ren).

Inductive quoted_subst :=
| qsubst_atom (σ : nat → cterm)
| qsubst_comp (s t : quoted_subst).

Inductive quoted_cterm :=
| qmeta (t : cterm)
| qren (r : quoted_ren) (t : quoted_cterm)
| qsubst (s : quoted_subst) (t : quoted_cterm).

Fixpoint unquote_ren q :=
  match q with
  | qren_atom ρ => ρ
  | qren_comp r q => funcomp (unquote_ren r) (unquote_ren q)
  end.

Fixpoint unquote_subst q :=
  match q with
  | qsubst_atom σ => σ
  | qsubst_comp s t => funcomp (subst_cterm (unquote_subst s)) (unquote_subst t)
  end.

Fixpoint unquote_cterm q :=
  match q with
  | qmeta t => t
  | qren r t => ren1 (unquote_ren r) (unquote_cterm t)
  | qsubst s t => subst1 (unquote_subst s) (unquote_cterm t)
  end.

(** A substitution/renaming is first a sequence of conses and then a composition
    of atomic substitutions/renamings.

    TODO See where shifts end up.
*)

Definition normal_ren := (list nat * list (nat → nat))%type.

Definition normal_subst := (list cterm * list (nat → cterm))%type.

Definition normal_cterm := (normal_subst * cterm)%type.

Fixpoint apply_ren (r : list (nat → nat)) n :=
  match r with
  | [] => n
  | ρ :: r => ρ (apply_ren r n)
  end.

Definition apply_nren (r : normal_ren) (n : nat) :=
  let (l, r) := r in
  match nth_error l n with
  | Some x => x
  | None => apply_ren r (n - length l)
  end.

Definition nr_comp (u v : normal_ren) :=
  let '(ul, ur) := u in
  let '(vl, vr) := v in


Fixpoint nr_comp uc ur vc vr : normal_ren :=
  match vc with
  | [] => (uc, ur ++ vr)

Fixpoint nr_comp (u v : normal_ren) :=
  let (uc, ur) := u in
  let (vc, vr) := v in


Fixpoint ns_comp (u v : normal_subst) :=
  match u with
  | [] => v
  |
  end.

Fixpoint eval_ren q :=
  match q with
  | qren_atom ρ => [ sren ρ ]
  | qren_comp r q => eval_ren r ++ eval_ren q
  end.

Fixpoint eval_subst q :=
  match q with
  | qsubst_atom σ => [ ssubst σ ]
  | qsubst_comp s t => eval_subst s ++ eval_subst t
  end.

Fixpoint eval_cterm q : normal_cterm :=
  match q with
  | qmeta t => ([], t)
  | qren r t =>
    let r' := eval_ren r in
    let '(s',t') := eval_cterm t in
    (s' ++ r', t')
  | qsubst s t =>
    let s' := eval_subst s in
    let '(s'',t') := eval_cterm t in
    (s'' ++ s', t')
  end.

Inductive normal_subst :=
| nId
| nRen (ρ : nat → nat)
| nSubst (σ : nat → cterm).

Definition ns_comp (s t : normal_subst) :=
  match s, t with
  | nId, _ => t
  | _, nId => s
  | nRen ρ, nRen ρ' => nRen (funcomp ρ ρ')
  | nRen ρ, nSubst σ => nSubst (funcomp (ren_cterm ρ) σ)
  | nSubst σ, nRen ρ => nSubst (funcomp σ ρ)
  | nSubst σ, nSubst θ => nSubst (funcomp (subst_cterm σ) θ)
  end.

Definition nscons (t : cterm) s :=
  match s with
  | nId => nSubst (scons t cvar)
  | nRen ρ => nSubst (scons t (funcomp cvar ρ))
  | nSubst σ => nSubst (scons t σ)
  end.

(* TODO Instead of all this, have a better normal form than lists
  of sparts. Like scons should be primitive in it.
*)

Fixpoint reify_sparts (s : list spart) : normal_subst :=
  match s with
  | [] => nId
  | sren ρ :: s =>
    match reify_sparts s with
    | nId => nRen ρ
    | nRen ρ' => nRen (funcomp ρ ρ')
    | nSubst σ => nSubst (funcomp (ren_cterm ρ) σ)
    end
  | ssubst σ :: s =>
    match reify_sparts s with
    | nId => nSubst σ
    | nRen ρ => nSubst (funcomp σ ρ)
    | nSubst θ => nSubst (funcomp (subst_cterm σ) θ)
    end
  | sscons t k :: sshift :: s =>
    let k' := reify_sparts k in
    let s' := reify_sparts s in
    ns_comp k' s'
  | sscons t k :: s =>
    let k' := reify_sparts k in
    let s' := reify_sparts s in
    ns_comp (nscons t k') s'
  | sshift :: s =>
    let s' := reify_sparts s in
    ns_comp (nRen shift) s'
  end.

Fixpoint reify_spart (s : list spart) (t : cterm) : cterm :=
  match s with
  | [] => t
  | sren ρ ::

Definition reify (t : normal_cterm) : cterm :=
  let '(s,t) := t in
  reify_spart s t.

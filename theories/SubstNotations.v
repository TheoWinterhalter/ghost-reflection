(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.

**)

From Coq Require Import Utf8 List.
(* From Equations Require Import Equations. *)
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

Inductive quoted_nat :=
| qnat_atom (n : nat)
| q0
| qS (n : quoted_nat).

Inductive quoted_ren :=
| qren_atom (ρ : nat → nat)
| qren_comp (r q : quoted_ren)
| qren_cons (n : quoted_nat) (q : quoted_ren)
| qren_id
| qren_shift.

Inductive quoted_subst :=
| qsubst_atom (σ : nat → cterm)
| qsubst_comp (s t : quoted_subst)
| qsubst_compr (s : quoted_subst) (r : quoted_ren)
| qsubst_cons (t : cterm) (s : quoted_subst)
| qsubst_id
| qsubst_ren (r : quoted_ren).

Inductive quoted_cterm :=
| qatom (t : cterm)
| qren (r : quoted_ren) (t : quoted_cterm)
| qsubst (s : quoted_subst) (t : quoted_cterm).

Fixpoint unquote_nat q :=
  match q with
  | qnat_atom n => n
  | q0 => 0
  | qS n => S (unquote_nat n)
  end.

Fixpoint unquote_ren q :=
  match q with
  | qren_atom ρ => ρ
  | qren_comp r q => funcomp (unquote_ren r) (unquote_ren q)
  | qren_cons n q => scons (unquote_nat n) (unquote_ren q)
  | qren_id => id
  | qren_shift => shift
  end.

Fixpoint unquote_subst q :=
  match q with
  | qsubst_atom σ => σ
  | qsubst_comp s t => funcomp (subst_cterm (unquote_subst s)) (unquote_subst t)
  | qsubst_compr s r => funcomp (unquote_subst s) (unquote_ren r)
  | qsubst_cons t s => scons t (unquote_subst s)
  | qsubst_id => ids
  | qsubst_ren r => funcomp cvar (unquote_ren r)
  end.

Fixpoint unquote_cterm q :=
  match q with
  | qatom t => t
  | qren r t => ren_cterm (unquote_ren r) (unquote_cterm t)
  | qsubst s t => subst_cterm (unquote_subst s) (unquote_cterm t)
  end.

(** Evaluation **)

Fixpoint apply_ren (r : quoted_ren) (n : quoted_nat) : quoted_nat :=
  match r, n with
  | qren_atom ρ, _ => qnat_atom (ρ (unquote_nat n))
  | qren_id, _ => n
  | qren_shift, _ => qS n
  | _, qnat_atom n => qnat_atom (unquote_ren r n)
  | qren_comp r q, _ => apply_ren r (apply_ren q n)
  | qren_cons m q, q0 => m
  | qren_cons m q, qS n => apply_ren q n
  end.

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
    | _, qren_cons n q => qren_cons (apply_ren r n) (qren_comp r q)
    | _, _ => qren_comp r q
    end
  | qren_cons q0 qren_shift => qren_id
  | qren_cons n r =>
    let r := eval_ren r in
    qren_cons n r
  | _ => r
  end.

(* Equations eval_ren (r : quoted_ren) : quoted_ren :=
  eval_ren qr with qr := {
  | qren_comp r q with eval_ren r, eval_ren q := {
    | qren_id, _ => q
    | _, qren_id => r
    | qren_cons n r', qren_shift => r'
    | _, qren_comp u v => qren_comp (qren_comp r u) v
    | _, qren_cons n q' => qren_cons (apply_ren r n) (qren_comp r q')
    | _, _ => qren_comp r q
    }
  | qren_cons q0 qren_shift => qren_id
  | qren_cons n r with eval_ren r := {
    | r' => qren_cons n r
    }
  | _ => qr
  }. *)

(* Inductive eval_ren_view : quoted_ren → Type :=
| eval_ren_comp r q : eval_ren_view (qren_comp r q)
| eval_ren_cons_0_shift : eval_ren_view (qren_cons q0 qren_shift)
| eval_ren_cons n r : eval_ren_view (qren_cons n r)
| eval_ren_other r : eval_ren_view r.

Definition eval_ren_c r : eval_ren_view r :=
  match r as r return eval_ren_view r with
  | qren_comp r q => eval_ren_comp r q
  | qren_cons q0 qren_shift => eval_ren_cons_0_shift
  | qren_cons n r => eval_ren_cons n r
  | r => eval_ren_other r
  end.

Inductive eval_ren_comp_view : quoted_ren → quoted_ren → Type :=
| eval_ren_id_l q : eval_ren_comp_view qren_id q
| eval_ren_id_r r : eval_ren_comp_view r qren_id
| eval_ren_cons_shift n r : eval_ren_comp_view (qren_cons n r) qren_shift
| eval_ren_comp_r r u v : eval_ren_comp_view r (qren_comp u v)
| eval_ren_cons_r r n q : eval_ren_comp_view r (qren_cons n q)
| eval_ren_comp_other r q : eval_ren_comp_view r q.

Definition eval_ren_comp_c r q : eval_ren_comp_view r q :=
  match r, q with
  | qren_id, q => eval_ren_id_l q
  | r, qren_id => eval_ren_id_r r
  | qren_cons n r, qren_shift => eval_ren_cons_shift n r
  | r, qren_comp u v => eval_ren_comp_r r u v
  | r, qren_cons n q => eval_ren_cons_r r n q
  | r, q =>  eval_ren_comp_other r q
  end. *)

(* Equations eval_ren (r : quoted_ren) : quoted_ren :=
  eval_ren r with eval_ren_c r := {
  (* | eval_ren_comp r q with eval_ren_comp_c (eval_ren r) (eval_ren q) := {
    | eval_ren_id_l q => q ;
    | eval_ren_id_r r => r ;
    | eval_ren_cons_shift n r => r ;
    | eval_ren_comp_r r u v => qren_comp (qren_comp r u) v ;
    | eval_ren_cons_r r n q => qren_cons (apply_ren r n) (qren_comp r q) ;
    | eval_ren_comp_other r q => qren_comp r q
    } ; *)
  | eval_ren_comp r q => r ;
  | eval_ren_cons_0_shift => qren_id ;
  | eval_ren_cons n r =>
    let r := eval_ren r in
    qren_cons n r ;
  | eval_ren_other r => r
  }. *)

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
    | _, qsubst_ren r => qsubst_compr u r
    | _, _ => qsubst_comp u v
    end
  | qsubst_compr s r =>
    let s := eval_subst s in
    let r := eval_ren r in
    match s, r with
    | qsubst_id, _ => qsubst_ren r
    | _, qren_id => s
    | _, qren_comp x y => qsubst_compr (qsubst_compr s x) y
    | _, qren_cons n r =>
      qsubst_cons (unquote_subst s (unquote_nat n)) (qsubst_compr s r)
    | qsubst_ren s, _ => qsubst_ren (qren_comp s r)
    | _, _ => qsubst_compr s r
    end
  | qsubst_cons t s =>
    let s := eval_subst s in
    qsubst_cons t s
  | qsubst_ren r =>
    let r := eval_ren r in
    match r with
    | qren_id => qsubst_id
    | _ => qsubst_ren r
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
    | qren r t => qsubst (qsubst_compr s r) t
    | _ => qsubst s t
    end
  | _ => t
  end.

(** Correctness **)

Ltac set_eval_ren na :=
  lazymatch goal with
  | |- context [ eval_ren ?r ] =>
    set (na := eval_ren r) in * ;
    clearbody na
  end.

Lemma eval_ren_sound :
  ∀ r n,
    unquote_ren r n = unquote_ren (eval_ren r) n.
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  - cbn. set_eval_ren er1. set_eval_ren er2.
    destruct er1, er2.
    all: unfold funcomp ; cbn in *.
    all: try solve [ rewrite IHr1, IHr2 ; reflexivity ].
    + rewrite IHr1, IHr2. apply scons_comp'.
    + rewrite IHr1, IHr2. destruct n0.
      * cbn. admit.
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

Ltac quote_nat n :=
  lazymatch n with
  | 0 => constr:(q0)
  | var_zero => constr:(q0)
  | S ?n =>
    let q := quote_nat n in
    constr:(qS q)
  | _ => constr:(qnat_atom n)
  end.

Ltac quote_ren r :=
  lazymatch r with
  | funcomp ?r ?r' =>
    let q := quote_ren r in
    let q' := quote_ren r' in
    constr:(qren_comp q q')
  | λ x, ?r (?r' x) =>
    let q := quote_ren r in
    let q' := quote_ren r' in
    constr:(qren_comp q q')
  | scons ?n ?r =>
    let qn := quote_nat n in
    let q := quote_ren r in
    constr:(qren_cons qn q)
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
  | λ x, subst_cterm ?s (?t x) =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | funcomp ?s ?r =>
    let qs := quote_subst s in
    let qr := quote_ren r in
    constr:(qsubst_compr qs qr)
  | λ x, ?s (?r x) =>
    let qs := quote_subst s in
    let qr := quote_ren r in
    constr:(qsubst_compr qs qr)
  | scons ?t ?s =>
    let q := quote_subst s in
    constr:(qsubst_cons t q)
  | ids => constr:(qsubst_id)
  | _ =>
    first [
      let q := quote_ren s in
      constr:(qsubst_ren q)
    | constr:(qsubst_atom s)
    ]
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

Ltac rasimpl1_t t :=
  let q := quote_cterm t in
  change t with (unquote_cterm q) ;
  rewrite eval_cterm_sound ;
  cbn [
    unquote_cterm eval_cterm
    unquote_ren eval_ren
    unquote_subst eval_subst
    unquote_nat
    ren_cterm subst_cterm
  ].

Ltac rasimpl1 :=
  match goal with
  | |- context G[ ?t ] => progress (rasimpl1_t t)
  end.

Ltac rasimpl' :=
  repeat rasimpl1.

Ltac rasimpl :=
  repeat
    unfold
      VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
      Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
      subst1 in * ;
  minimize ;
  rasimpl' ;
  minimize.

Ltac rssimpl :=
  rasimpl ;
  autosubst_unfold ;
  rasimpl ;
  resubst ;
  rasimpl.

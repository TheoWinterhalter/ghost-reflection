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

(** Autosubst reflective tactic that should be more efficient than asimpl

  Downsides:
  - If an expression is under a binder and uses the bound variable, then rasimpl
    is unable to do anything. I don't see a way to avoid using setoid_rewrite
    there.
    ⇒ Maybe by using meta-variables instead of "atoms" so that rewrite doesn't
      have to touch the local variables.
      Not sure it would work.
    ⇒ Another option would be to have setoid_rasimpl which uses setoid_rewrite
      instead.
  - Also it cannot currently rewrite under new custom contexts.
  - Because I still need to use asimpl sometimes, and they don't normalise
    exactly the same, there might be a mismatch.

  Ways to improve:
  - Maybe the traversal isn't optimal, some subterms might be quoted and
    unquoted many times unnecessarily.
  - Maybe treatment of var, ids, and renamings as substitutions.
  - An NbE approach would be nice.
  - Ideally, we could do much more in one step if we could incude all rules
    pertaining to constructors of the syntax, but this should be generated.
  - shift could be shiftn instead, as we often need those, better than using
    addn manually, and the tactic could handle those easily.
  - Could call minimize only on subterms that are to be quoted as substitutions
    or renamings. In fact could be on the fly like quote λ x, ?f x as
    quote_subst f and so on for funcomp.
  - We could hijack typeclass resolution and hints to make the tactic extensible
    so as to support user-defined symbols. In that case, they could even call
    rasimpl_t or event rasimpl_r or rasimpl_s directly when the subterm is
    already known to be eg. a substitution.
  - We could also make the tactic generic over the syntax (at least as long as
    we don't exploit it) by replacing cterm here by some variable.
    The problem being that we need to provide the ren_cterm and subst_cterm
    somehow. We also would need some preprocessing to move everything to using
    typeclasses notations.
    Preprocessing can be done on the fly though.

**)

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
| qsubst_rcomp (r : quoted_ren) (s : quoted_subst)
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
  | qsubst_rcomp r s => funcomp (ren_cterm (unquote_ren r)) (unquote_subst s)
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
  end.

Fixpoint eval_ren (r : quoted_ren) :=
  match r with
  | qren_comp r q =>
    let r := eval_ren r in
    let q := eval_ren q in
    match eval_ren_comp_c r q with
    | eval_ren_id_l q => q
    | eval_ren_id_r r => r
    | eval_ren_cons_shift n r => r
    | eval_ren_comp_r r u v =>  qren_comp (qren_comp r u) v
    | eval_ren_cons_r r n q =>  qren_cons (apply_ren r n) (qren_comp r q)
    | eval_ren_comp_other r q => qren_comp r q
    end
  | qren_cons q0 qren_shift => qren_id
  | qren_cons n r =>
    let r := eval_ren r in
    qren_cons n r
  | _ => r
  end.

Inductive eval_subst_comp_view : quoted_subst → quoted_subst → Type :=
| es_id_l s : eval_subst_comp_view qsubst_id s
| es_id_r s : eval_subst_comp_view s qsubst_id
| es_comp_r s u v : eval_subst_comp_view s (qsubst_comp u v)
| es_compr_r s x y : eval_subst_comp_view s (qsubst_compr x y)
| es_rcomp_r s x y : eval_subst_comp_view s (qsubst_rcomp x y)
| es_cons_r s t s' : eval_subst_comp_view s (qsubst_cons t s')
| es_ren_l r s : eval_subst_comp_view (qsubst_ren r) s
| es_ren_r s r : eval_subst_comp_view s (qsubst_ren r)
| es_other u v : eval_subst_comp_view u v.

Definition eval_subst_comp_c u v : eval_subst_comp_view u v :=
  match u, v with
  | qsubst_id, v => es_id_l v
  | u, qsubst_id => es_id_r u
  | u, qsubst_comp x y => es_comp_r u x y
  | u, qsubst_compr x y => es_compr_r u x y
  | u, qsubst_rcomp x y => es_rcomp_r u x y
  | u, qsubst_cons t s => es_cons_r u t s
  | qsubst_ren r, s => es_ren_l r s
  | u, qsubst_ren r => es_ren_r u r
  | u, v => es_other u v
  end.

Inductive eval_subst_compr_view : quoted_subst → quoted_ren → Type :=
| esr_id_l r : eval_subst_compr_view qsubst_id r
| esr_id_r s : eval_subst_compr_view s qren_id
| esr_comp_r s x y : eval_subst_compr_view s (qren_comp x y)
| esr_cons_r s n r : eval_subst_compr_view s (qren_cons n r)
| esr_ren_l s r : eval_subst_compr_view (qsubst_ren s) r
| esr_cons_shift t s : eval_subst_compr_view (qsubst_cons t s) qren_shift
| esr_other s r : eval_subst_compr_view s r.

Definition eval_subst_compr_c s r : eval_subst_compr_view s r :=
  match s, r with
  | qsubst_id, r => esr_id_l r
  | s, qren_id => esr_id_r s
  | s, qren_comp x y => esr_comp_r s x y
  | s, qren_cons n r => esr_cons_r s n r
  | qsubst_ren s, r => esr_ren_l s r
  | qsubst_cons t s, qren_shift => esr_cons_shift t s
  | s, r => esr_other s r
  end.

Inductive eval_subst_rcomp_view : quoted_ren → quoted_subst → Type :=
| ers_id_l s : eval_subst_rcomp_view qren_id s
| ers_id_r r : eval_subst_rcomp_view r qsubst_id
| ers_comp_r r x y : eval_subst_rcomp_view r (qsubst_comp x y)
| ers_compr_r r x y : eval_subst_rcomp_view r (qsubst_compr x y)
| ers_rcomp_r r x y : eval_subst_rcomp_view r (qsubst_rcomp x y)
| ers_cons_r r t s : eval_subst_rcomp_view r (qsubst_cons t s)
| ers_ren_r r s : eval_subst_rcomp_view r (qsubst_ren s)
| ers_other r s : eval_subst_rcomp_view r s.

Definition eval_subst_rcomp_c r s : eval_subst_rcomp_view r s :=
  match r, s with
  | qren_id, s => ers_id_l s
  | r, qsubst_id => ers_id_r r
  | r, qsubst_comp x y => ers_comp_r r x y
  | r, qsubst_compr x y => ers_compr_r r x y
  | r, qsubst_rcomp x y => ers_rcomp_r r x y
  | r, qsubst_cons t s => ers_cons_r r t s
  | r, qsubst_ren s => ers_ren_r r s
  | r, s => ers_other r s
  end.

Inductive qren_id_view : quoted_ren → Type :=
| is_qren_id : qren_id_view qren_id
| not_qren_id r : qren_id_view r.

Definition test_qren_id r : qren_id_view r :=
  match r with
  | qren_id => is_qren_id
  | r => not_qren_id r
  end.

Fixpoint eval_subst (s : quoted_subst) : quoted_subst :=
  match s with
  | qsubst_comp u v =>
    let u := eval_subst u in
    let v := eval_subst v in
    match eval_subst_comp_c u v with
    | es_id_l v => v
    | es_id_r u => u
    | es_comp_r u x y => qsubst_comp (qsubst_comp u x) y
    | es_compr_r u x y => qsubst_compr (qsubst_comp u x) y
    | es_rcomp_r u x y => qsubst_comp (qsubst_compr u x) y
    | es_cons_r u t s => qsubst_cons (subst_cterm (unquote_subst u) t) (qsubst_comp u s)
    | es_ren_l r s => qsubst_rcomp r s
    | es_ren_r u r => qsubst_compr u r
    | es_other u v => qsubst_comp u v
    end
  | qsubst_compr s r =>
    let s := eval_subst s in
    let r := eval_ren r in
    match eval_subst_compr_c s r with
    | esr_id_l r => qsubst_ren r
    | esr_id_r s => s
    | esr_comp_r s x y => qsubst_compr (qsubst_compr s x) y
    | esr_cons_r s n r =>
      qsubst_cons (unquote_subst s (unquote_nat n)) (qsubst_compr s r)
    | esr_ren_l s r => qsubst_ren (qren_comp s r)
    | esr_cons_shift t s => s
    | esr_other s r => qsubst_compr s r
    end
  | qsubst_rcomp r s =>
    let r := eval_ren r in
    let s := eval_subst s in
    match eval_subst_rcomp_c r s with
    | ers_id_l s => s
    | ers_id_r r => qsubst_ren r
    | ers_comp_r r x y => qsubst_comp (qsubst_rcomp r x) y
    | ers_compr_r r x y => qsubst_compr (qsubst_rcomp r x) y
    | ers_rcomp_r r x y => qsubst_rcomp (qren_comp r x) y
    | ers_cons_r r t s =>
      qsubst_cons (ren_cterm (unquote_ren r) t) (qsubst_rcomp r s)
    | ers_ren_r r s => qsubst_ren (qren_comp r s)
    | ers_other r s => qsubst_rcomp r s
    end
  | qsubst_cons t s =>
    let s := eval_subst s in
    qsubst_cons t s
  | qsubst_ren r =>
    let r := eval_ren r in
    match test_qren_id r with
    | is_qren_id => qsubst_id
    | not_qren_id r => qsubst_ren r
    end
  | _ => s
  end.

Inductive qsubst_ren_id_view : quoted_subst → Type :=
| is_qsubst_ren r : qsubst_ren_id_view (qsubst_ren r)
| is_qsubst_id : qsubst_ren_id_view qsubst_id
| not_qsubst_ren_id s : qsubst_ren_id_view s.

Definition test_qsubst_ren_id s : qsubst_ren_id_view s :=
  match s with
  | qsubst_ren r => is_qsubst_ren r
  | qsubst_id => is_qsubst_id
  | s => not_qsubst_ren_id s
  end.

Fixpoint eval_cterm (t : quoted_cterm) : quoted_cterm :=
  match t with
  | qren r t =>
    let r := eval_ren r in
    let t := eval_cterm t in
    match t with
    | qsubst s t => qsubst (qsubst_comp (qsubst_ren r) s) t
    | qren r' t => qren (qren_comp r r') t
    | _ =>
      match test_qren_id r with
      | is_qren_id => t
      | not_qren_id r => qren r t
      end
    end
  | qsubst s t =>
    let s := eval_subst s in
    let t := eval_cterm t in
    match t with
    | qsubst s' t => qsubst (qsubst_comp s s') t
    | qren r t => qsubst (qsubst_compr s r) t
    | _ =>
      match test_qsubst_ren_id s with
      | is_qsubst_ren r => qren r t
      | is_qsubst_id => t
      | not_qsubst_ren_id s => qsubst s t
      end
    end
  | _ => t
  end.

(** Correctness **)

Lemma apply_ren_sound :
  ∀ r n,
    unquote_nat (apply_ren r n) = unquote_ren r (unquote_nat n).
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHr1, IHr2. reflexivity.
    + cbn. rewrite IHr1, IHr2. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + reflexivity.
    + cbn. rewrite IHr. reflexivity.
Qed.

Ltac set_eval_ren na :=
  lazymatch goal with
  | |- context [ eval_ren ?r ] =>
    set (na := eval_ren r) in * ;
    clearbody na
  end.

Ltac set_unquote_ren na :=
  lazymatch goal with
  | |- context [ unquote_ren ?r ] =>
    set (na := unquote_ren r) in * ;
    clearbody na
  end.

Ltac set_unquote_rens :=
  repeat (let n := fresh "r" in set_unquote_ren n).

Lemma eval_ren_sound :
  ∀ r n,
    unquote_ren r n = unquote_ren (eval_ren r) n.
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  - cbn. set_eval_ren er1. set_eval_ren er2.
    destruct eval_ren_comp_c.
    all: unfold funcomp ; cbn - [apply_ren] in *.
    all: try solve [ rewrite IHr1, IHr2 ; reflexivity ].
    rewrite IHr1, IHr2.
    rewrite apply_ren_sound.
    apply scons_comp'.
  - cbn. destruct n0.
    + cbn. eapply scons_morphism. 1: reflexivity.
      assumption.
    + destruct r. all: try reflexivity.
      * set (rr := eval_ren _) in *.
        etransitivity.
        1:{
          eapply scons_morphism. 1: reflexivity.
          intro. eapply IHr.
        }
        destruct n. all: reflexivity.
      * set (rr := eval_ren _) in *.
        etransitivity.
        1:{
          eapply scons_morphism. 1: reflexivity.
          intro. eapply IHr.
        }
        destruct n. all: reflexivity.
      * cbn. apply scons_eta_id'.
    + cbn. apply scons_morphism. 1: reflexivity.
      assumption.
Qed.

Ltac set_eval_subst na :=
  lazymatch goal with
  | |- context [ eval_subst ?s ] =>
    set (na := eval_subst s) in * ;
    clearbody na
  end.

Lemma eval_subst_sound :
  ∀ s n,
    unquote_subst s n = unquote_subst (eval_subst s) n.
Proof.
  intros s n.
  induction s in n |- *.
  all: try reflexivity.
  - cbn. set_eval_subst es1. set_eval_subst es2.
    destruct eval_subst_comp_c.
    + cbn in *. unfold funcomp. rewrite IHs2.
      etransitivity.
      1:{
        eapply subst_cterm_morphism. 1: eassumption.
        reflexivity.
      }
      asimpl. reflexivity.
    + cbn in *. unfold funcomp. rewrite IHs2.
      etransitivity.
      1:{
        eapply subst_cterm_morphism. 1: eassumption.
        reflexivity.
      }
      asimpl. reflexivity.
    + cbn in *. unfold funcomp in *.
      erewrite subst_cterm_morphism. 2,3: eauto.
      asimpl. reflexivity.
    + cbn in *. unfold funcomp in *.
      erewrite subst_cterm_morphism. 2,3: eauto.
      asimpl. reflexivity.
    + cbn in *. unfold funcomp in *.
      erewrite subst_cterm_morphism. 2,3: eauto.
      asimpl. reflexivity.
    + cbn in *. unfold funcomp.
      erewrite subst_cterm_morphism. 2,3: eauto.
      asimpl. destruct n. all: reflexivity.
    + cbn in *. unfold funcomp in *.
      rewrite IHs2.
      rewrite rinstInst'_cterm. apply subst_cterm_morphism. 2: reflexivity.
      intro. rewrite IHs1. unfold funcomp. reflexivity.
    + cbn in *. unfold funcomp in *.
      rewrite IHs2. cbn. rewrite IHs1. reflexivity.
    + cbn in *. unfold funcomp. rewrite IHs2.
      erewrite subst_cterm_morphism. 2,3: eauto.
      reflexivity.
  - cbn. set_eval_subst es.
    remember (eval_ren _) as er eqn:e.
    destruct eval_subst_compr_c.
    + subst. cbn. unfold funcomp. rewrite IHs.
      cbn. rewrite <- eval_ren_sound. reflexivity.
    + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
      rewrite IHs. reflexivity.
    + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
      rewrite IHs. reflexivity.
    + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
      rewrite IHs. destruct n. all: reflexivity.
    + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
      rewrite IHs. reflexivity.
    + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
      rewrite IHs. cbn. reflexivity.
    + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
      rewrite IHs. reflexivity.
  - cbn. set_eval_subst es.
    remember (eval_ren _) as er eqn:e.
    destruct eval_subst_rcomp_c.
    + unfold funcomp.
      erewrite ren_cterm_morphism. 3: reflexivity.
      2:{ intro. rewrite eval_ren_sound, <- e. reflexivity. }
      cbn. asimpl. auto.
    + subst. unfold funcomp. rewrite IHs. cbn. rewrite eval_ren_sound.
      reflexivity.
    + subst. unfold funcomp. rewrite IHs. cbn. unfold funcomp.
      rewrite substRen_cterm. apply subst_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp. apply ren_cterm_morphism. 2: reflexivity.
      intro. rewrite <- eval_ren_sound. reflexivity.
    + subst. unfold funcomp. rewrite IHs. cbn. unfold funcomp.
      apply ren_cterm_morphism. 2: reflexivity.
      intro. rewrite <- eval_ren_sound. reflexivity.
    + subst. unfold funcomp. rewrite IHs. cbn. unfold funcomp.
      rewrite renRen_cterm. apply ren_cterm_morphism. 2: reflexivity.
      intro. rewrite <- eval_ren_sound. reflexivity.
    + subst. unfold funcomp. rewrite IHs. cbn.
      destruct n.
      * cbn. apply ren_cterm_morphism. 2: reflexivity.
        intro. rewrite eval_ren_sound. reflexivity.
      * cbn. unfold funcomp. apply ren_cterm_morphism. 2: reflexivity.
        intro. rewrite eval_ren_sound. reflexivity.
    + subst. unfold funcomp. rewrite IHs. cbn. unfold funcomp.
      rewrite <- eval_ren_sound. reflexivity.
    + subst. cbn. unfold funcomp. rewrite IHs.
      apply ren_cterm_morphism. 2: reflexivity.
      intro. rewrite eval_ren_sound. reflexivity.
  - cbn. erewrite scons_morphism. 2,3: eauto.
    reflexivity.
  - cbn. remember (eval_ren _) as er eqn:e.
    destruct test_qren_id.
    + cbn. unfold funcomp. rewrite eval_ren_sound, <- e.
      reflexivity.
    + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
      reflexivity.
Qed.

Lemma eval_cterm_sound :
  ∀ t,
    unquote_cterm t = unquote_cterm (eval_cterm t).
Proof.
  intros t.
  induction t.
  - reflexivity.
  - cbn. remember (eval_cterm _) as et eqn:e in *.
    destruct et.
    + remember (eval_ren _) as rr eqn:er.
      destruct test_qren_id.
      * cbn. erewrite ren_cterm_morphism. 3: reflexivity.
        2:{ intro. rewrite eval_ren_sound, <- er. reflexivity. }
        cbn. asimpl. assumption.
      * subst. cbn. rewrite IHt. cbn.
        eapply ren_cterm_morphism. 2: reflexivity.
        intro. apply eval_ren_sound.
    + cbn. rewrite IHt. cbn. rewrite renRen_cterm.
      apply ren_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp. rewrite <- eval_ren_sound. reflexivity.
    + cbn. rewrite IHt. cbn.
      rewrite substRen_cterm.
      apply subst_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp.
      rewrite rinstInst'_cterm.
      apply subst_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp.
      rewrite <- eval_ren_sound. reflexivity.
  - cbn. remember (eval_cterm _) as et eqn:e in *.
    destruct et.
    + remember (eval_subst _) as ss eqn:es in *.
      rewrite IHt. cbn.
      destruct test_qsubst_ren_id.
      * cbn. erewrite subst_cterm_morphism. 3: reflexivity.
        2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
        cbn. rewrite rinstInst'_cterm. reflexivity.
      * cbn. erewrite subst_cterm_morphism. 3: reflexivity.
        2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
        cbn. asimpl. reflexivity.
      * subst. cbn.
        eapply subst_cterm_morphism. 2: reflexivity.
        intro. apply eval_subst_sound.
    + cbn. rewrite IHt. cbn. rewrite renSubst_cterm.
      apply subst_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp. rewrite <- eval_subst_sound. reflexivity.
    + cbn. rewrite IHt. cbn. rewrite substSubst_cterm.
      eapply subst_cterm_morphism. 2: reflexivity.
      intro. unfold funcomp.
      eapply subst_cterm_morphism. 2: reflexivity.
      intro. rewrite <- eval_subst_sound. reflexivity.
Qed.

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
  | λ x, x => constr:(qren_id)
  | shift => constr:(qren_shift)
  | S => constr:(qren_shift)
  | _ => constr:(qren_atom r)
  end.

Ltac quote_subst s :=
  lazymatch s with
  | funcomp cvar ?r =>
    let q := quote_ren r in
    constr:(qsubst_ren q)
  | λ x, cvar (?r x) =>
    let q := quote_ren r in
    constr:(qsubst_ren q)
  | funcomp (subst_cterm ?s) ?t =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | λ x, subst_cterm ?s (?t x) =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | funcomp (ren_cterm ?r) ?s =>
    let qr := quote_ren r in
    let qs := quote_subst s in
    constr:(qsubst_rcomp qr qs)
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
  | cvar => constr:(qsubst_id)
  | _ => constr:(qsubst_atom s)
  end.

Ltac quote_cterm t :=
  lazymatch t with
  | ren_cterm ?r ?t =>
    let qr := quote_ren r in
    let qt := quote_cterm t in
    constr:(qren qr qt)
  | subst_cterm ?s ?t =>
    let qs := quote_subst s in
    let qt := quote_cterm t in
    constr:(qsubst qs qt)
  | _ => constr:(qatom t)
  end.

(** Main tactic **)

Ltac asimpl_unfold :=
  unfold
    (* Taken from asimpl *)
    VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
    Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
    subst1,
    (* Added myself *)
    upRen_cterm_cterm, up_ren, up_cterm_cterm, var_zero.

Ltac asimpl_unfold_in h :=
  unfold
    (* Taken from asimpl *)
    VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
    Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
    subst1,
    (* Added myself *)
    upRen_cterm_cterm, up_ren, up_cterm_cterm, var_zero
  in h.

Ltac asimpl_unfold_all :=
  unfold
    (* Taken from asimpl *)
    VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
    Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
    subst1,
    (* Added myself *)
    upRen_cterm_cterm, up_ren, up_cterm_cterm, var_zero
  in *.

Tactic Notation "aunfold" := asimpl_unfold.
Tactic Notation "aunfold" "in" hyp(h) := asimpl_unfold_in h.
Tactic Notation "aunfold" "in" "*" := asimpl_unfold_all.

Ltac post_process :=
  cbn [
    unquote_cterm eval_cterm test_qren_id test_qsubst_ren_id
    unquote_ren eval_ren apply_ren eval_ren_comp_c
    unquote_subst eval_subst eval_subst_compr_c eval_subst_comp_c
    eval_subst_rcomp_c
    unquote_nat
    ren_cterm subst_cterm scons
  ] ;
  unfold upRen_cterm_cterm, up_ren, up_cterm_cterm, var_zero. (* Maybe aunfold? *)

Ltac rasimpl1_t t :=
  let q := quote_cterm t in
  change t with (unquote_cterm q) ;
  rewrite eval_cterm_sound ;
  post_process.

Ltac setoid_rasimpl1_t t :=
  let q := quote_cterm t in
  change t with (unquote_cterm q) ;
  setoid_rewrite eval_cterm_sound ;
  post_process.

Ltac rasimpl1_aux tac g :=
  let rec aux t :=
    first [
      progress (repeat (tac t))
    | lazymatch t with
      | subst_cterm ?s _ => aux s
      | ren_cterm ?r _ => aux r
      | ?f ?u => aux f ; aux u
      | ∀ x : ?A, ?B => aux A ; aux B
      end
    | idtac
    ]
  in aux g.

Ltac rasimpl1 tac :=
  lazymatch goal with
  | |- ?g => rasimpl1_aux tac g
  end.

Ltac rasimpl' tac :=
  repeat (rasimpl1 tac).

Ltac rasimpl_ tac :=
  repeat aunfold ;
  minimize ;
  rasimpl' tac ;
  minimize.

Ltac rasimpl :=
  rasimpl_ rasimpl1_t.

Ltac setoid_rasimpl :=
  rasimpl_ setoid_rasimpl1_t.

(* It's how it's done for asimpl but that's unsatisfactory *)
Ltac rasimpl_in h :=
  revert h ;
  rasimpl ;
  intro h.

Ltac setoid_rasimpl_in h :=
  revert h ;
  setoid_rasimpl ;
  intro h.

(* Taken from core.minimize *)
(* Ltac minimize_in h :=
  repeat first [
    change (λ x, ?f x) with f in h
  | change (λ x, ?g (?f x)) with (funcomp g f) in h
  ].

Tactic Notation "minimize" "in" hyp(h) := minimize_in h.

Ltac rasimpl1_t_in h t :=
  let q := quote_cterm t in
  change t with (unquote_cterm q) in h ;
  rewrite eval_cterm_sound in h ;
  cbn [
    unquote_cterm eval_cterm test_qren_id test_qsubst_ren
    unquote_ren eval_ren apply_ren eval_ren_comp_c
    unquote_subst eval_subst eval_subst_compr_c eval_subst_comp_c
    unquote_nat
    ren_cterm subst_cterm scons
  ] in h.

Ltac rasimpl1_aux_in h g :=
  first [
    progress (rasimpl1_t_in h g)
  | lazymatch g with
    | subst_cterm ?s _ => rasimpl1_aux_in h s
    | ren_cterm ?r _ => rasimpl1_aux_in h r
    | ?f ?u => rasimpl1_aux_in h f ; rasimpl1_aux_in h u
    | ∀ x : ?A, ?B => rasimpl1_aux_in h A ; rasimpl1_aux_in h B
    end
  | idtac
  ].

Ltac rasimpl1_in h :=
  rasimpl1_aux_in h h.

Ltac rasimpl'_in h :=
  repeat (rasimpl1_in h).

Ltac rasimpl_in h :=
  repeat aunfold in h ;
  minimize in h ;
  rasimpl'_in h ;
  minimize in h. *)

Tactic Notation "rasimpl" "in" hyp(h) :=
  rasimpl_in h.

Tactic Notation "setoid_rasimpl" "in" hyp(h) :=
  setoid_rasimpl_in h.

(* Ltac rssimpl :=
  rasimpl ;
  autosubst_unfold ;
  rasimpl ;
  resubst ;
  rasimpl. *)

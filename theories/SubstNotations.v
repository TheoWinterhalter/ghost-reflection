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
| es_cons_r s t s' : eval_subst_comp_view s (qsubst_cons t s')
| es_ren_r s r : eval_subst_comp_view s (qsubst_ren r)
| es_other u v : eval_subst_comp_view u v.

Definition eval_subst_comp_c u v : eval_subst_comp_view u v :=
  match u, v with
  | qsubst_id, v => es_id_l v
  | u, qsubst_id => es_id_r u
  | u, qsubst_comp x y => es_comp_r u x y
  | u, qsubst_cons t s => es_cons_r u t s
  | u, qsubst_ren r => es_ren_r u r
  | u, v => es_other u v
  end.

Inductive eval_subst_compr_view : quoted_subst → quoted_ren → Type :=
| esr_id_l r : eval_subst_compr_view qsubst_id r
| esr_id_r s : eval_subst_compr_view s qren_id
| esr_comp_r s x y : eval_subst_compr_view s (qren_comp x y)
| esr_cons_r s n r : eval_subst_compr_view s (qren_cons n r)
| esr_ren_l s r : eval_subst_compr_view (qsubst_ren s) r
| esr_other s r : eval_subst_compr_view s r.

Definition eval_subst_compr_c s r : eval_subst_compr_view s r :=
  match s, r with
  | qsubst_id, v => esr_id_l r
  | s, qren_id => esr_id_r s
  | s, qren_comp x y => esr_comp_r s x y
  | s, qren_cons n r => esr_cons_r s n r
  | qsubst_ren s, r => esr_ren_l s r
  | s, r => esr_other s r
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
    | es_cons_r u t s => qsubst_cons (subst_cterm (unquote_subst u) t) (qsubst_comp u s)
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
    | esr_other s r => qsubst_compr s r
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

Fixpoint eval_cterm (t : quoted_cterm) : quoted_cterm :=
  match t with
  | qren r t =>
    let r := eval_ren r in
    let t := eval_cterm t in
    match t with
    | qsubst s t => qsubst (qsubst_comp (qsubst_ren r) s) t
    | qren r' t => qren (qren_comp r r') t
    | _ => qren r t
    end
  | qsubst s t =>
    let s := eval_subst s in
    let t := eval_cterm t in
    match t with
    | qsubst s' t => qsubst (qsubst_comp s s') t
    | qren r t => qsubst (qsubst_compr s r) t
    | _ => qsubst s t
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
    + cbn in *. unfold funcomp.
      erewrite subst_cterm_morphism. 2,3: eauto.
      asimpl. destruct n. all: reflexivity.
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
    + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
      rewrite IHs. reflexivity.
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
    + cbn. rewrite IHt. cbn.
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
    + cbn. rewrite IHt. cbn.
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

Ltac rasimpl1_t t :=
  let q := quote_cterm t in
  change t with (unquote_cterm q) ;
  rewrite eval_cterm_sound ;
  cbn [
    unquote_cterm eval_cterm test_qren_id
    unquote_ren eval_ren apply_ren eval_ren_comp_c
    unquote_subst eval_subst eval_subst_compr_c eval_subst_comp_c
    unquote_nat
    ren_cterm subst_cterm
  ].

Ltac rasimpl1_aux g :=
  first [
    progress (rasimpl1_t g)
  | lazymatch g with
    | subst_cterm ?s _ => rasimpl1_aux s
    | ren_cterm ?r _ => rasimpl1_aux r
    | ?f ?u => rasimpl1_aux f ; rasimpl1_aux u
    end
  | idtac
  ].

Ltac rasimpl1 :=
  lazymatch goal with
  | |- ?g => rasimpl1_aux g
  end.

Ltac rasimpl' :=
  repeat rasimpl1.

Ltac rasimpl :=
  repeat
    unfold
      (* Taken from asimpl *)
      VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
      Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
      subst1,
      (* Added myself *)
      upRen_cterm_cterm, up_ren ;
  minimize ;
  rasimpl' ;
  minimize.

Ltac rssimpl :=
  rasimpl ;
  autosubst_unfold ;
  rasimpl ;
  resubst ;
  rasimpl.

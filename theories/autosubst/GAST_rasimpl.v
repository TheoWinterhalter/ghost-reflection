(** GAST support for rasimpl **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import core unscoped GAST RAsimpl.
From Coq Require Import Setoid Morphisms Relation_Definitions.
Import ListNotations.

Inductive quoted_subst :=
| qsubst_atom (σ : nat → term)
| qsubst_comp (s t : quoted_subst)
| qsubst_compr (s : quoted_subst) (r : quoted_ren)
| qsubst_rcomp (r : quoted_ren) (s : quoted_subst)
| qsubst_cons (t : quoted_term) (s : quoted_subst)
| qsubst_id
| qsubst_ren (r : quoted_ren)

with quoted_term :=
| qatom (t : term)
| qren (r : quoted_ren) (t : quoted_term)
| qsubst (s : quoted_subst) (t : quoted_term).

Fixpoint unquote_subst q :=
  match q with
  | qsubst_atom σ => σ
  | qsubst_comp s t => funcomp (subst_term (unquote_subst s)) (unquote_subst t)
  | qsubst_compr s r => funcomp (unquote_subst s) (unquote_ren r)
  | qsubst_rcomp r s => funcomp (ren_term (unquote_ren r)) (unquote_subst s)
  | qsubst_cons t s => scons (unquote_term t) (unquote_subst s)
  | qsubst_id => var
  | qsubst_ren r => funcomp var (unquote_ren r)
  end

with unquote_term q :=
  match q with
  | qatom t => t
  | qren r t => ren_term (unquote_ren r) (unquote_term t)
  | qsubst s t => subst_term (unquote_subst s) (unquote_term t)
  end.

(** Evaluation **)

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

(* TODO Could be improved like apply_ren *)
Fixpoint apply_subst (s : quoted_subst) (n : quoted_nat) : quoted_term :=
  match s, n with
  | qsubst_atom s, _ => qatom (s (unquote_nat n))
  | qsubst_id, _ => qatom (var (unquote_nat n))
  | _, qnat_atom n => qatom (unquote_subst s n)
  | qsubst_comp s1 s2, _ => qsubst s1 (apply_subst s2 n)
  | qsubst_compr s r, _ => apply_subst s (apply_ren r n)
  | qsubst_rcomp r s, _ => qren r (apply_subst s n)
  | qsubst_cons t s, q0 => t
  | qsubst_cons t s, qS n => apply_subst s n
  | qsubst_ren r, n => qatom (var (unquote_nat (apply_ren r n)))
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
    | es_cons_r u t s => qsubst_cons (qsubst u t) (qsubst_comp u s)
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
    | esr_cons_r s n r => qsubst_cons (apply_subst s n) (qsubst_compr s r)
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
    | ers_cons_r r t s => qsubst_cons (qren r t) (qsubst_rcomp r s)
    | ers_ren_r r s => qsubst_ren (qren_comp r s)
    | ers_other r s => qsubst_rcomp r s
    end
  | qsubst_cons t s =>
    let t := eval_term t in
    let s := eval_subst s in
    qsubst_cons t s
  | qsubst_ren r =>
    let r := eval_ren r in
    match test_qren_id r with
    | is_qren_id => qsubst_id
    | not_qren_id r => qsubst_ren r
    end
  | _ => s
  end

with eval_term (t : quoted_term) : quoted_term :=
  match t with
  | qren r t =>
    let r := eval_ren r in
    let t := eval_term t in
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
    let t := eval_term t in
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

Lemma apply_subst_sound :
  ∀ s n,
    unquote_term (apply_subst s n) = unquote_subst s (unquote_nat n).
Proof.
  intros s n.
  induction s in n |- *.
  all: try reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHs2. reflexivity.
    + cbn. rewrite IHs2. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + rewrite IHs. rewrite apply_ren_sound. reflexivity.
    + cbn. rewrite IHs. rewrite apply_ren_sound. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHs. reflexivity.
    + cbn. rewrite IHs. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + reflexivity.
    + cbn. rewrite IHs. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite apply_ren_sound. reflexivity.
    + cbn. rewrite apply_ren_sound. reflexivity.
Qed.

Ltac set_eval_subst na :=
  lazymatch goal with
  | eval_subst_sound : ∀ s : quoted_subst, _ |- context [ eval_subst ?s ] =>
    let IH := fresh "IH" in
    pose proof (eval_subst_sound s) as IH ;
    set (na := eval_subst s) in * ;
    clearbody na
  end.

Fixpoint eval_subst_sound s :
    pointwise_relation _ eq (unquote_subst s) (unquote_subst (eval_subst s))

with eval_term_sound t :
    unquote_term t = unquote_term (eval_term t).
Proof.
  {
    intros n.
    destruct s.
    all: try reflexivity.
    - cbn. set_eval_subst es1. set_eval_subst es2.
      destruct eval_subst_comp_c.
      + cbn in *. unfold funcomp. rewrite IH, IH0.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp. rewrite IH, IH0.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. destruct n. all: reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite IH, IH0.
        rewrite rinstInst'_term. reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite IH, IH0. reflexivity.
      + cbn in *. unfold funcomp. rewrite IH, IH0. reflexivity.
    - cbn. set_eval_subst es.
      remember (eval_ren _) as er eqn:e.
      destruct eval_subst_compr_c.
      + subst. cbn. unfold funcomp. rewrite IH.
        cbn. rewrite <- eval_ren_sound. reflexivity.
      + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
        rewrite IH. reflexivity.
      + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
        rewrite IH. reflexivity.
      + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
        rewrite IH. destruct n. 2: reflexivity.
        cbn. rewrite apply_subst_sound. reflexivity.
      + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
        rewrite IH. reflexivity.
      + unfold funcomp. rewrite eval_ren_sound, <- e. cbn.
        rewrite IH. cbn. reflexivity.
      + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
        rewrite IH. reflexivity.
    - cbn. set_eval_subst es.
      remember (eval_ren _) as er eqn:e.
      destruct eval_subst_rcomp_c.
      + unfold funcomp.
        erewrite ren_term_morphism. 3: reflexivity.
        2:{ intro. rewrite eval_ren_sound, <- e. reflexivity. }
        cbn. asimpl. auto.
      + subst. unfold funcomp. rewrite IH. cbn. rewrite eval_ren_sound.
        reflexivity.
      + subst. unfold funcomp. rewrite IH. cbn. unfold funcomp.
        rewrite substRen_term. apply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp. apply ren_term_morphism. 2: reflexivity.
        intro. rewrite <- eval_ren_sound. reflexivity.
      + subst. unfold funcomp. rewrite IH. cbn. unfold funcomp.
        apply ren_term_morphism. 2: reflexivity.
        intro. rewrite <- eval_ren_sound. reflexivity.
      + subst. unfold funcomp. rewrite IH. cbn. unfold funcomp.
        rewrite renRen_term. apply ren_term_morphism. 2: reflexivity.
        intro. rewrite <- eval_ren_sound. reflexivity.
      + subst. unfold funcomp. rewrite IH. cbn.
        destruct n.
        * cbn. apply ren_term_morphism. 2: reflexivity.
          intro. rewrite eval_ren_sound. reflexivity.
        * cbn. unfold funcomp. apply ren_term_morphism. 2: reflexivity.
          intro. rewrite eval_ren_sound. reflexivity.
      + subst. unfold funcomp. rewrite IH. cbn. unfold funcomp.
        rewrite <- eval_ren_sound. reflexivity.
      + subst. cbn. unfold funcomp. rewrite IH.
        apply ren_term_morphism. 2: reflexivity.
        intro. rewrite eval_ren_sound. reflexivity.
    - cbn. erewrite scons_morphism. 2,3: eauto.
      reflexivity.
    - cbn. remember (eval_ren _) as er eqn:e.
      destruct test_qren_id.
      + cbn. unfold funcomp. rewrite eval_ren_sound, <- e.
        reflexivity.
      + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
        reflexivity.
  }
  {
    destruct t.
    - reflexivity.
    - cbn. remember (eval_term _) as et eqn:e in *.
      destruct et.
      + remember (eval_ren _) as rr eqn:er.
        destruct test_qren_id.
        * rewrite eval_term_sound, <- e.
          cbn. erewrite ren_term_morphism. 3: reflexivity.
          2:{ intro. rewrite eval_ren_sound, <- er. reflexivity. }
          cbn. asimpl. reflexivity.
        * subst. cbn. rewrite eval_term_sound, <- e. cbn.
          eapply ren_term_morphism. 2: reflexivity.
          intro. apply eval_ren_sound.
      + cbn. rewrite eval_term_sound, <- e. cbn. rewrite renRen_term.
        apply ren_term_morphism. 2: reflexivity.
        intro. unfold funcomp. rewrite <- eval_ren_sound. reflexivity.
      + cbn. rewrite eval_term_sound, <- e. cbn.
        rewrite substRen_term.
        apply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp.
        rewrite rinstInst'_term.
        apply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp.
        rewrite <- eval_ren_sound. reflexivity.
    - cbn. remember (eval_term _) as et eqn:e in *.
      destruct et.
      + remember (eval_subst _) as ss eqn:es in *.
        rewrite eval_term_sound, <- e. cbn.
        destruct test_qsubst_ren_id.
        * cbn. erewrite subst_term_morphism. 3: reflexivity.
          2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
          cbn. rewrite rinstInst'_term. reflexivity.
        * cbn. erewrite subst_term_morphism. 3: reflexivity.
          2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
          cbn. asimpl. reflexivity.
        * subst. cbn.
          eapply subst_term_morphism. 2: reflexivity.
          intro. apply eval_subst_sound.
      + cbn. rewrite eval_term_sound, <- e. cbn. rewrite renSubst_term.
        apply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp. rewrite <- eval_subst_sound. reflexivity.
      + cbn. rewrite eval_term_sound, <- e. cbn. rewrite substSubst_term.
        eapply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp.
        eapply subst_term_morphism. 2: reflexivity.
        intro. rewrite <- eval_subst_sound. reflexivity.
  }
Qed.

(** Quoting **)

Ltac quote_subst s :=
  lazymatch s with
  | funcomp var ?r =>
    let q := quote_ren r in
    constr:(qsubst_ren q)
  | λ x, var (?r x) =>
    let q := quote_ren r in
    constr:(qsubst_ren q)
  | funcomp (subst_term ?s) ?t =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | funcomp (ren_term ?r) ?s =>
    let qr := quote_ren r in
    let qs := quote_subst s in
    constr:(qsubst_rcomp qr qs)
  | funcomp ?s ?r =>
    let qs := quote_subst s in
    let qr := quote_ren r in
    constr:(qsubst_compr qs qr)
  | scons ?t ?s =>
    let qt := quote_term t in
    let q := quote_subst s in
    constr:(qsubst_cons qt q)
  | ids => constr:(qsubst_id)
  | var => constr:(qsubst_id)
  (* Instead of minimize *)
  | λ x, ?g (?f x) =>
    let t := constr:(funcomp g f) in
    quote_subst t
  | λ x, ?f x =>
    let t := constr:(f) in
    quote_subst t
  | _ => constr:(qsubst_atom s)
  end

with quote_term t :=
  lazymatch t with
  | ren_term ?r ?t =>
    let qr := quote_ren r in
    let qt := quote_term t in
    constr:(qren qr qt)
  | subst_term ?s ?t =>
    let qs := quote_subst s in
    let qt := quote_term t in
    constr:(qsubst qs qt)
  | _ => constr:(qatom t)
  end.

(** Unfoldings **)

#[export] Hint Unfold
  VarInstance_term Ren_term Up_term_term Up_term up_term Subst_term
  upRen_term_term up_term_term
  : asimpl_unfold.

Class TermSimplification (t s : term) := MkSimplTm {
  autosubst_simpl_term : t = s
}.

Arguments autosubst_simpl_term t {s _}.

Hint Mode TermSimplification + - : typeclass_instances.

Declare Reduction asimpl_cbn_term :=
  cbn [
    unquote_term eval_term test_qren_id test_qsubst_ren_id
    unquote_ren eval_ren apply_ren eval_ren_comp_c
    unquote_subst eval_subst eval_subst_compr_c eval_subst_comp_c
    eval_subst_rcomp_c apply_subst
    unquote_nat
    ren_term subst_term scons
  ].

Declare Reduction asimpl_unfold_term :=
  unfold upRen_term_term, up_ren, up_term_term, var_zero.

#[export] Hint Extern 10 (TermSimplification ?t _) =>
  let q := quote_term t in
  let s := eval asimpl_cbn_term in (unquote_term (eval_term q)) in
  let s := eval asimpl_unfold_term in s in
  exact (MkSimplTm t s (eval_term_sound q))
  : typeclass_instances.

Class SubstSimplification (r s : nat → term) := MkSimplSubst {
  autosubst_simpl_csubst : pointwise_relation _ eq r s
}.

Arguments autosubst_simpl_csubst r {s _}.

Hint Mode SubstSimplification + - : typeclass_instances.

#[export] Hint Extern 10 (SubstSimplification ?r _) =>
  let q := quote_subst r in
  let s := eval asimpl_cbn_term in (unquote_subst (eval_subst q)) in
  let s := eval asimpl_unfold_term in s in
  exact (MkSimplSubst r s (eval_subst_sound q))
  : typeclass_instances.

Lemma autosubst_simpl_term_ren :
  ∀ r t s,
    TermSimplification (ren_term r t) s →
    ren_term r t = s.
Proof.
  intros r t s H.
  apply autosubst_simpl_term, _.
Qed.

Lemma autosubst_simpl_term_subst :
  ∀ r t s,
    TermSimplification (subst_term r t) s →
    subst_term r t = s.
Proof.
  intros r t s H.
  apply autosubst_simpl_term, _.
Qed.

(** Triggers **)

#[export] Hint Rewrite -> autosubst_simpl_term_ren : asimpl.
#[export] Hint Rewrite -> autosubst_simpl_term_subst : asimpl.

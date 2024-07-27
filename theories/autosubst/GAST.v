From GhostTT.autosubst Require Import core unscoped.
From GhostTT Require Import BasicAST.
From Coq Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive term : Type :=
  | var : nat -> term
  | Sort : mode -> level -> term
  | Pi : level -> level -> mode -> mode -> term -> term -> term
  | lam : mode -> term -> term -> term
  | app : term -> term -> term
  | Erased : term -> term
  | hide : term -> term
  | reveal : term -> term -> term -> term
  | Reveal : term -> term -> term
  | toRev : term -> term -> term -> term
  | fromRev : term -> term -> term -> term
  | gheq : term -> term -> term -> term
  | ghrefl : term -> term -> term
  | ghcast : term -> term -> term -> term -> term -> term -> term
  | tbool : term
  | ttrue : term
  | tfalse : term
  | tif : mode -> term -> term -> term -> term -> term
  | tnat : term
  | tzero : term
  | tsucc : term -> term
  | tnat_elim : mode -> term -> term -> term -> term -> term
  | tvec : term -> term -> term
  | tvnil : term -> term
  | tvcons : term -> term -> term -> term
  | tvec_elim : mode -> term -> term -> term -> term -> term -> term -> term
  | bot : term
  | bot_elim : mode -> term -> term -> term.

Lemma congr_Sort {s0 : mode} {s1 : level} {t0 : mode} {t1 : level}
  (H0 : s0 = t0) (H1 : s1 = t1) : Sort s0 s1 = Sort t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Sort x s1) H0))
         (ap (fun x => Sort t0 x) H1)).
Qed.

Lemma congr_Pi {s0 : level} {s1 : level} {s2 : mode} {s3 : mode} {s4 : term}
  {s5 : term} {t0 : level} {t1 : level} {t2 : mode} {t3 : mode} {t4 : term}
  {t5 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3)
  (H4 : s4 = t4) (H5 : s5 = t5) : Pi s0 s1 s2 s3 s4 s5 = Pi t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl (ap (fun x => Pi x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => Pi t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => Pi t0 t1 x s3 s4 s5) H2))
               (ap (fun x => Pi t0 t1 t2 x s4 s5) H3))
            (ap (fun x => Pi t0 t1 t2 t3 x s5) H4))
         (ap (fun x => Pi t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_lam {s0 : mode} {s1 : term} {s2 : term} {t0 : mode} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  lam s0 s1 s2 = lam t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => lam x s1 s2) H0))
            (ap (fun x => lam t0 x s2) H1)) (ap (fun x => lam t0 t1 x) H2)).
Qed.

Lemma congr_app {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_Erased {s0 : term} {t0 : term} (H0 : s0 = t0) :
  Erased s0 = Erased t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Erased x) H0)).
Qed.

Lemma congr_hide {s0 : term} {t0 : term} (H0 : s0 = t0) : hide s0 = hide t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => hide x) H0)).
Qed.

Lemma congr_reveal {s0 : term} {s1 : term} {s2 : term} {t0 : term}
  {t1 : term} {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  reveal s0 s1 s2 = reveal t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => reveal x s1 s2) H0))
            (ap (fun x => reveal t0 x s2) H1))
         (ap (fun x => reveal t0 t1 x) H2)).
Qed.

Lemma congr_Reveal {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : Reveal s0 s1 = Reveal t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Reveal x s1) H0))
         (ap (fun x => Reveal t0 x) H1)).
Qed.

Lemma congr_toRev {s0 : term} {s1 : term} {s2 : term} {t0 : term} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  toRev s0 s1 s2 = toRev t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => toRev x s1 s2) H0))
            (ap (fun x => toRev t0 x s2) H1))
         (ap (fun x => toRev t0 t1 x) H2)).
Qed.

Lemma congr_fromRev {s0 : term} {s1 : term} {s2 : term} {t0 : term}
  {t1 : term} {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  fromRev s0 s1 s2 = fromRev t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => fromRev x s1 s2) H0))
            (ap (fun x => fromRev t0 x s2) H1))
         (ap (fun x => fromRev t0 t1 x) H2)).
Qed.

Lemma congr_gheq {s0 : term} {s1 : term} {s2 : term} {t0 : term} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  gheq s0 s1 s2 = gheq t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => gheq x s1 s2) H0))
            (ap (fun x => gheq t0 x s2) H1)) (ap (fun x => gheq t0 t1 x) H2)).
Qed.

Lemma congr_ghrefl {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : ghrefl s0 s1 = ghrefl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ghrefl x s1) H0))
         (ap (fun x => ghrefl t0 x) H1)).
Qed.

Lemma congr_ghcast {s0 : term} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {t0 : term} {t1 : term} {t2 : term} {t3 : term}
  {t4 : term} {t5 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  ghcast s0 s1 s2 s3 s4 s5 = ghcast t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => ghcast x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => ghcast t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => ghcast t0 t1 x s3 s4 s5) H2))
               (ap (fun x => ghcast t0 t1 t2 x s4 s5) H3))
            (ap (fun x => ghcast t0 t1 t2 t3 x s5) H4))
         (ap (fun x => ghcast t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_tbool : tbool = tbool.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ttrue : ttrue = ttrue.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tfalse : tfalse = tfalse.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tif {s0 : mode} {s1 : term} {s2 : term} {s3 : term} {s4 : term}
  {t0 : mode} {t1 : term} {t2 : term} {t3 : term} {t4 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) :
  tif s0 s1 s2 s3 s4 = tif t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl (ap (fun x => tif x s1 s2 s3 s4) H0))
                  (ap (fun x => tif t0 x s2 s3 s4) H1))
               (ap (fun x => tif t0 t1 x s3 s4) H2))
            (ap (fun x => tif t0 t1 t2 x s4) H3))
         (ap (fun x => tif t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_tnat : tnat = tnat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tzero : tzero = tzero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tsucc {s0 : term} {t0 : term} (H0 : s0 = t0) :
  tsucc s0 = tsucc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tsucc x) H0)).
Qed.

Lemma congr_tnat_elim {s0 : mode} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {t0 : mode} {t1 : term} {t2 : term} {t3 : term} {t4 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  : tnat_elim s0 s1 s2 s3 s4 = tnat_elim t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl
                     (ap (fun x => tnat_elim x s1 s2 s3 s4) H0))
                  (ap (fun x => tnat_elim t0 x s2 s3 s4) H1))
               (ap (fun x => tnat_elim t0 t1 x s3 s4) H2))
            (ap (fun x => tnat_elim t0 t1 t2 x s4) H3))
         (ap (fun x => tnat_elim t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_tvec {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tvec s0 s1 = tvec t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tvec x s1) H0))
         (ap (fun x => tvec t0 x) H1)).
Qed.

Lemma congr_tvnil {s0 : term} {t0 : term} (H0 : s0 = t0) :
  tvnil s0 = tvnil t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tvnil x) H0)).
Qed.

Lemma congr_tvcons {s0 : term} {s1 : term} {s2 : term} {t0 : term}
  {t1 : term} {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tvcons s0 s1 s2 = tvcons t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tvcons x s1 s2) H0))
            (ap (fun x => tvcons t0 x s2) H1))
         (ap (fun x => tvcons t0 t1 x) H2)).
Qed.

Lemma congr_tvec_elim {s0 : mode} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {t0 : mode} {t1 : term} {t2 : term}
  {t3 : term} {t4 : term} {t5 : term} {t6 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5)
  (H6 : s6 = t6) :
  tvec_elim s0 s1 s2 s3 s4 s5 s6 = tvec_elim t0 t1 t2 t3 t4 t5 t6.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans eq_refl
                           (ap (fun x => tvec_elim x s1 s2 s3 s4 s5 s6) H0))
                        (ap (fun x => tvec_elim t0 x s2 s3 s4 s5 s6) H1))
                     (ap (fun x => tvec_elim t0 t1 x s3 s4 s5 s6) H2))
                  (ap (fun x => tvec_elim t0 t1 t2 x s4 s5 s6) H3))
               (ap (fun x => tvec_elim t0 t1 t2 t3 x s5 s6) H4))
            (ap (fun x => tvec_elim t0 t1 t2 t3 t4 x s6) H5))
         (ap (fun x => tvec_elim t0 t1 t2 t3 t4 t5 x) H6)).
Qed.

Lemma congr_bot : bot = bot.
Proof.
exact (eq_refl).
Qed.

Lemma congr_bot_elim {s0 : mode} {s1 : term} {s2 : term} {t0 : mode}
  {t1 : term} {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  bot_elim s0 s1 s2 = bot_elim t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => bot_elim x s1 s2) H0))
            (ap (fun x => bot_elim t0 x s2) H1))
         (ap (fun x => bot_elim t0 t1 x) H2)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var s0 => var (xi_term s0)
  | Sort s0 s1 => Sort s0 s1
  | Pi s0 s1 s2 s3 s4 s5 =>
      Pi s0 s1 s2 s3 (ren_term xi_term s4)
        (ren_term (upRen_term_term xi_term) s5)
  | lam s0 s1 s2 =>
      lam s0 (ren_term xi_term s1) (ren_term (upRen_term_term xi_term) s2)
  | app s0 s1 => app (ren_term xi_term s0) (ren_term xi_term s1)
  | Erased s0 => Erased (ren_term xi_term s0)
  | hide s0 => hide (ren_term xi_term s0)
  | reveal s0 s1 s2 =>
      reveal (ren_term xi_term s0) (ren_term xi_term s1)
        (ren_term xi_term s2)
  | Reveal s0 s1 => Reveal (ren_term xi_term s0) (ren_term xi_term s1)
  | toRev s0 s1 s2 =>
      toRev (ren_term xi_term s0) (ren_term xi_term s1) (ren_term xi_term s2)
  | fromRev s0 s1 s2 =>
      fromRev (ren_term xi_term s0) (ren_term xi_term s1)
        (ren_term xi_term s2)
  | gheq s0 s1 s2 =>
      gheq (ren_term xi_term s0) (ren_term xi_term s1) (ren_term xi_term s2)
  | ghrefl s0 s1 => ghrefl (ren_term xi_term s0) (ren_term xi_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      ghcast (ren_term xi_term s0) (ren_term xi_term s1)
        (ren_term xi_term s2) (ren_term xi_term s3) (ren_term xi_term s4)
        (ren_term xi_term s5)
  | tbool => tbool
  | ttrue => ttrue
  | tfalse => tfalse
  | tif s0 s1 s2 s3 s4 =>
      tif s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | tnat => tnat
  | tzero => tzero
  | tsucc s0 => tsucc (ren_term xi_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      tnat_elim s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | tvec s0 s1 => tvec (ren_term xi_term s0) (ren_term xi_term s1)
  | tvnil s0 => tvnil (ren_term xi_term s0)
  | tvcons s0 s1 s2 =>
      tvcons (ren_term xi_term s0) (ren_term xi_term s1)
        (ren_term xi_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      tvec_elim s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3) (ren_term xi_term s4) (ren_term xi_term s5)
        (ren_term xi_term s6)
  | bot => bot
  | bot_elim s0 s1 s2 =>
      bot_elim s0 (ren_term xi_term s1) (ren_term xi_term s2)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | var s0 => sigma_term s0
  | Sort s0 s1 => Sort s0 s1
  | Pi s0 s1 s2 s3 s4 s5 =>
      Pi s0 s1 s2 s3 (subst_term sigma_term s4)
        (subst_term (up_term_term sigma_term) s5)
  | lam s0 s1 s2 =>
      lam s0 (subst_term sigma_term s1)
        (subst_term (up_term_term sigma_term) s2)
  | app s0 s1 => app (subst_term sigma_term s0) (subst_term sigma_term s1)
  | Erased s0 => Erased (subst_term sigma_term s0)
  | hide s0 => hide (subst_term sigma_term s0)
  | reveal s0 s1 s2 =>
      reveal (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | Reveal s0 s1 =>
      Reveal (subst_term sigma_term s0) (subst_term sigma_term s1)
  | toRev s0 s1 s2 =>
      toRev (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | fromRev s0 s1 s2 =>
      fromRev (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | gheq s0 s1 s2 =>
      gheq (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | ghrefl s0 s1 =>
      ghrefl (subst_term sigma_term s0) (subst_term sigma_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      ghcast (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2) (subst_term sigma_term s3)
        (subst_term sigma_term s4) (subst_term sigma_term s5)
  | tbool => tbool
  | ttrue => ttrue
  | tfalse => tfalse
  | tif s0 s1 s2 s3 s4 =>
      tif s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | tnat => tnat
  | tzero => tzero
  | tsucc s0 => tsucc (subst_term sigma_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      tnat_elim s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | tvec s0 s1 => tvec (subst_term sigma_term s0) (subst_term sigma_term s1)
  | tvnil s0 => tvnil (subst_term sigma_term s0)
  | tvcons s0 s1 s2 =>
      tvcons (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      tvec_elim s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5) (subst_term sigma_term s6)
  | bot => bot
  | bot_elim s0 s1 s2 =>
      bot_elim s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
  end.

Lemma upId_term_term (sigma : nat -> term) (Eq : forall x, sigma x = var x) :
  forall x, up_term_term sigma x = var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s2)
  | app s0 s1 =>
      congr_app (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | Erased s0 => congr_Erased (idSubst_term sigma_term Eq_term s0)
  | hide s0 => congr_hide (idSubst_term sigma_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 => congr_tsucc (idSubst_term sigma_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | tvnil s0 => congr_tvnil (idSubst_term sigma_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
        (idSubst_term sigma_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | Erased s0 => congr_Erased (extRen_term xi_term zeta_term Eq_term s0)
  | hide s0 => congr_hide (extRen_term xi_term zeta_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 => congr_tsucc (extRen_term xi_term zeta_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | tvnil s0 => congr_tvnil (extRen_term xi_term zeta_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
        (extRen_term xi_term zeta_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | Erased s0 => congr_Erased (ext_term sigma_term tau_term Eq_term s0)
  | hide s0 => congr_hide (ext_term sigma_term tau_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 => congr_tsucc (ext_term sigma_term tau_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | tvnil s0 => congr_tvnil (ext_term sigma_term tau_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
        (ext_term sigma_term tau_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | Erased s0 =>
      congr_Erased (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | hide s0 =>
      congr_hide (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 =>
      congr_tsucc (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tvnil s0 =>
      congr_tvnil (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s2)
  | app s0 s1 =>
      congr_app (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | Erased s0 =>
      congr_Erased (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | hide s0 =>
      congr_hide (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev
        (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 =>
      congr_tsucc (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tvnil s0 =>
      congr_tvnil (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | Erased s0 =>
      congr_Erased
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | hide s0 =>
      congr_hide
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 =>
      congr_tsucc
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tvnil s0 =>
      congr_tvnil
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | Erased s0 =>
      congr_Erased
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | hide s0 =>
      congr_hide
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 =>
      congr_tsucc
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tvnil s0 =>
      congr_tvnil
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var) xi x = sigma x) :
  forall x, funcomp (var) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 s1 => congr_Sort (eq_refl s0) (eq_refl s1)
  | Pi s0 s1 s2 s3 s4 s5 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (eq_refl s2) (eq_refl s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s5)
  | lam s0 s1 s2 =>
      congr_lam (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s2)
  | app s0 s1 =>
      congr_app (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | Erased s0 => congr_Erased (rinst_inst_term xi_term sigma_term Eq_term s0)
  | hide s0 => congr_hide (rinst_inst_term xi_term sigma_term Eq_term s0)
  | reveal s0 s1 s2 =>
      congr_reveal (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | Reveal s0 s1 =>
      congr_Reveal (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | toRev s0 s1 s2 =>
      congr_toRev (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | fromRev s0 s1 s2 =>
      congr_fromRev (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | gheq s0 s1 s2 =>
      congr_gheq (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | ghrefl s0 s1 =>
      congr_ghrefl (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      congr_ghcast (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
  | tbool => congr_tbool
  | ttrue => congr_ttrue
  | tfalse => congr_tfalse
  | tif s0 s1 s2 s3 s4 =>
      congr_tif (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
  | tnat => congr_tnat
  | tzero => congr_tzero
  | tsucc s0 => congr_tsucc (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tnat_elim s0 s1 s2 s3 s4 =>
      congr_tnat_elim (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
  | tvec s0 s1 =>
      congr_tvec (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tvnil s0 => congr_tvnil (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tvcons s0 s1 s2 =>
      congr_tvcons (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      congr_tvec_elim (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
  | bot => congr_bot
  | bot_elim s0 s1 s2 =>
      congr_bot_elim (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (var) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var) s = s.
Proof.
exact (idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise : pointwise_relation _ eq (subst_term (var)) id.
Proof.
exact (fun s => idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (var x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var)) sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (var x) = var (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var))
    (funcomp (var) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

#[global]Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global]Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global]Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]
Instance VarInstance_term : (Var _ _) := @var.

Notation "[ sigma_term ]" := (subst_term sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_term xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var x) ( at level 5, format "x __term")  :
subst_scope.

#[global]
Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Allfv.

Import
Core.

Lemma upAllfv_term_term (p : nat -> Prop) : nat -> Prop.
Proof.
exact (up_allfv p).
Defined.

Fixpoint allfv_term (p_term : nat -> Prop) (s : term) {struct s} : Prop :=
  match s with
  | var s0 => p_term s0
  | Sort s0 s1 => and True (and True True)
  | Pi s0 s1 s2 s3 s4 s5 =>
      and True
        (and True
           (and True
              (and True
                 (and (allfv_term p_term s4)
                    (and (allfv_term (upAllfv_term_term p_term) s5) True)))))
  | lam s0 s1 s2 =>
      and True
        (and (allfv_term p_term s1)
           (and (allfv_term (upAllfv_term_term p_term) s2) True))
  | app s0 s1 => and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | Erased s0 => and (allfv_term p_term s0) True
  | hide s0 => and (allfv_term p_term s0) True
  | reveal s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | Reveal s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | toRev s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | fromRev s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | gheq s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | ghrefl s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2)
              (and (allfv_term p_term s3)
                 (and (allfv_term p_term s4)
                    (and (allfv_term p_term s5) True)))))
  | tbool => True
  | ttrue => True
  | tfalse => True
  | tif s0 s1 s2 s3 s4 =>
      and True
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2)
              (and (allfv_term p_term s3) (and (allfv_term p_term s4) True))))
  | tnat => True
  | tzero => True
  | tsucc s0 => and (allfv_term p_term s0) True
  | tnat_elim s0 s1 s2 s3 s4 =>
      and True
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2)
              (and (allfv_term p_term s3) (and (allfv_term p_term s4) True))))
  | tvec s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | tvnil s0 => and (allfv_term p_term s0) True
  | tvcons s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      and True
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2)
              (and (allfv_term p_term s3)
                 (and (allfv_term p_term s4)
                    (and (allfv_term p_term s5)
                       (and (allfv_term p_term s6) True))))))
  | bot => True
  | bot_elim s0 s1 s2 =>
      and True (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  end.

Lemma upAllfvTriv_term_term {p : nat -> Prop} (H : forall x, p x) :
  forall x, upAllfv_term_term p x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => I
                end).
Qed.

Fixpoint allfvTriv_term (p_term : nat -> Prop) (H_term : forall x, p_term x)
(s : term) {struct s} : allfv_term p_term s :=
  match s with
  | var s0 => H_term s0
  | Sort s0 s1 => conj I (conj I I)
  | Pi s0 s1 s2 s3 s4 s5 =>
      conj I
        (conj I
           (conj I
              (conj I
                 (conj (allfvTriv_term p_term H_term s4)
                    (conj
                       (allfvTriv_term (upAllfv_term_term p_term)
                          (upAllfvTriv_term_term H_term) s5) I)))))
  | lam s0 s1 s2 =>
      conj I
        (conj (allfvTriv_term p_term H_term s1)
           (conj
              (allfvTriv_term (upAllfv_term_term p_term)
                 (upAllfvTriv_term_term H_term) s2) I))
  | app s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | Erased s0 => conj (allfvTriv_term p_term H_term s0) I
  | hide s0 => conj (allfvTriv_term p_term H_term s0) I
  | reveal s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | Reveal s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | toRev s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | fromRev s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | gheq s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | ghrefl s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj (allfvTriv_term p_term H_term s4)
                    (conj (allfvTriv_term p_term H_term s5) I)))))
  | tbool => I
  | ttrue => I
  | tfalse => I
  | tif s0 s1 s2 s3 s4 =>
      conj I
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj (allfvTriv_term p_term H_term s4) I))))
  | tnat => I
  | tzero => I
  | tsucc s0 => conj (allfvTriv_term p_term H_term s0) I
  | tnat_elim s0 s1 s2 s3 s4 =>
      conj I
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj (allfvTriv_term p_term H_term s4) I))))
  | tvec s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | tvnil s0 => conj (allfvTriv_term p_term H_term s0) I
  | tvcons s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      conj I
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj (allfvTriv_term p_term H_term s4)
                    (conj (allfvTriv_term p_term H_term s5)
                       (conj (allfvTriv_term p_term H_term s6) I))))))
  | bot => I
  | bot_elim s0 s1 s2 =>
      conj I
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  end.

Lemma upAllfvImpl_term_term {p : nat -> Prop} {q : nat -> Prop}
  (H : forall x, p x -> q x) :
  forall x, upAllfv_term_term p x -> upAllfv_term_term q x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => fun Hp => Hp
                end).
Qed.

Fixpoint allfvImpl_term (p_term : nat -> Prop) (q_term : nat -> Prop)
(H_term : forall x, p_term x -> q_term x) (s : term) {struct s} :
allfv_term p_term s -> allfv_term q_term s :=
  match s with
  | var s0 => fun HP => H_term s0 HP
  | Sort s0 s1 => fun HP => conj I (conj I I)
  | Pi s0 s1 s2 s3 s4 s5 =>
      fun HP =>
      conj I
        (conj I
           (conj I
              (conj I
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
                           match HP with
                           | conj _ HP =>
                               match HP with
                               | conj _ HP =>
                                   match HP with
                                   | conj _ HP =>
                                       match HP with
                                       | conj HP _ => HP
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvImpl_term (upAllfv_term_term p_term)
                          (upAllfv_term_term q_term)
                          (upAllfvImpl_term_term H_term) s5
                          match HP with
                          | conj _ HP =>
                              match HP with
                              | conj _ HP =>
                                  match HP with
                                  | conj _ HP =>
                                      match HP with
                                      | conj _ HP =>
                                          match HP with
                                          | conj _ HP =>
                                              match HP with
                                              | conj HP _ => HP
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | lam s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term (upAllfv_term_term p_term)
                 (upAllfv_term_term q_term) (upAllfvImpl_term_term H_term) s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | app s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | Erased s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | hide s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | reveal s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | Reveal s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | toRev s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | fromRev s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | gheq s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | ghrefl s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_term p_term q_term H_term s3
                    match HP with
                    | conj _ HP =>
                        match HP with
                        | conj _ HP =>
                            match HP with
                            | conj _ HP =>
                                match HP with
                                | conj HP _ => HP
                                end
                            end
                        end
                    end)
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
                           match HP with
                           | conj _ HP =>
                               match HP with
                               | conj _ HP =>
                                   match HP with
                                   | conj _ HP =>
                                       match HP with
                                       | conj HP _ => HP
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvImpl_term p_term q_term H_term s5
                          match HP with
                          | conj _ HP =>
                              match HP with
                              | conj _ HP =>
                                  match HP with
                                  | conj _ HP =>
                                      match HP with
                                      | conj _ HP =>
                                          match HP with
                                          | conj _ HP =>
                                              match HP with
                                              | conj HP _ => HP
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | tbool => fun HP => I
  | ttrue => fun HP => I
  | tfalse => fun HP => I
  | tif s0 s1 s2 s3 s4 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_term p_term q_term H_term s3
                    match HP with
                    | conj _ HP =>
                        match HP with
                        | conj _ HP =>
                            match HP with
                            | conj _ HP =>
                                match HP with
                                | conj HP _ => HP
                                end
                            end
                        end
                    end)
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
                           match HP with
                           | conj _ HP =>
                               match HP with
                               | conj _ HP =>
                                   match HP with
                                   | conj _ HP =>
                                       match HP with
                                       | conj HP _ => HP
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tnat => fun HP => I
  | tzero => fun HP => I
  | tsucc s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | tnat_elim s0 s1 s2 s3 s4 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_term p_term q_term H_term s3
                    match HP with
                    | conj _ HP =>
                        match HP with
                        | conj _ HP =>
                            match HP with
                            | conj _ HP =>
                                match HP with
                                | conj HP _ => HP
                                end
                            end
                        end
                    end)
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
                           match HP with
                           | conj _ HP =>
                               match HP with
                               | conj _ HP =>
                                   match HP with
                                   | conj _ HP =>
                                       match HP with
                                       | conj HP _ => HP
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tvec s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tvnil s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | tvcons s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_term p_term q_term H_term s3
                    match HP with
                    | conj _ HP =>
                        match HP with
                        | conj _ HP =>
                            match HP with
                            | conj _ HP =>
                                match HP with
                                | conj HP _ => HP
                                end
                            end
                        end
                    end)
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
                           match HP with
                           | conj _ HP =>
                               match HP with
                               | conj _ HP =>
                                   match HP with
                                   | conj _ HP =>
                                       match HP with
                                       | conj HP _ => HP
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvImpl_term p_term q_term H_term s5
                          match HP with
                          | conj _ HP =>
                              match HP with
                              | conj _ HP =>
                                  match HP with
                                  | conj _ HP =>
                                      match HP with
                                      | conj _ HP =>
                                          match HP with
                                          | conj _ HP =>
                                              match HP with
                                              | conj HP _ => HP
                                              end
                                          end
                                      end
                                  end
                              end
                          end)
                       (conj
                          (allfvImpl_term p_term q_term H_term s6
                             match HP with
                             | conj _ HP =>
                                 match HP with
                                 | conj _ HP =>
                                     match HP with
                                     | conj _ HP =>
                                         match HP with
                                         | conj _ HP =>
                                             match HP with
                                             | conj _ HP =>
                                                 match HP with
                                                 | conj _ HP =>
                                                     match HP with
                                                     | conj HP _ => HP
                                                     end
                                                 end
                                             end
                                         end
                                     end
                                 end
                             end) I))))))
  | bot => fun HP => I
  | bot_elim s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  end.

Lemma upAllfvRenL_term_term (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_term_term p (upRen_term_term xi x) ->
  upAllfv_term_term (funcomp p xi) x.
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenL_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term p_term (ren_term xi_term s) ->
allfv_term (funcomp p_term xi_term) s :=
  match s with
  | var s0 => fun H => H
  | Sort s0 s1 => fun H => conj I (conj I I)
  | Pi s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj I
        (conj I
           (conj I
              (conj I
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvImpl_term _ _
                          (upAllfvRenL_term_term p_term xi_term) s5
                          (allfvRenL_term (upAllfv_term_term p_term)
                             (upRen_term_term xi_term) s5
                             match H with
                             | conj _ H =>
                                 match H with
                                 | conj _ H =>
                                     match H with
                                     | conj _ H =>
                                         match H with
                                         | conj _ H =>
                                             match H with
                                             | conj _ H =>
                                                 match H with
                                                 | conj H _ => H
                                                 end
                                             end
                                         end
                                     end
                                 end
                             end)) I)))))
  | lam s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvImpl_term _ _ (upAllfvRenL_term_term p_term xi_term) s2
                 (allfvRenL_term (upAllfv_term_term p_term)
                    (upRen_term_term xi_term) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | app s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | Erased s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | hide s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | reveal s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | Reveal s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | toRev s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | fromRev s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | gheq s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ghrefl s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenL_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | tbool => fun H => I
  | ttrue => fun H => I
  | tfalse => fun H => I
  | tif s0 s1 s2 s3 s4 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tnat => fun H => I
  | tzero => fun H => I
  | tsucc s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tnat_elim s0 s1 s2 s3 s4 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tvec s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tvnil s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tvcons s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenL_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end)
                       (conj
                          (allfvRenL_term p_term xi_term s6
                             match H with
                             | conj _ H =>
                                 match H with
                                 | conj _ H =>
                                     match H with
                                     | conj _ H =>
                                         match H with
                                         | conj _ H =>
                                             match H with
                                             | conj _ H =>
                                                 match H with
                                                 | conj _ H =>
                                                     match H with
                                                     | conj H _ => H
                                                     end
                                                 end
                                             end
                                         end
                                     end
                                 end
                             end) I))))))
  | bot => fun H => I
  | bot_elim s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  end.

Lemma upAllfvRenR_term_term (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_term_term (funcomp p xi) x ->
  upAllfv_term_term p (upRen_term_term xi x).
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenR_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term (funcomp p_term xi_term) s ->
allfv_term p_term (ren_term xi_term s) :=
  match s with
  | var s0 => fun H => H
  | Sort s0 s1 => fun H => conj I (conj I I)
  | Pi s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj I
        (conj I
           (conj I
              (conj I
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenR_term (upAllfv_term_term p_term)
                          (upRen_term_term xi_term) s5
                          (allfvImpl_term _ _
                             (upAllfvRenR_term_term p_term xi_term) s5
                             match H with
                             | conj _ H =>
                                 match H with
                                 | conj _ H =>
                                     match H with
                                     | conj _ H =>
                                         match H with
                                         | conj _ H =>
                                             match H with
                                             | conj _ H =>
                                                 match H with
                                                 | conj H _ => H
                                                 end
                                             end
                                         end
                                     end
                                 end
                             end)) I)))))
  | lam s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term (upAllfv_term_term p_term)
                 (upRen_term_term xi_term) s2
                 (allfvImpl_term _ _ (upAllfvRenR_term_term p_term xi_term)
                    s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | app s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | Erased s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | hide s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | reveal s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | Reveal s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | toRev s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | fromRev s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | gheq s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ghrefl s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | ghcast s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenR_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | tbool => fun H => I
  | ttrue => fun H => I
  | tfalse => fun H => I
  | tif s0 s1 s2 s3 s4 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tnat => fun H => I
  | tzero => fun H => I
  | tsucc s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tnat_elim s0 s1 s2 s3 s4 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end) I))))
  | tvec s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tvnil s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tvcons s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | tvec_elim s0 s1 s2 s3 s4 s5 s6 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end)
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenR_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end)
                       (conj
                          (allfvRenR_term p_term xi_term s6
                             match H with
                             | conj _ H =>
                                 match H with
                                 | conj _ H =>
                                     match H with
                                     | conj _ H =>
                                         match H with
                                         | conj _ H =>
                                             match H with
                                             | conj _ H =>
                                                 match H with
                                                 | conj _ H =>
                                                     match H with
                                                     | conj H _ => H
                                                     end
                                                 end
                                             end
                                         end
                                     end
                                 end
                             end) I))))))
  | bot => fun H => I
  | bot_elim s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  end.

End Allfv.

Module Extra.

Import Core.

#[global]Hint Opaque subst_term: rewrite.

#[global]Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Allfv.

Export Extra.

End interface.

Export interface.


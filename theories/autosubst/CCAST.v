From GhostTT.autosubst Require Import core unscoped.
From GhostTT Require Import BasicAST.
From Coq Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive cterm : Type :=
  | cvar : nat -> cterm
  | cSort : cmode -> level -> cterm
  | cPi : cmode -> cterm -> cterm -> cterm
  | clam : cmode -> cterm -> cterm -> cterm
  | capp : cterm -> cterm -> cterm
  | cunit : cterm
  | ctt : cterm
  | ctop : cterm
  | cstar : cterm
  | cbot : cterm
  | cbot_elim : cmode -> cterm -> cterm -> cterm
  | cty : level -> cterm
  | ctyval : mark -> cterm -> cterm -> cterm
  | ctyerr : cterm
  | cEl : cterm -> cterm
  | cErr : cterm -> cterm
  | squash : cterm -> cterm
  | sq : cterm -> cterm
  | sq_elim : cterm -> cterm -> cterm -> cterm
  | teq : cterm -> cterm -> cterm -> cterm
  | trefl : cterm -> cterm -> cterm
  | tJ : cterm -> cterm -> cterm -> cterm
  | ebool : cterm
  | etrue : cterm
  | efalse : cterm
  | bool_err : cterm
  | eif : cmode -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
  | pbool : cterm
  | ptrue : cterm
  | pfalse : cterm
  | pif : cterm -> cterm -> cterm -> cterm -> cterm
  | enat : cterm
  | ezero : cterm
  | esucc : cterm -> cterm
  | enat_elim : cterm -> cterm -> cterm -> cterm -> cterm
  | pnat : cterm
  | pzero : cterm
  | psucc : cterm -> cterm
  | pnat_elim :
      cterm ->
      cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
  | pnat_elimP : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
  | evec : cterm -> cterm
  | evnil : cterm -> cterm
  | evcons : cterm -> cterm -> cterm
  | evec_elim : cterm -> cterm -> cterm -> cterm -> cterm
  | pvec : cterm -> cterm -> cterm -> cterm -> cterm
  | pvnil : cterm -> cterm
  | pvcons : cterm -> cterm -> cterm -> cterm
  | pvec_elim :
      cterm ->
      cterm ->
      cterm ->
      cterm ->
      cterm ->
      cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
  | pvec_elimG :
      cterm ->
      cterm ->
      cterm ->
      cterm ->
      cterm ->
      cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
  | pvec_elimP :
      cterm ->
      cterm ->
      cterm ->
      cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm.

Lemma congr_cSort {s0 : cmode} {s1 : level} {t0 : cmode} {t1 : level}
  (H0 : s0 = t0) (H1 : s1 = t1) : cSort s0 s1 = cSort t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cSort x s1) H0))
         (ap (fun x => cSort t0 x) H1)).
Qed.

Lemma congr_cPi {s0 : cmode} {s1 : cterm} {s2 : cterm} {t0 : cmode}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cPi s0 s1 s2 = cPi t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cPi x s1 s2) H0))
            (ap (fun x => cPi t0 x s2) H1)) (ap (fun x => cPi t0 t1 x) H2)).
Qed.

Lemma congr_clam {s0 : cmode} {s1 : cterm} {s2 : cterm} {t0 : cmode}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  clam s0 s1 s2 = clam t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => clam x s1 s2) H0))
            (ap (fun x => clam t0 x s2) H1)) (ap (fun x => clam t0 t1 x) H2)).
Qed.

Lemma congr_capp {s0 : cterm} {s1 : cterm} {t0 : cterm} {t1 : cterm}
  (H0 : s0 = t0) (H1 : s1 = t1) : capp s0 s1 = capp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => capp x s1) H0))
         (ap (fun x => capp t0 x) H1)).
Qed.

Lemma congr_cunit : cunit = cunit.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ctt : ctt = ctt.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ctop : ctop = ctop.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cstar : cstar = cstar.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cbot : cbot = cbot.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cbot_elim {s0 : cmode} {s1 : cterm} {s2 : cterm} {t0 : cmode}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cbot_elim s0 s1 s2 = cbot_elim t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cbot_elim x s1 s2) H0))
            (ap (fun x => cbot_elim t0 x s2) H1))
         (ap (fun x => cbot_elim t0 t1 x) H2)).
Qed.

Lemma congr_cty {s0 : level} {t0 : level} (H0 : s0 = t0) : cty s0 = cty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => cty x) H0)).
Qed.

Lemma congr_ctyval {s0 : mark} {s1 : cterm} {s2 : cterm} {t0 : mark}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  ctyval s0 s1 s2 = ctyval t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => ctyval x s1 s2) H0))
            (ap (fun x => ctyval t0 x s2) H1))
         (ap (fun x => ctyval t0 t1 x) H2)).
Qed.

Lemma congr_ctyerr : ctyerr = ctyerr.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cEl {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) : cEl s0 = cEl t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => cEl x) H0)).
Qed.

Lemma congr_cErr {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) : cErr s0 = cErr t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => cErr x) H0)).
Qed.

Lemma congr_squash {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) :
  squash s0 = squash t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => squash x) H0)).
Qed.

Lemma congr_sq {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) : sq s0 = sq t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => sq x) H0)).
Qed.

Lemma congr_sq_elim {s0 : cterm} {s1 : cterm} {s2 : cterm} {t0 : cterm}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  sq_elim s0 s1 s2 = sq_elim t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => sq_elim x s1 s2) H0))
            (ap (fun x => sq_elim t0 x s2) H1))
         (ap (fun x => sq_elim t0 t1 x) H2)).
Qed.

Lemma congr_teq {s0 : cterm} {s1 : cterm} {s2 : cterm} {t0 : cterm}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  teq s0 s1 s2 = teq t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => teq x s1 s2) H0))
            (ap (fun x => teq t0 x s2) H1)) (ap (fun x => teq t0 t1 x) H2)).
Qed.

Lemma congr_trefl {s0 : cterm} {s1 : cterm} {t0 : cterm} {t1 : cterm}
  (H0 : s0 = t0) (H1 : s1 = t1) : trefl s0 s1 = trefl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => trefl x s1) H0))
         (ap (fun x => trefl t0 x) H1)).
Qed.

Lemma congr_tJ {s0 : cterm} {s1 : cterm} {s2 : cterm} {t0 : cterm}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tJ s0 s1 s2 = tJ t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tJ x s1 s2) H0))
            (ap (fun x => tJ t0 x s2) H1)) (ap (fun x => tJ t0 t1 x) H2)).
Qed.

Lemma congr_ebool : ebool = ebool.
Proof.
exact (eq_refl).
Qed.

Lemma congr_etrue : etrue = etrue.
Proof.
exact (eq_refl).
Qed.

Lemma congr_efalse : efalse = efalse.
Proof.
exact (eq_refl).
Qed.

Lemma congr_bool_err : bool_err = bool_err.
Proof.
exact (eq_refl).
Qed.

Lemma congr_eif {s0 : cmode} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {t0 : cmode} {t1 : cterm} {t2 : cterm}
  {t3 : cterm} {t4 : cterm} {t5 : cterm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  eif s0 s1 s2 s3 s4 s5 = eif t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => eif x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => eif t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => eif t0 t1 x s3 s4 s5) H2))
               (ap (fun x => eif t0 t1 t2 x s4 s5) H3))
            (ap (fun x => eif t0 t1 t2 t3 x s5) H4))
         (ap (fun x => eif t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_pbool : pbool = pbool.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ptrue : ptrue = ptrue.
Proof.
exact (eq_refl).
Qed.

Lemma congr_pfalse : pfalse = pfalse.
Proof.
exact (eq_refl).
Qed.

Lemma congr_pif {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {t0 : cterm} {t1 : cterm} {t2 : cterm} {t3 : cterm} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  pif s0 s1 s2 s3 = pif t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => pif x s1 s2 s3) H0))
               (ap (fun x => pif t0 x s2 s3) H1))
            (ap (fun x => pif t0 t1 x s3) H2))
         (ap (fun x => pif t0 t1 t2 x) H3)).
Qed.

Lemma congr_enat : enat = enat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ezero : ezero = ezero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_esucc {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) :
  esucc s0 = esucc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => esucc x) H0)).
Qed.

Lemma congr_enat_elim {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {t0 : cterm} {t1 : cterm} {t2 : cterm} {t3 : cterm} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  enat_elim s0 s1 s2 s3 = enat_elim t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans eq_refl (ap (fun x => enat_elim x s1 s2 s3) H0))
               (ap (fun x => enat_elim t0 x s2 s3) H1))
            (ap (fun x => enat_elim t0 t1 x s3) H2))
         (ap (fun x => enat_elim t0 t1 t2 x) H3)).
Qed.

Lemma congr_pnat : pnat = pnat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_pzero : pzero = pzero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_psucc {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) :
  psucc s0 = psucc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => psucc x) H0)).
Qed.

Lemma congr_pnat_elim {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {s6 : cterm} {s7 : cterm} {t0 : cterm}
  {t1 : cterm} {t2 : cterm} {t3 : cterm} {t4 : cterm} {t5 : cterm}
  {t6 : cterm} {t7 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  : pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 = pnat_elim t0 t1 t2 t3 t4 t5 t6 t7.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans eq_refl
                              (ap (fun x => pnat_elim x s1 s2 s3 s4 s5 s6 s7)
                                 H0))
                           (ap (fun x => pnat_elim t0 x s2 s3 s4 s5 s6 s7) H1))
                        (ap (fun x => pnat_elim t0 t1 x s3 s4 s5 s6 s7) H2))
                     (ap (fun x => pnat_elim t0 t1 t2 x s4 s5 s6 s7) H3))
                  (ap (fun x => pnat_elim t0 t1 t2 t3 x s5 s6 s7) H4))
               (ap (fun x => pnat_elim t0 t1 t2 t3 t4 x s6 s7) H5))
            (ap (fun x => pnat_elim t0 t1 t2 t3 t4 t5 x s7) H6))
         (ap (fun x => pnat_elim t0 t1 t2 t3 t4 t5 t6 x) H7)).
Qed.

Lemma congr_pnat_elimP {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {t0 : cterm} {t1 : cterm} {t2 : cterm}
  {t3 : cterm} {t4 : cterm} {t5 : cterm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  pnat_elimP s0 s1 s2 s3 s4 s5 = pnat_elimP t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => pnat_elimP x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => pnat_elimP t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => pnat_elimP t0 t1 x s3 s4 s5) H2))
               (ap (fun x => pnat_elimP t0 t1 t2 x s4 s5) H3))
            (ap (fun x => pnat_elimP t0 t1 t2 t3 x s5) H4))
         (ap (fun x => pnat_elimP t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_evec {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) : evec s0 = evec t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => evec x) H0)).
Qed.

Lemma congr_evnil {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) :
  evnil s0 = evnil t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => evnil x) H0)).
Qed.

Lemma congr_evcons {s0 : cterm} {s1 : cterm} {t0 : cterm} {t1 : cterm}
  (H0 : s0 = t0) (H1 : s1 = t1) : evcons s0 s1 = evcons t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => evcons x s1) H0))
         (ap (fun x => evcons t0 x) H1)).
Qed.

Lemma congr_evec_elim {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {t0 : cterm} {t1 : cterm} {t2 : cterm} {t3 : cterm} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  evec_elim s0 s1 s2 s3 = evec_elim t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans eq_refl (ap (fun x => evec_elim x s1 s2 s3) H0))
               (ap (fun x => evec_elim t0 x s2 s3) H1))
            (ap (fun x => evec_elim t0 t1 x s3) H2))
         (ap (fun x => evec_elim t0 t1 t2 x) H3)).
Qed.

Lemma congr_pvec {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {t0 : cterm} {t1 : cterm} {t2 : cterm} {t3 : cterm} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  pvec s0 s1 s2 s3 = pvec t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => pvec x s1 s2 s3) H0))
               (ap (fun x => pvec t0 x s2 s3) H1))
            (ap (fun x => pvec t0 t1 x s3) H2))
         (ap (fun x => pvec t0 t1 t2 x) H3)).
Qed.

Lemma congr_pvnil {s0 : cterm} {t0 : cterm} (H0 : s0 = t0) :
  pvnil s0 = pvnil t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pvnil x) H0)).
Qed.

Lemma congr_pvcons {s0 : cterm} {s1 : cterm} {s2 : cterm} {t0 : cterm}
  {t1 : cterm} {t2 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  pvcons s0 s1 s2 = pvcons t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => pvcons x s1 s2) H0))
            (ap (fun x => pvcons t0 x s2) H1))
         (ap (fun x => pvcons t0 t1 x) H2)).
Qed.

Lemma congr_pvec_elim {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {s6 : cterm} {s7 : cterm} {s8 : cterm}
  {s9 : cterm} {s10 : cterm} {s11 : cterm} {t0 : cterm} {t1 : cterm}
  {t2 : cterm} {t3 : cterm} {t4 : cterm} {t5 : cterm} {t6 : cterm}
  {t7 : cterm} {t8 : cterm} {t9 : cterm} {t10 : cterm} {t11 : cterm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) (H8 : s8 = t8) (H9 : s9 = t9)
  (H10 : s10 = t10) (H11 : s11 = t11) :
  pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =
  pvec_elim t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans
                              (eq_trans
                                 (eq_trans
                                    (eq_trans
                                       (eq_trans eq_refl
                                          (ap
                                             (fun x =>
                                              pvec_elim x s1 s2 s3 s4 s5 s6
                                                s7 s8 s9 s10 s11) H0))
                                       (ap
                                          (fun x =>
                                           pvec_elim t0 x s2 s3 s4 s5 s6 s7
                                             s8 s9 s10 s11) H1))
                                    (ap
                                       (fun x =>
                                        pvec_elim t0 t1 x s3 s4 s5 s6 s7 s8
                                          s9 s10 s11) H2))
                                 (ap
                                    (fun x =>
                                     pvec_elim t0 t1 t2 x s4 s5 s6 s7 s8 s9
                                       s10 s11) H3))
                              (ap
                                 (fun x =>
                                  pvec_elim t0 t1 t2 t3 x s5 s6 s7 s8 s9 s10
                                    s11) H4))
                           (ap
                              (fun x =>
                               pvec_elim t0 t1 t2 t3 t4 x s6 s7 s8 s9 s10 s11)
                              H5))
                        (ap
                           (fun x =>
                            pvec_elim t0 t1 t2 t3 t4 t5 x s7 s8 s9 s10 s11)
                           H6))
                     (ap
                        (fun x =>
                         pvec_elim t0 t1 t2 t3 t4 t5 t6 x s8 s9 s10 s11) H7))
                  (ap
                     (fun x => pvec_elim t0 t1 t2 t3 t4 t5 t6 t7 x s9 s10 s11)
                     H8))
               (ap (fun x => pvec_elim t0 t1 t2 t3 t4 t5 t6 t7 t8 x s10 s11)
                  H9))
            (ap (fun x => pvec_elim t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 x s11) H10))
         (ap (fun x => pvec_elim t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 x) H11)).
Qed.

Lemma congr_pvec_elimG {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {s6 : cterm} {s7 : cterm} {s8 : cterm}
  {s9 : cterm} {s10 : cterm} {s11 : cterm} {t0 : cterm} {t1 : cterm}
  {t2 : cterm} {t3 : cterm} {t4 : cterm} {t5 : cterm} {t6 : cterm}
  {t7 : cterm} {t8 : cterm} {t9 : cterm} {t10 : cterm} {t11 : cterm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) (H8 : s8 = t8) (H9 : s9 = t9)
  (H10 : s10 = t10) (H11 : s11 = t11) :
  pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =
  pvec_elimG t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans
                              (eq_trans
                                 (eq_trans
                                    (eq_trans
                                       (eq_trans eq_refl
                                          (ap
                                             (fun x =>
                                              pvec_elimG x s1 s2 s3 s4 s5 s6
                                                s7 s8 s9 s10 s11) H0))
                                       (ap
                                          (fun x =>
                                           pvec_elimG t0 x s2 s3 s4 s5 s6 s7
                                             s8 s9 s10 s11) H1))
                                    (ap
                                       (fun x =>
                                        pvec_elimG t0 t1 x s3 s4 s5 s6 s7 s8
                                          s9 s10 s11) H2))
                                 (ap
                                    (fun x =>
                                     pvec_elimG t0 t1 t2 x s4 s5 s6 s7 s8 s9
                                       s10 s11) H3))
                              (ap
                                 (fun x =>
                                  pvec_elimG t0 t1 t2 t3 x s5 s6 s7 s8 s9 s10
                                    s11) H4))
                           (ap
                              (fun x =>
                               pvec_elimG t0 t1 t2 t3 t4 x s6 s7 s8 s9 s10
                                 s11) H5))
                        (ap
                           (fun x =>
                            pvec_elimG t0 t1 t2 t3 t4 t5 x s7 s8 s9 s10 s11)
                           H6))
                     (ap
                        (fun x =>
                         pvec_elimG t0 t1 t2 t3 t4 t5 t6 x s8 s9 s10 s11) H7))
                  (ap
                     (fun x =>
                      pvec_elimG t0 t1 t2 t3 t4 t5 t6 t7 x s9 s10 s11) H8))
               (ap (fun x => pvec_elimG t0 t1 t2 t3 t4 t5 t6 t7 t8 x s10 s11)
                  H9))
            (ap (fun x => pvec_elimG t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 x s11) H10))
         (ap (fun x => pvec_elimG t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 x) H11)).
Qed.

Lemma congr_pvec_elimP {s0 : cterm} {s1 : cterm} {s2 : cterm} {s3 : cterm}
  {s4 : cterm} {s5 : cterm} {s6 : cterm} {s7 : cterm} {s8 : cterm}
  {s9 : cterm} {t0 : cterm} {t1 : cterm} {t2 : cterm} {t3 : cterm}
  {t4 : cterm} {t5 : cterm} {t6 : cterm} {t7 : cterm} {t8 : cterm}
  {t9 : cterm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3)
  (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) (H8 : s8 = t8)
  (H9 : s9 = t9) :
  pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  pvec_elimP t0 t1 t2 t3 t4 t5 t6 t7 t8 t9.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans
                              (eq_trans
                                 (eq_trans eq_refl
                                    (ap
                                       (fun x =>
                                        pvec_elimP x s1 s2 s3 s4 s5 s6 s7 s8
                                          s9) H0))
                                 (ap
                                    (fun x =>
                                     pvec_elimP t0 x s2 s3 s4 s5 s6 s7 s8 s9)
                                    H1))
                              (ap
                                 (fun x =>
                                  pvec_elimP t0 t1 x s3 s4 s5 s6 s7 s8 s9) H2))
                           (ap
                              (fun x =>
                               pvec_elimP t0 t1 t2 x s4 s5 s6 s7 s8 s9) H3))
                        (ap
                           (fun x => pvec_elimP t0 t1 t2 t3 x s5 s6 s7 s8 s9)
                           H4))
                     (ap (fun x => pvec_elimP t0 t1 t2 t3 t4 x s6 s7 s8 s9)
                        H5))
                  (ap (fun x => pvec_elimP t0 t1 t2 t3 t4 t5 x s7 s8 s9) H6))
               (ap (fun x => pvec_elimP t0 t1 t2 t3 t4 t5 t6 x s8 s9) H7))
            (ap (fun x => pvec_elimP t0 t1 t2 t3 t4 t5 t6 t7 x s9) H8))
         (ap (fun x => pvec_elimP t0 t1 t2 t3 t4 t5 t6 t7 t8 x) H9)).
Qed.

Lemma upRen_cterm_cterm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_cterm (xi_cterm : nat -> nat) (s : cterm) {struct s} : cterm :=
  match s with
  | cvar s0 => cvar (xi_cterm s0)
  | cSort s0 s1 => cSort s0 s1
  | cPi s0 s1 s2 =>
      cPi s0 (ren_cterm xi_cterm s1)
        (ren_cterm (upRen_cterm_cterm xi_cterm) s2)
  | clam s0 s1 s2 =>
      clam s0 (ren_cterm xi_cterm s1)
        (ren_cterm (upRen_cterm_cterm xi_cterm) s2)
  | capp s0 s1 => capp (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
  | cunit => cunit
  | ctt => ctt
  | ctop => ctop
  | cstar => cstar
  | cbot => cbot
  | cbot_elim s0 s1 s2 =>
      cbot_elim s0 (ren_cterm xi_cterm s1) (ren_cterm xi_cterm s2)
  | cty s0 => cty s0
  | ctyval s0 s1 s2 =>
      ctyval s0 (ren_cterm xi_cterm s1) (ren_cterm xi_cterm s2)
  | ctyerr => ctyerr
  | cEl s0 => cEl (ren_cterm xi_cterm s0)
  | cErr s0 => cErr (ren_cterm xi_cterm s0)
  | squash s0 => squash (ren_cterm xi_cterm s0)
  | sq s0 => sq (ren_cterm xi_cterm s0)
  | sq_elim s0 s1 s2 =>
      sq_elim (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2)
  | teq s0 s1 s2 =>
      teq (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2)
  | trefl s0 s1 => trefl (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
  | tJ s0 s1 s2 =>
      tJ (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2)
  | ebool => ebool
  | etrue => etrue
  | efalse => efalse
  | bool_err => bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      eif s0 (ren_cterm xi_cterm s1) (ren_cterm xi_cterm s2)
        (ren_cterm xi_cterm s3) (ren_cterm xi_cterm s4)
        (ren_cterm xi_cterm s5)
  | pbool => pbool
  | ptrue => ptrue
  | pfalse => pfalse
  | pif s0 s1 s2 s3 =>
      pif (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
  | enat => enat
  | ezero => ezero
  | esucc s0 => esucc (ren_cterm xi_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      enat_elim (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
  | pnat => pnat
  | pzero => pzero
  | psucc s0 => psucc (ren_cterm xi_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      pnat_elim (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
        (ren_cterm xi_cterm s4) (ren_cterm xi_cterm s5)
        (ren_cterm xi_cterm s6) (ren_cterm xi_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      pnat_elimP (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
        (ren_cterm xi_cterm s4) (ren_cterm xi_cterm s5)
  | evec s0 => evec (ren_cterm xi_cterm s0)
  | evnil s0 => evnil (ren_cterm xi_cterm s0)
  | evcons s0 s1 => evcons (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      evec_elim (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
  | pvec s0 s1 s2 s3 =>
      pvec (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
  | pvnil s0 => pvnil (ren_cterm xi_cterm s0)
  | pvcons s0 s1 s2 =>
      pvcons (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      pvec_elim (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
        (ren_cterm xi_cterm s4) (ren_cterm xi_cterm s5)
        (ren_cterm xi_cterm s6) (ren_cterm xi_cterm s7)
        (ren_cterm xi_cterm s8) (ren_cterm xi_cterm s9)
        (ren_cterm xi_cterm s10) (ren_cterm xi_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      pvec_elimG (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
        (ren_cterm xi_cterm s4) (ren_cterm xi_cterm s5)
        (ren_cterm xi_cterm s6) (ren_cterm xi_cterm s7)
        (ren_cterm xi_cterm s8) (ren_cterm xi_cterm s9)
        (ren_cterm xi_cterm s10) (ren_cterm xi_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      pvec_elimP (ren_cterm xi_cterm s0) (ren_cterm xi_cterm s1)
        (ren_cterm xi_cterm s2) (ren_cterm xi_cterm s3)
        (ren_cterm xi_cterm s4) (ren_cterm xi_cterm s5)
        (ren_cterm xi_cterm s6) (ren_cterm xi_cterm s7)
        (ren_cterm xi_cterm s8) (ren_cterm xi_cterm s9)
  end.

Lemma up_cterm_cterm (sigma : nat -> cterm) : nat -> cterm.
Proof.
exact (scons (cvar var_zero) (funcomp (ren_cterm shift) sigma)).
Defined.

Fixpoint subst_cterm (sigma_cterm : nat -> cterm) (s : cterm) {struct s} :
cterm :=
  match s with
  | cvar s0 => sigma_cterm s0
  | cSort s0 s1 => cSort s0 s1
  | cPi s0 s1 s2 =>
      cPi s0 (subst_cterm sigma_cterm s1)
        (subst_cterm (up_cterm_cterm sigma_cterm) s2)
  | clam s0 s1 s2 =>
      clam s0 (subst_cterm sigma_cterm s1)
        (subst_cterm (up_cterm_cterm sigma_cterm) s2)
  | capp s0 s1 =>
      capp (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
  | cunit => cunit
  | ctt => ctt
  | ctop => ctop
  | cstar => cstar
  | cbot => cbot
  | cbot_elim s0 s1 s2 =>
      cbot_elim s0 (subst_cterm sigma_cterm s1) (subst_cterm sigma_cterm s2)
  | cty s0 => cty s0
  | ctyval s0 s1 s2 =>
      ctyval s0 (subst_cterm sigma_cterm s1) (subst_cterm sigma_cterm s2)
  | ctyerr => ctyerr
  | cEl s0 => cEl (subst_cterm sigma_cterm s0)
  | cErr s0 => cErr (subst_cterm sigma_cterm s0)
  | squash s0 => squash (subst_cterm sigma_cterm s0)
  | sq s0 => sq (subst_cterm sigma_cterm s0)
  | sq_elim s0 s1 s2 =>
      sq_elim (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2)
  | teq s0 s1 s2 =>
      teq (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2)
  | trefl s0 s1 =>
      trefl (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
  | tJ s0 s1 s2 =>
      tJ (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2)
  | ebool => ebool
  | etrue => etrue
  | efalse => efalse
  | bool_err => bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      eif s0 (subst_cterm sigma_cterm s1) (subst_cterm sigma_cterm s2)
        (subst_cterm sigma_cterm s3) (subst_cterm sigma_cterm s4)
        (subst_cterm sigma_cterm s5)
  | pbool => pbool
  | ptrue => ptrue
  | pfalse => pfalse
  | pif s0 s1 s2 s3 =>
      pif (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
  | enat => enat
  | ezero => ezero
  | esucc s0 => esucc (subst_cterm sigma_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      enat_elim (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
  | pnat => pnat
  | pzero => pzero
  | psucc s0 => psucc (subst_cterm sigma_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      pnat_elim (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
        (subst_cterm sigma_cterm s4) (subst_cterm sigma_cterm s5)
        (subst_cterm sigma_cterm s6) (subst_cterm sigma_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      pnat_elimP (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
        (subst_cterm sigma_cterm s4) (subst_cterm sigma_cterm s5)
  | evec s0 => evec (subst_cterm sigma_cterm s0)
  | evnil s0 => evnil (subst_cterm sigma_cterm s0)
  | evcons s0 s1 =>
      evcons (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      evec_elim (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
  | pvec s0 s1 s2 s3 =>
      pvec (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
  | pvnil s0 => pvnil (subst_cterm sigma_cterm s0)
  | pvcons s0 s1 s2 =>
      pvcons (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      pvec_elim (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
        (subst_cterm sigma_cterm s4) (subst_cterm sigma_cterm s5)
        (subst_cterm sigma_cterm s6) (subst_cterm sigma_cterm s7)
        (subst_cterm sigma_cterm s8) (subst_cterm sigma_cterm s9)
        (subst_cterm sigma_cterm s10) (subst_cterm sigma_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      pvec_elimG (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
        (subst_cterm sigma_cterm s4) (subst_cterm sigma_cterm s5)
        (subst_cterm sigma_cterm s6) (subst_cterm sigma_cterm s7)
        (subst_cterm sigma_cterm s8) (subst_cterm sigma_cterm s9)
        (subst_cterm sigma_cterm s10) (subst_cterm sigma_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      pvec_elimP (subst_cterm sigma_cterm s0) (subst_cterm sigma_cterm s1)
        (subst_cterm sigma_cterm s2) (subst_cterm sigma_cterm s3)
        (subst_cterm sigma_cterm s4) (subst_cterm sigma_cterm s5)
        (subst_cterm sigma_cterm s6) (subst_cterm sigma_cterm s7)
        (subst_cterm sigma_cterm s8) (subst_cterm sigma_cterm s9)
  end.

Lemma upId_cterm_cterm (sigma : nat -> cterm)
  (Eq : forall x, sigma x = cvar x) :
  forall x, up_cterm_cterm sigma x = cvar x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_cterm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_cterm (sigma_cterm : nat -> cterm)
(Eq_cterm : forall x, sigma_cterm x = cvar x) (s : cterm) {struct s} :
subst_cterm sigma_cterm s = s :=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0) (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm (up_cterm_cterm sigma_cterm)
           (upId_cterm_cterm _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0) (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm (up_cterm_cterm sigma_cterm)
           (upId_cterm_cterm _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0) (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0) (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 => congr_cEl (idSubst_cterm sigma_cterm Eq_cterm s0)
  | cErr s0 => congr_cErr (idSubst_cterm sigma_cterm Eq_cterm s0)
  | squash s0 => congr_squash (idSubst_cterm sigma_cterm Eq_cterm s0)
  | sq s0 => congr_sq (idSubst_cterm sigma_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0) (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (idSubst_cterm sigma_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 => congr_psucc (idSubst_cterm sigma_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
        (idSubst_cterm sigma_cterm Eq_cterm s6)
        (idSubst_cterm sigma_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
  | evec s0 => congr_evec (idSubst_cterm sigma_cterm Eq_cterm s0)
  | evnil s0 => congr_evnil (idSubst_cterm sigma_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
  | pvnil s0 => congr_pvnil (idSubst_cterm sigma_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
        (idSubst_cterm sigma_cterm Eq_cterm s6)
        (idSubst_cterm sigma_cterm Eq_cterm s7)
        (idSubst_cterm sigma_cterm Eq_cterm s8)
        (idSubst_cterm sigma_cterm Eq_cterm s9)
        (idSubst_cterm sigma_cterm Eq_cterm s10)
        (idSubst_cterm sigma_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
        (idSubst_cterm sigma_cterm Eq_cterm s6)
        (idSubst_cterm sigma_cterm Eq_cterm s7)
        (idSubst_cterm sigma_cterm Eq_cterm s8)
        (idSubst_cterm sigma_cterm Eq_cterm s9)
        (idSubst_cterm sigma_cterm Eq_cterm s10)
        (idSubst_cterm sigma_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP (idSubst_cterm sigma_cterm Eq_cterm s0)
        (idSubst_cterm sigma_cterm Eq_cterm s1)
        (idSubst_cterm sigma_cterm Eq_cterm s2)
        (idSubst_cterm sigma_cterm Eq_cterm s3)
        (idSubst_cterm sigma_cterm Eq_cterm s4)
        (idSubst_cterm sigma_cterm Eq_cterm s5)
        (idSubst_cterm sigma_cterm Eq_cterm s6)
        (idSubst_cterm sigma_cterm Eq_cterm s7)
        (idSubst_cterm sigma_cterm Eq_cterm s8)
        (idSubst_cterm sigma_cterm Eq_cterm s9)
  end.

Lemma upExtRen_cterm_cterm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_cterm_cterm xi x = upRen_cterm_cterm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_cterm (xi_cterm : nat -> nat) (zeta_cterm : nat -> nat)
(Eq_cterm : forall x, xi_cterm x = zeta_cterm x) (s : cterm) {struct s} :
ren_cterm xi_cterm s = ren_cterm zeta_cterm s :=
  match s with
  | cvar s0 => ap (cvar) (Eq_cterm s0)
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0) (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm (upRen_cterm_cterm xi_cterm)
           (upRen_cterm_cterm zeta_cterm) (upExtRen_cterm_cterm _ _ Eq_cterm)
           s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0) (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm (upRen_cterm_cterm xi_cterm)
           (upRen_cterm_cterm zeta_cterm) (upExtRen_cterm_cterm _ _ Eq_cterm)
           s2)
  | capp s0 s1 =>
      congr_capp (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 => congr_cEl (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | cErr s0 => congr_cErr (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | squash s0 => congr_squash (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | sq s0 => congr_sq (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0) (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 => congr_psucc (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s6)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
  | evec s0 => congr_evec (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | evnil s0 => congr_evnil (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
  | pvnil s0 => congr_pvnil (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s6)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s7)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s8)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s9)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s10)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s6)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s7)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s8)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s9)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s10)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP (extRen_cterm xi_cterm zeta_cterm Eq_cterm s0)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s1)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s2)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s3)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s4)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s5)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s6)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s7)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s8)
        (extRen_cterm xi_cterm zeta_cterm Eq_cterm s9)
  end.

Lemma upExt_cterm_cterm (sigma : nat -> cterm) (tau : nat -> cterm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_cterm_cterm sigma x = up_cterm_cterm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_cterm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_cterm (sigma_cterm : nat -> cterm) (tau_cterm : nat -> cterm)
(Eq_cterm : forall x, sigma_cterm x = tau_cterm x) (s : cterm) {struct s} :
subst_cterm sigma_cterm s = subst_cterm tau_cterm s :=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0) (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm (up_cterm_cterm sigma_cterm) (up_cterm_cterm tau_cterm)
           (upExt_cterm_cterm _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0) (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm (up_cterm_cterm sigma_cterm) (up_cterm_cterm tau_cterm)
           (upExt_cterm_cterm _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0) (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 => congr_cEl (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | cErr s0 => congr_cErr (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | squash s0 => congr_squash (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | sq s0 => congr_sq (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0) (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 => congr_psucc (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s6)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
  | evec s0 => congr_evec (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | evnil s0 => congr_evnil (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
  | pvnil s0 => congr_pvnil (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s6)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s7)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s8)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s9)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s10)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s6)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s7)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s8)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s9)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s10)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP (ext_cterm sigma_cterm tau_cterm Eq_cterm s0)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s1)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s2)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s3)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s4)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s5)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s6)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s7)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s8)
        (ext_cterm sigma_cterm tau_cterm Eq_cterm s9)
  end.

Lemma up_ren_ren_cterm_cterm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_cterm_cterm zeta) (upRen_cterm_cterm xi) x =
  upRen_cterm_cterm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_cterm (xi_cterm : nat -> nat) (zeta_cterm : nat -> nat)
(rho_cterm : nat -> nat)
(Eq_cterm : forall x, funcomp zeta_cterm xi_cterm x = rho_cterm x)
(s : cterm) {struct s} :
ren_cterm zeta_cterm (ren_cterm xi_cterm s) = ren_cterm rho_cterm s :=
  match s with
  | cvar s0 => ap (cvar) (Eq_cterm s0)
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm (upRen_cterm_cterm xi_cterm)
           (upRen_cterm_cterm zeta_cterm) (upRen_cterm_cterm rho_cterm)
           (up_ren_ren _ _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm (upRen_cterm_cterm xi_cterm)
           (upRen_cterm_cterm zeta_cterm) (upRen_cterm_cterm rho_cterm)
           (up_ren_ren _ _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 =>
      congr_cEl (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | cErr s0 =>
      congr_cErr (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | squash s0 =>
      congr_squash
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | sq s0 =>
      congr_sq (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 =>
      congr_psucc
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s6)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
  | evec s0 =>
      congr_evec (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | evnil s0 =>
      congr_evnil
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
  | pvnil s0 =>
      congr_pvnil
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s6)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s7)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s8)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s9)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s10)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s6)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s7)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s8)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s9)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s10)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s0)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s1)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s2)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s3)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s4)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s5)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s6)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s7)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s8)
        (compRenRen_cterm xi_cterm zeta_cterm rho_cterm Eq_cterm s9)
  end.

Lemma up_ren_subst_cterm_cterm (xi : nat -> nat) (tau : nat -> cterm)
  (theta : nat -> cterm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_cterm_cterm tau) (upRen_cterm_cterm xi) x =
  up_cterm_cterm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_cterm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_cterm (xi_cterm : nat -> nat)
(tau_cterm : nat -> cterm) (theta_cterm : nat -> cterm)
(Eq_cterm : forall x, funcomp tau_cterm xi_cterm x = theta_cterm x)
(s : cterm) {struct s} :
subst_cterm tau_cterm (ren_cterm xi_cterm s) = subst_cterm theta_cterm s :=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm (upRen_cterm_cterm xi_cterm)
           (up_cterm_cterm tau_cterm) (up_cterm_cterm theta_cterm)
           (up_ren_subst_cterm_cterm _ _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm (upRen_cterm_cterm xi_cterm)
           (up_cterm_cterm tau_cterm) (up_cterm_cterm theta_cterm)
           (up_ren_subst_cterm_cterm _ _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 =>
      congr_cEl
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | cErr s0 =>
      congr_cErr
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | squash s0 =>
      congr_squash
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | sq s0 =>
      congr_sq
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 =>
      congr_psucc
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
  | evec s0 =>
      congr_evec
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | evnil s0 =>
      congr_evnil
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pvnil s0 =>
      congr_pvnil
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s9)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s10)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s9)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s10)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compRenSubst_cterm xi_cterm tau_cterm theta_cterm Eq_cterm s9)
  end.

Lemma up_subst_ren_cterm_cterm (sigma : nat -> cterm)
  (zeta_cterm : nat -> nat) (theta : nat -> cterm)
  (Eq : forall x, funcomp (ren_cterm zeta_cterm) sigma x = theta x) :
  forall x,
  funcomp (ren_cterm (upRen_cterm_cterm zeta_cterm)) (up_cterm_cterm sigma) x =
  up_cterm_cterm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_cterm shift (upRen_cterm_cterm zeta_cterm)
                (funcomp shift zeta_cterm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_cterm zeta_cterm shift
                      (funcomp shift zeta_cterm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_cterm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_cterm (sigma_cterm : nat -> cterm)
(zeta_cterm : nat -> nat) (theta_cterm : nat -> cterm)
(Eq_cterm : forall x,
            funcomp (ren_cterm zeta_cterm) sigma_cterm x = theta_cterm x)
(s : cterm) {struct s} :
ren_cterm zeta_cterm (subst_cterm sigma_cterm s) = subst_cterm theta_cterm s
:=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm (up_cterm_cterm sigma_cterm)
           (upRen_cterm_cterm zeta_cterm) (up_cterm_cterm theta_cterm)
           (up_subst_ren_cterm_cterm _ _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm (up_cterm_cterm sigma_cterm)
           (upRen_cterm_cterm zeta_cterm) (up_cterm_cterm theta_cterm)
           (up_subst_ren_cterm_cterm _ _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 =>
      congr_cEl
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | cErr s0 =>
      congr_cErr
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | squash s0 =>
      congr_squash
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | sq s0 =>
      congr_sq
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 =>
      congr_psucc
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s6)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
  | evec s0 =>
      congr_evec
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | evnil s0 =>
      congr_evnil
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
  | pvnil s0 =>
      congr_pvnil
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s6)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s7)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s8)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s9)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s10)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s6)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s7)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s8)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s9)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s10)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s0)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s1)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s2)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s3)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s4)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s5)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s6)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s7)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s8)
        (compSubstRen_cterm sigma_cterm zeta_cterm theta_cterm Eq_cterm s9)
  end.

Lemma up_subst_subst_cterm_cterm (sigma : nat -> cterm)
  (tau_cterm : nat -> cterm) (theta : nat -> cterm)
  (Eq : forall x, funcomp (subst_cterm tau_cterm) sigma x = theta x) :
  forall x,
  funcomp (subst_cterm (up_cterm_cterm tau_cterm)) (up_cterm_cterm sigma) x =
  up_cterm_cterm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_cterm shift (up_cterm_cterm tau_cterm)
                (funcomp (up_cterm_cterm tau_cterm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_cterm tau_cterm shift
                      (funcomp (ren_cterm shift) tau_cterm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_cterm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_cterm (sigma_cterm : nat -> cterm)
(tau_cterm : nat -> cterm) (theta_cterm : nat -> cterm)
(Eq_cterm : forall x,
            funcomp (subst_cterm tau_cterm) sigma_cterm x = theta_cterm x)
(s : cterm) {struct s} :
subst_cterm tau_cterm (subst_cterm sigma_cterm s) = subst_cterm theta_cterm s
:=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm (up_cterm_cterm sigma_cterm)
           (up_cterm_cterm tau_cterm) (up_cterm_cterm theta_cterm)
           (up_subst_subst_cterm_cterm _ _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm (up_cterm_cterm sigma_cterm)
           (up_cterm_cterm tau_cterm) (up_cterm_cterm theta_cterm)
           (up_subst_subst_cterm_cterm _ _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 =>
      congr_cEl
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | cErr s0 =>
      congr_cErr
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | squash s0 =>
      congr_squash
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | sq s0 =>
      congr_sq
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 =>
      congr_psucc
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
  | evec s0 =>
      congr_evec
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | evnil s0 =>
      congr_evnil
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
  | pvnil s0 =>
      congr_pvnil
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s9)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s10)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s9)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s10)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s0)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s1)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s2)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s3)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s4)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s5)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s6)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s7)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s8)
        (compSubstSubst_cterm sigma_cterm tau_cterm theta_cterm Eq_cterm s9)
  end.

Lemma renRen_cterm (xi_cterm : nat -> nat) (zeta_cterm : nat -> nat)
  (s : cterm) :
  ren_cterm zeta_cterm (ren_cterm xi_cterm s) =
  ren_cterm (funcomp zeta_cterm xi_cterm) s.
Proof.
exact (compRenRen_cterm xi_cterm zeta_cterm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_cterm_pointwise (xi_cterm : nat -> nat)
  (zeta_cterm : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_cterm zeta_cterm) (ren_cterm xi_cterm))
    (ren_cterm (funcomp zeta_cterm xi_cterm)).
Proof.
exact (fun s => compRenRen_cterm xi_cterm zeta_cterm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_cterm (xi_cterm : nat -> nat) (tau_cterm : nat -> cterm)
  (s : cterm) :
  subst_cterm tau_cterm (ren_cterm xi_cterm s) =
  subst_cterm (funcomp tau_cterm xi_cterm) s.
Proof.
exact (compRenSubst_cterm xi_cterm tau_cterm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_cterm_pointwise (xi_cterm : nat -> nat)
  (tau_cterm : nat -> cterm) :
  pointwise_relation _ eq
    (funcomp (subst_cterm tau_cterm) (ren_cterm xi_cterm))
    (subst_cterm (funcomp tau_cterm xi_cterm)).
Proof.
exact (fun s => compRenSubst_cterm xi_cterm tau_cterm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_cterm (sigma_cterm : nat -> cterm) (zeta_cterm : nat -> nat)
  (s : cterm) :
  ren_cterm zeta_cterm (subst_cterm sigma_cterm s) =
  subst_cterm (funcomp (ren_cterm zeta_cterm) sigma_cterm) s.
Proof.
exact (compSubstRen_cterm sigma_cterm zeta_cterm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_cterm_pointwise (sigma_cterm : nat -> cterm)
  (zeta_cterm : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_cterm zeta_cterm) (subst_cterm sigma_cterm))
    (subst_cterm (funcomp (ren_cterm zeta_cterm) sigma_cterm)).
Proof.
exact (fun s =>
       compSubstRen_cterm sigma_cterm zeta_cterm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_cterm (sigma_cterm : nat -> cterm)
  (tau_cterm : nat -> cterm) (s : cterm) :
  subst_cterm tau_cterm (subst_cterm sigma_cterm s) =
  subst_cterm (funcomp (subst_cterm tau_cterm) sigma_cterm) s.
Proof.
exact (compSubstSubst_cterm sigma_cterm tau_cterm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_cterm_pointwise (sigma_cterm : nat -> cterm)
  (tau_cterm : nat -> cterm) :
  pointwise_relation _ eq
    (funcomp (subst_cterm tau_cterm) (subst_cterm sigma_cterm))
    (subst_cterm (funcomp (subst_cterm tau_cterm) sigma_cterm)).
Proof.
exact (fun s =>
       compSubstSubst_cterm sigma_cterm tau_cterm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_cterm_cterm (xi : nat -> nat) (sigma : nat -> cterm)
  (Eq : forall x, funcomp (cvar) xi x = sigma x) :
  forall x, funcomp (cvar) (upRen_cterm_cterm xi) x = up_cterm_cterm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_cterm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_cterm (xi_cterm : nat -> nat)
(sigma_cterm : nat -> cterm)
(Eq_cterm : forall x, funcomp (cvar) xi_cterm x = sigma_cterm x) (s : cterm)
{struct s} : ren_cterm xi_cterm s = subst_cterm sigma_cterm s :=
  match s with
  | cvar s0 => Eq_cterm s0
  | cSort s0 s1 => congr_cSort (eq_refl s0) (eq_refl s1)
  | cPi s0 s1 s2 =>
      congr_cPi (eq_refl s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm (upRen_cterm_cterm xi_cterm)
           (up_cterm_cterm sigma_cterm)
           (rinstInst_up_cterm_cterm _ _ Eq_cterm) s2)
  | clam s0 s1 s2 =>
      congr_clam (eq_refl s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm (upRen_cterm_cterm xi_cterm)
           (up_cterm_cterm sigma_cterm)
           (rinstInst_up_cterm_cterm _ _ Eq_cterm) s2)
  | capp s0 s1 =>
      congr_capp (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
  | cunit => congr_cunit
  | ctt => congr_ctt
  | ctop => congr_ctop
  | cstar => congr_cstar
  | cbot => congr_cbot
  | cbot_elim s0 s1 s2 =>
      congr_cbot_elim (eq_refl s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | cty s0 => congr_cty (eq_refl s0)
  | ctyval s0 s1 s2 =>
      congr_ctyval (eq_refl s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | ctyerr => congr_ctyerr
  | cEl s0 => congr_cEl (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | cErr s0 => congr_cErr (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | squash s0 =>
      congr_squash (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | sq s0 => congr_sq (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | sq_elim s0 s1 s2 =>
      congr_sq_elim (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | teq s0 s1 s2 =>
      congr_teq (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | trefl s0 s1 =>
      congr_trefl (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
  | tJ s0 s1 s2 =>
      congr_tJ (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | ebool => congr_ebool
  | etrue => congr_etrue
  | efalse => congr_efalse
  | bool_err => congr_bool_err
  | eif s0 s1 s2 s3 s4 s5 =>
      congr_eif (eq_refl s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
  | pbool => congr_pbool
  | ptrue => congr_ptrue
  | pfalse => congr_pfalse
  | pif s0 s1 s2 s3 =>
      congr_pif (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | enat_elim s0 s1 s2 s3 =>
      congr_enat_elim (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
  | pnat => congr_pnat
  | pzero => congr_pzero
  | psucc s0 =>
      congr_psucc (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_pnat_elim (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s6)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s7)
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      congr_pnat_elimP (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
  | evec s0 => congr_evec (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | evnil s0 =>
      congr_evnil (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | evcons s0 s1 =>
      congr_evcons (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
  | evec_elim s0 s1 s2 s3 =>
      congr_evec_elim (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
  | pvec s0 s1 s2 s3 =>
      congr_pvec (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
  | pvnil s0 =>
      congr_pvnil (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
  | pvcons s0 s1 s2 =>
      congr_pvcons (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elim (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s6)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s7)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s8)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s9)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s10)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s11)
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      congr_pvec_elimG (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s6)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s7)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s8)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s9)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s10)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s11)
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      congr_pvec_elimP (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s0)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s1)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s2)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s3)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s4)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s5)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s6)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s7)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s8)
        (rinst_inst_cterm xi_cterm sigma_cterm Eq_cterm s9)
  end.

Lemma rinstInst'_cterm (xi_cterm : nat -> nat) (s : cterm) :
  ren_cterm xi_cterm s = subst_cterm (funcomp (cvar) xi_cterm) s.
Proof.
exact (rinst_inst_cterm xi_cterm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_cterm_pointwise (xi_cterm : nat -> nat) :
  pointwise_relation _ eq (ren_cterm xi_cterm)
    (subst_cterm (funcomp (cvar) xi_cterm)).
Proof.
exact (fun s => rinst_inst_cterm xi_cterm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_cterm (s : cterm) : subst_cterm (cvar) s = s.
Proof.
exact (idSubst_cterm (cvar) (fun n => eq_refl) s).
Qed.

Lemma instId'_cterm_pointwise :
  pointwise_relation _ eq (subst_cterm (cvar)) id.
Proof.
exact (fun s => idSubst_cterm (cvar) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_cterm (s : cterm) : ren_cterm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_cterm s) (rinstInst'_cterm id s)).
Qed.

Lemma rinstId'_cterm_pointwise : pointwise_relation _ eq (@ren_cterm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_cterm s) (rinstInst'_cterm id s)).
Qed.

Lemma varL'_cterm (sigma_cterm : nat -> cterm) (x : nat) :
  subst_cterm sigma_cterm (cvar x) = sigma_cterm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_cterm_pointwise (sigma_cterm : nat -> cterm) :
  pointwise_relation _ eq (funcomp (subst_cterm sigma_cterm) (cvar))
    sigma_cterm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_cterm (xi_cterm : nat -> nat) (x : nat) :
  ren_cterm xi_cterm (cvar x) = cvar (xi_cterm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_cterm_pointwise (xi_cterm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_cterm xi_cterm) (cvar))
    (funcomp (cvar) xi_cterm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_cterm X Y :=
    up_cterm : X -> Y.

#[global]Instance Subst_cterm : (Subst1 _ _ _) := @subst_cterm.

#[global]
Instance Up_cterm_cterm : (Up_cterm _ _) := @up_cterm_cterm.

#[global]Instance Ren_cterm : (Ren1 _ _ _) := @ren_cterm.

#[global]
Instance VarInstance_cterm : (Var _ _) := @cvar.

Notation "[ sigma_cterm ]" := (subst_cterm sigma_cterm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_cterm ]" := (subst_cterm sigma_cterm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__cterm" := up_cterm (only printing)  : subst_scope.

Notation "↑__cterm" := up_cterm_cterm (only printing)  : subst_scope.

Notation "⟨ xi_cterm ⟩" := (ren_cterm xi_cterm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_cterm ⟩" := (ren_cterm xi_cterm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := cvar ( at level 1, only printing)  : subst_scope.

Notation "x '__cterm'" := (@ids _ _ VarInstance_cterm x)
( at level 5, format "x __cterm", only printing)  : subst_scope.

Notation "x '__cterm'" := (cvar x) ( at level 5, format "x __cterm")  :
subst_scope.

#[global]
Instance subst_cterm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_cterm)).
Proof.
exact (fun f_cterm g_cterm Eq_cterm s t Eq_st =>
       eq_ind s (fun t' => subst_cterm f_cterm s = subst_cterm g_cterm t')
         (ext_cterm f_cterm g_cterm Eq_cterm s) t Eq_st).
Qed.

#[global]
Instance subst_cterm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_cterm)).
Proof.
exact (fun f_cterm g_cterm Eq_cterm s => ext_cterm f_cterm g_cterm Eq_cterm s).
Qed.

#[global]
Instance ren_cterm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_cterm)).
Proof.
exact (fun f_cterm g_cterm Eq_cterm s t Eq_st =>
       eq_ind s (fun t' => ren_cterm f_cterm s = ren_cterm g_cterm t')
         (extRen_cterm f_cterm g_cterm Eq_cterm s) t Eq_st).
Qed.

#[global]
Instance ren_cterm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_cterm)).
Proof.
exact (fun f_cterm g_cterm Eq_cterm s =>
       extRen_cterm f_cterm g_cterm Eq_cterm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_cterm, Var, ids, Ren_cterm, Ren1,
                      ren1, Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm,
                      Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_cterm, Var,
                                            ids, Ren_cterm, Ren1, ren1,
                                            Up_cterm_cterm, Up_cterm,
                                            up_cterm, Subst_cterm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_cterm_pointwise
                 | progress setoid_rewrite substSubst_cterm
                 | progress setoid_rewrite substRen_cterm_pointwise
                 | progress setoid_rewrite substRen_cterm
                 | progress setoid_rewrite renSubst_cterm_pointwise
                 | progress setoid_rewrite renSubst_cterm
                 | progress setoid_rewrite renRen'_cterm_pointwise
                 | progress setoid_rewrite renRen_cterm
                 | progress setoid_rewrite varLRen'_cterm_pointwise
                 | progress setoid_rewrite varLRen'_cterm
                 | progress setoid_rewrite varL'_cterm_pointwise
                 | progress setoid_rewrite varL'_cterm
                 | progress setoid_rewrite rinstId'_cterm_pointwise
                 | progress setoid_rewrite rinstId'_cterm
                 | progress setoid_rewrite instId'_cterm_pointwise
                 | progress setoid_rewrite instId'_cterm
                 | progress unfold up_cterm_cterm, upRen_cterm_cterm, up_ren
                 | progress cbn[subst_cterm ren_cterm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_cterm, Var, ids, Ren_cterm, Ren1, ren1,
                  Up_cterm_cterm, Up_cterm, up_cterm, Subst_cterm, Subst1,
                  subst1 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_cterm_pointwise;
                  try setoid_rewrite rinstInst'_cterm.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_cterm_pointwise;
                  try setoid_rewrite_left rinstInst'_cterm.

End Core.

Module Allfv.

Import
Core.

Lemma upAllfv_cterm_cterm (p : nat -> Prop) : nat -> Prop.
Proof.
exact (up_allfv p).
Defined.

Fixpoint allfv_cterm (p_cterm : nat -> Prop) (s : cterm) {struct s} : Prop :=
  match s with
  | cvar s0 => p_cterm s0
  | cSort s0 s1 => and True (and True True)
  | cPi s0 s1 s2 =>
      and True
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm (upAllfv_cterm_cterm p_cterm) s2) True))
  | clam s0 s1 s2 =>
      and True
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm (upAllfv_cterm_cterm p_cterm) s2) True))
  | capp s0 s1 =>
      and (allfv_cterm p_cterm s0) (and (allfv_cterm p_cterm s1) True)
  | cunit => True
  | ctt => True
  | ctop => True
  | cstar => True
  | cbot => True
  | cbot_elim s0 s1 s2 =>
      and True
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | cty s0 => and True True
  | ctyval s0 s1 s2 =>
      and True
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | ctyerr => True
  | cEl s0 => and (allfv_cterm p_cterm s0) True
  | cErr s0 => and (allfv_cterm p_cterm s0) True
  | squash s0 => and (allfv_cterm p_cterm s0) True
  | sq s0 => and (allfv_cterm p_cterm s0) True
  | sq_elim s0 s1 s2 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | teq s0 s1 s2 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | trefl s0 s1 =>
      and (allfv_cterm p_cterm s0) (and (allfv_cterm p_cterm s1) True)
  | tJ s0 s1 s2 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | ebool => True
  | etrue => True
  | efalse => True
  | bool_err => True
  | eif s0 s1 s2 s3 s4 s5 =>
      and True
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5) True)))))
  | pbool => True
  | ptrue => True
  | pfalse => True
  | pif s0 s1 s2 s3 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2) (and (allfv_cterm p_cterm s3) True)))
  | enat => True
  | ezero => True
  | esucc s0 => and (allfv_cterm p_cterm s0) True
  | enat_elim s0 s1 s2 s3 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2) (and (allfv_cterm p_cterm s3) True)))
  | pnat => True
  | pzero => True
  | psucc s0 => and (allfv_cterm p_cterm s0) True
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5)
                       (and (allfv_cterm p_cterm s6)
                          (and (allfv_cterm p_cterm s7) True)))))))
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5) True)))))
  | evec s0 => and (allfv_cterm p_cterm s0) True
  | evnil s0 => and (allfv_cterm p_cterm s0) True
  | evcons s0 s1 =>
      and (allfv_cterm p_cterm s0) (and (allfv_cterm p_cterm s1) True)
  | evec_elim s0 s1 s2 s3 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2) (and (allfv_cterm p_cterm s3) True)))
  | pvec s0 s1 s2 s3 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2) (and (allfv_cterm p_cterm s3) True)))
  | pvnil s0 => and (allfv_cterm p_cterm s0) True
  | pvcons s0 s1 s2 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1) (and (allfv_cterm p_cterm s2) True))
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5)
                       (and (allfv_cterm p_cterm s6)
                          (and (allfv_cterm p_cterm s7)
                             (and (allfv_cterm p_cterm s8)
                                (and (allfv_cterm p_cterm s9)
                                   (and (allfv_cterm p_cterm s10)
                                      (and (allfv_cterm p_cterm s11) True)))))))))))
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5)
                       (and (allfv_cterm p_cterm s6)
                          (and (allfv_cterm p_cterm s7)
                             (and (allfv_cterm p_cterm s8)
                                (and (allfv_cterm p_cterm s9)
                                   (and (allfv_cterm p_cterm s10)
                                      (and (allfv_cterm p_cterm s11) True)))))))))))
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      and (allfv_cterm p_cterm s0)
        (and (allfv_cterm p_cterm s1)
           (and (allfv_cterm p_cterm s2)
              (and (allfv_cterm p_cterm s3)
                 (and (allfv_cterm p_cterm s4)
                    (and (allfv_cterm p_cterm s5)
                       (and (allfv_cterm p_cterm s6)
                          (and (allfv_cterm p_cterm s7)
                             (and (allfv_cterm p_cterm s8)
                                (and (allfv_cterm p_cterm s9) True)))))))))
  end.

Lemma upAllfvTriv_cterm_cterm {p : nat -> Prop} (H : forall x, p x) :
  forall x, upAllfv_cterm_cterm p x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => I
                end).
Qed.

Fixpoint allfvTriv_cterm (p_cterm : nat -> Prop)
(H_cterm : forall x, p_cterm x) (s : cterm) {struct s} :
allfv_cterm p_cterm s :=
  match s with
  | cvar s0 => H_cterm s0
  | cSort s0 s1 => conj I (conj I I)
  | cPi s0 s1 s2 =>
      conj I
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj
              (allfvTriv_cterm (upAllfv_cterm_cterm p_cterm)
                 (upAllfvTriv_cterm_cterm H_cterm) s2) I))
  | clam s0 s1 s2 =>
      conj I
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj
              (allfvTriv_cterm (upAllfv_cterm_cterm p_cterm)
                 (upAllfvTriv_cterm_cterm H_cterm) s2) I))
  | capp s0 s1 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1) I)
  | cunit => I
  | ctt => I
  | ctop => I
  | cstar => I
  | cbot => I
  | cbot_elim s0 s1 s2 =>
      conj I
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | cty s0 => conj I I
  | ctyval s0 s1 s2 =>
      conj I
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | ctyerr => I
  | cEl s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | cErr s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | squash s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | sq s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | sq_elim s0 s1 s2 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | teq s0 s1 s2 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | trefl s0 s1 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1) I)
  | tJ s0 s1 s2 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | ebool => I
  | etrue => I
  | efalse => I
  | bool_err => I
  | eif s0 s1 s2 s3 s4 s5 =>
      conj I
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5) I)))))
  | pbool => I
  | ptrue => I
  | pfalse => I
  | pif s0 s1 s2 s3 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3) I)))
  | enat => I
  | ezero => I
  | esucc s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | enat_elim s0 s1 s2 s3 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3) I)))
  | pnat => I
  | pzero => I
  | psucc s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5)
                       (conj (allfvTriv_cterm p_cterm H_cterm s6)
                          (conj (allfvTriv_cterm p_cterm H_cterm s7) I)))))))
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5) I)))))
  | evec s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | evnil s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | evcons s0 s1 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1) I)
  | evec_elim s0 s1 s2 s3 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3) I)))
  | pvec s0 s1 s2 s3 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3) I)))
  | pvnil s0 => conj (allfvTriv_cterm p_cterm H_cterm s0) I
  | pvcons s0 s1 s2 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2) I))
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5)
                       (conj (allfvTriv_cterm p_cterm H_cterm s6)
                          (conj (allfvTriv_cterm p_cterm H_cterm s7)
                             (conj (allfvTriv_cterm p_cterm H_cterm s8)
                                (conj (allfvTriv_cterm p_cterm H_cterm s9)
                                   (conj
                                      (allfvTriv_cterm p_cterm H_cterm s10)
                                      (conj
                                         (allfvTriv_cterm p_cterm H_cterm s11)
                                         I)))))))))))
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5)
                       (conj (allfvTriv_cterm p_cterm H_cterm s6)
                          (conj (allfvTriv_cterm p_cterm H_cterm s7)
                             (conj (allfvTriv_cterm p_cterm H_cterm s8)
                                (conj (allfvTriv_cterm p_cterm H_cterm s9)
                                   (conj
                                      (allfvTriv_cterm p_cterm H_cterm s10)
                                      (conj
                                         (allfvTriv_cterm p_cterm H_cterm s11)
                                         I)))))))))))
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      conj (allfvTriv_cterm p_cterm H_cterm s0)
        (conj (allfvTriv_cterm p_cterm H_cterm s1)
           (conj (allfvTriv_cterm p_cterm H_cterm s2)
              (conj (allfvTriv_cterm p_cterm H_cterm s3)
                 (conj (allfvTriv_cterm p_cterm H_cterm s4)
                    (conj (allfvTriv_cterm p_cterm H_cterm s5)
                       (conj (allfvTriv_cterm p_cterm H_cterm s6)
                          (conj (allfvTriv_cterm p_cterm H_cterm s7)
                             (conj (allfvTriv_cterm p_cterm H_cterm s8)
                                (conj (allfvTriv_cterm p_cterm H_cterm s9) I)))))))))
  end.

Lemma upAllfvImpl_cterm_cterm {p : nat -> Prop} {q : nat -> Prop}
  (H : forall x, p x -> q x) :
  forall x, upAllfv_cterm_cterm p x -> upAllfv_cterm_cterm q x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => fun Hp => Hp
                end).
Qed.

Fixpoint allfvImpl_cterm (p_cterm : nat -> Prop) (q_cterm : nat -> Prop)
(H_cterm : forall x, p_cterm x -> q_cterm x) (s : cterm) {struct s} :
allfv_cterm p_cterm s -> allfv_cterm q_cterm s :=
  match s with
  | cvar s0 => fun HP => H_cterm s0 HP
  | cSort s0 s1 => fun HP => conj I (conj I I)
  | cPi s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm (upAllfv_cterm_cterm p_cterm)
                 (upAllfv_cterm_cterm q_cterm)
                 (upAllfvImpl_cterm_cterm H_cterm) s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | clam s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm (upAllfv_cterm_cterm p_cterm)
                 (upAllfv_cterm_cterm q_cterm)
                 (upAllfvImpl_cterm_cterm H_cterm) s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | capp s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | cunit => fun HP => I
  | ctt => fun HP => I
  | ctop => fun HP => I
  | cstar => fun HP => I
  | cbot => fun HP => I
  | cbot_elim s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | cty s0 => fun HP => conj I I
  | ctyval s0 s1 s2 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | ctyerr => fun HP => I
  | cEl s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | cErr s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | squash s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | sq s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | sq_elim s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | teq s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | trefl s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tJ s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | ebool => fun HP => I
  | etrue => fun HP => I
  | efalse => fun HP => I
  | bool_err => fun HP => I
  | eif s0 s1 s2 s3 s4 s5 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
  | pbool => fun HP => I
  | ptrue => fun HP => I
  | pfalse => fun HP => I
  | pif s0 s1 s2 s3 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    end) I)))
  | enat => fun HP => I
  | ezero => fun HP => I
  | esucc s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | enat_elim s0 s1 s2 s3 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    end) I)))
  | pnat => fun HP => I
  | pzero => fun HP => I
  | psucc s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
                          (allfvImpl_cterm p_cterm q_cterm H_cterm s6
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
                             end)
                          (conj
                             (allfvImpl_cterm p_cterm q_cterm H_cterm s7
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
                                                        | conj _ HP =>
                                                            match HP with
                                                            | conj HP _ => HP
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end) I)))))))
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
  | evec s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | evnil s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | evcons s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | evec_elim s0 s1 s2 s3 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    end) I)))
  | pvec s0 s1 s2 s3 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    end) I)))
  | pvnil s0 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end) I
  | pvcons s0 s1 s2 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end) I))
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
                          (allfvImpl_cterm p_cterm q_cterm H_cterm s6
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
                             end)
                          (conj
                             (allfvImpl_cterm p_cterm q_cterm H_cterm s7
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
                                                        | conj _ HP =>
                                                            match HP with
                                                            | conj HP _ => HP
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvImpl_cterm p_cterm q_cterm H_cterm s8
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
                                                           | conj _ HP =>
                                                               match HP with
                                                               | conj _ HP =>
                                                                   match
                                                                    HP
                                                                   with
                                                                   | conj HP
                                                                    _ => HP
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvImpl_cterm p_cterm q_cterm H_cterm
                                      s9
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
                                                              | conj _ HP =>
                                                                  match
                                                                    HP
                                                                  with
                                                                  | conj _ HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvImpl_cterm p_cterm q_cterm
                                         H_cterm s10
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
                                                                 match
                                                                   HP
                                                                 with
                                                                 | conj _ HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvImpl_cterm p_cterm q_cterm
                                            H_cterm s11
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
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
                          (allfvImpl_cterm p_cterm q_cterm H_cterm s6
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
                             end)
                          (conj
                             (allfvImpl_cterm p_cterm q_cterm H_cterm s7
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
                                                        | conj _ HP =>
                                                            match HP with
                                                            | conj HP _ => HP
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvImpl_cterm p_cterm q_cterm H_cterm s8
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
                                                           | conj _ HP =>
                                                               match HP with
                                                               | conj _ HP =>
                                                                   match
                                                                    HP
                                                                   with
                                                                   | conj HP
                                                                    _ => HP
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvImpl_cterm p_cterm q_cterm H_cterm
                                      s9
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
                                                              | conj _ HP =>
                                                                  match
                                                                    HP
                                                                  with
                                                                  | conj _ HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvImpl_cterm p_cterm q_cterm
                                         H_cterm s10
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
                                                                 match
                                                                   HP
                                                                 with
                                                                 | conj _ HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvImpl_cterm p_cterm q_cterm
                                            H_cterm s11
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
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      fun HP =>
      conj
        (allfvImpl_cterm p_cterm q_cterm H_cterm s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_cterm p_cterm q_cterm H_cterm s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_cterm p_cterm q_cterm H_cterm s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_cterm p_cterm q_cterm H_cterm s3
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
                    (allfvImpl_cterm p_cterm q_cterm H_cterm s4
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
                       (allfvImpl_cterm p_cterm q_cterm H_cterm s5
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
                          (allfvImpl_cterm p_cterm q_cterm H_cterm s6
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
                             end)
                          (conj
                             (allfvImpl_cterm p_cterm q_cterm H_cterm s7
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
                                                        | conj _ HP =>
                                                            match HP with
                                                            | conj HP _ => HP
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvImpl_cterm p_cterm q_cterm H_cterm s8
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
                                                           | conj _ HP =>
                                                               match HP with
                                                               | conj _ HP =>
                                                                   match
                                                                    HP
                                                                   with
                                                                   | conj HP
                                                                    _ => HP
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvImpl_cterm p_cterm q_cterm H_cterm
                                      s9
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
                                                              | conj _ HP =>
                                                                  match
                                                                    HP
                                                                  with
                                                                  | conj _ HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj _
                                                                    HP =>
                                                                    match
                                                                    HP
                                                                    with
                                                                    | conj HP
                                                                    _ => HP
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end) I)))))))))
  end.

Lemma upAllfvRenL_cterm_cterm (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_cterm_cterm p (upRen_cterm_cterm xi x) ->
  upAllfv_cterm_cterm (funcomp p xi) x.
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenL_cterm (p_cterm : nat -> Prop) (xi_cterm : nat -> nat)
(s : cterm) {struct s} :
allfv_cterm p_cterm (ren_cterm xi_cterm s) ->
allfv_cterm (funcomp p_cterm xi_cterm) s :=
  match s with
  | cvar s0 => fun H => H
  | cSort s0 s1 => fun H => conj I (conj I I)
  | cPi s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvImpl_cterm _ _ (upAllfvRenL_cterm_cterm p_cterm xi_cterm)
                 s2
                 (allfvRenL_cterm (upAllfv_cterm_cterm p_cterm)
                    (upRen_cterm_cterm xi_cterm) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | clam s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvImpl_cterm _ _ (upAllfvRenL_cterm_cterm p_cterm xi_cterm)
                 s2
                 (allfvRenL_cterm (upAllfv_cterm_cterm p_cterm)
                    (upRen_cterm_cterm xi_cterm) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | capp s0 s1 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | cunit => fun H => I
  | ctt => fun H => I
  | ctop => fun H => I
  | cstar => fun H => I
  | cbot => fun H => I
  | cbot_elim s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | cty s0 => fun H => conj I I
  | ctyval s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ctyerr => fun H => I
  | cEl s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | cErr s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | squash s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | sq s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | sq_elim s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | teq s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | trefl s0 s1 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tJ s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ebool => fun H => I
  | etrue => fun H => I
  | efalse => fun H => I
  | bool_err => fun H => I
  | eif s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
  | pbool => fun H => I
  | ptrue => fun H => I
  | pfalse => fun H => I
  | pif s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | enat => fun H => I
  | ezero => fun H => I
  | esucc s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | enat_elim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pnat => fun H => I
  | pzero => fun H => I
  | psucc s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
                          (allfvRenL_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenL_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end) I)))))))
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
  | evec s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | evnil s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | evcons s0 s1 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | evec_elim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pvec s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pvnil s0 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | pvcons s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
                          (allfvRenL_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenL_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenL_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenL_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvRenL_cterm p_cterm xi_cterm s10
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
                                                                 | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvRenL_cterm p_cterm xi_cterm
                                            s11
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
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
                          (allfvRenL_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenL_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenL_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenL_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvRenL_cterm p_cterm xi_cterm s10
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
                                                                 | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvRenL_cterm p_cterm xi_cterm
                                            s11
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
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      fun H =>
      conj
        (allfvRenL_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenL_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_cterm p_cterm xi_cterm s3
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
                    (allfvRenL_cterm p_cterm xi_cterm s4
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
                       (allfvRenL_cterm p_cterm xi_cterm s5
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
                          (allfvRenL_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenL_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenL_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenL_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end) I)))))))))
  end.

Lemma upAllfvRenR_cterm_cterm (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_cterm_cterm (funcomp p xi) x ->
  upAllfv_cterm_cterm p (upRen_cterm_cterm xi x).
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenR_cterm (p_cterm : nat -> Prop) (xi_cterm : nat -> nat)
(s : cterm) {struct s} :
allfv_cterm (funcomp p_cterm xi_cterm) s ->
allfv_cterm p_cterm (ren_cterm xi_cterm s) :=
  match s with
  | cvar s0 => fun H => H
  | cSort s0 s1 => fun H => conj I (conj I I)
  | cPi s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm (upAllfv_cterm_cterm p_cterm)
                 (upRen_cterm_cterm xi_cterm) s2
                 (allfvImpl_cterm _ _
                    (upAllfvRenR_cterm_cterm p_cterm xi_cterm) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | clam s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm (upAllfv_cterm_cterm p_cterm)
                 (upRen_cterm_cterm xi_cterm) s2
                 (allfvImpl_cterm _ _
                    (upAllfvRenR_cterm_cterm p_cterm xi_cterm) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end)) I))
  | capp s0 s1 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | cunit => fun H => I
  | ctt => fun H => I
  | ctop => fun H => I
  | cstar => fun H => I
  | cbot => fun H => I
  | cbot_elim s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | cty s0 => fun H => conj I I
  | ctyval s0 s1 s2 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ctyerr => fun H => I
  | cEl s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | cErr s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | squash s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | sq s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | sq_elim s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | teq s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | trefl s0 s1 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tJ s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | ebool => fun H => I
  | etrue => fun H => I
  | efalse => fun H => I
  | bool_err => fun H => I
  | eif s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
  | pbool => fun H => I
  | ptrue => fun H => I
  | pfalse => fun H => I
  | pif s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | enat => fun H => I
  | ezero => fun H => I
  | esucc s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | enat_elim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pnat => fun H => I
  | pzero => fun H => I
  | psucc s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | pnat_elim s0 s1 s2 s3 s4 s5 s6 s7 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
                          (allfvRenR_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenR_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end) I)))))))
  | pnat_elimP s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
  | evec s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | evnil s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | evcons s0 s1 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | evec_elim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pvec s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    end) I)))
  | pvnil s0 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end) I
  | pvcons s0 s1 s2 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end) I))
  | pvec_elim s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
                          (allfvRenR_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenR_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenR_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenR_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvRenR_cterm p_cterm xi_cterm s10
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
                                                                 | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvRenR_cterm p_cterm xi_cterm
                                            s11
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
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
                          (allfvRenR_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenR_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenR_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenR_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end)
                                   (conj
                                      (allfvRenR_cterm p_cterm xi_cterm s10
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
                                                                 | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                 end
                                                             end
                                                         end
                                                     end
                                                 end
                                             end
                                         end)
                                      (conj
                                         (allfvRenR_cterm p_cterm xi_cterm
                                            s11
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
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end) I)))))))))))
  | pvec_elimP s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =>
      fun H =>
      conj
        (allfvRenR_cterm p_cterm xi_cterm s0 match H with
                                             | conj H _ => H
                                             end)
        (conj
           (allfvRenR_cterm p_cterm xi_cterm s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_cterm p_cterm xi_cterm s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_cterm p_cterm xi_cterm s3
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
                    (allfvRenR_cterm p_cterm xi_cterm s4
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
                       (allfvRenR_cterm p_cterm xi_cterm s5
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
                          (allfvRenR_cterm p_cterm xi_cterm s6
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
                             end)
                          (conj
                             (allfvRenR_cterm p_cterm xi_cterm s7
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
                                                        | conj _ H =>
                                                            match H with
                                                            | conj H _ => H
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end)
                             (conj
                                (allfvRenR_cterm p_cterm xi_cterm s8
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
                                                           | conj _ H =>
                                                               match H with
                                                               | conj _ H =>
                                                                   match
                                                                    H
                                                                   with
                                                                   | conj H _ =>
                                                                    H
                                                                   end
                                                               end
                                                           end
                                                       end
                                                   end
                                               end
                                           end
                                       end
                                   end)
                                (conj
                                   (allfvRenR_cterm p_cterm xi_cterm s9
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
                                                              | conj _ H =>
                                                                  match
                                                                    H
                                                                  with
                                                                  | conj _ H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj _
                                                                    H =>
                                                                    match
                                                                    H
                                                                    with
                                                                    | conj H
                                                                    _ => H
                                                                    end
                                                                    end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end) I)))))))))
  end.

End Allfv.

Module Extra.

Import Core.

#[global]Hint Opaque subst_cterm: rewrite.

#[global]Hint Opaque ren_cterm: rewrite.

End Extra.

Module interface.

Export Core.

Export Allfv.

Export Extra.

End interface.

Export interface.


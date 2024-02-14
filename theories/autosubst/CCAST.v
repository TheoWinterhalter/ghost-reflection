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
  | tJ : cterm -> cterm -> cterm -> cterm.

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
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_cterm ]" := (subst_cterm sigma_cterm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__cterm" := up_cterm (only printing) : subst_scope.

Notation "↑__cterm" := up_cterm_cterm (only printing) : subst_scope.

Notation "⟨ xi_cterm ⟩" := (ren_cterm xi_cterm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_cterm ⟩" := (ren_cterm xi_cterm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := cvar ( at level 1, only printing) : subst_scope.

Notation "x '__cterm'" := (@ids _ _ VarInstance_cterm x)
  ( at level 5, format "x __cterm", only printing) : subst_scope.

Notation "x '__cterm'" := (cvar x) ( at level 5, format "x __cterm") :
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


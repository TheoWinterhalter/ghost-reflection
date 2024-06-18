From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.multisteps Require Import Properties.
From GhostTT.reduction.multisteps Require Export Reduction.

Import ListNotations.
Set Default Goal Selector "!".

(* Definition *)
Inductive reduction_trans (Γ : scope) (u v: term) : Prop :=
  | Refl: u = v → reduction_trans Γ u v
  | Trans w : Γ ⊨ u ↣ w → reduction_trans Γ w v → reduction_trans Γ u v.

Notation "Γ ⊨ u ↣* v" := (reduction_trans Γ u v).

(* Usefull properties *)
Lemma red_trans_direct {Γ : scope } {u v: term} : Γ ⊨ u ↣ v → Γ ⊨ u ↣* v.
Proof.
  refine ( λ H, Trans Γ u v v H (Refl Γ v v _)).
  reflexivity.
Qed.

Lemma red_trans_trans {Γ : scope} {u v: term} :
  ∀ w, Γ ⊨ u ↣* w → Γ ⊨ w ↣* v → Γ ⊨ u ↣* v.
Proof.
  intros w red_u red_w.
  induction red_u as [ u | u w w' red_u red_w' IHw].
  - subst u; exact red_w.
  - eapply Trans; eauto.
Qed.

Corollary reds_scope (Γ : scope) (m: mode) (t t': term) :
  Γ ⊨ t ↣* t' → Γ⊢t∷m → Γ⊢t'∷m.
Proof.
  intros reds_t scope_t.
  induction reds_t.
  - subst; assumption.
  - eauto using red_scope.
Qed.


(* reds deinitions *)

Local Ltac end_things H:= 
  induction H in H |- *;
      [subst; apply Refl; reflexivity |
          eapply Trans; [ gred | eassumption]].

Lemma reds_beta (Γ : scope) (mx : mode) (A t t' u u' : term) :
  mx :: Γ⊨t↣*t'→ md Γ u = mx → Γ⊨u↣*u' → Γ⊨app (lam mx A t) u↣*t' <[u'··].
Proof.
  intros red_t scope_u red_u.
  induction red_u.
  - subst. induction red_t.
    * subst. apply red_trans_direct. gred; reflexivity.
    * eapply Trans; [ | eauto]. gred.
  - eapply Trans; [ | erewrite red_md in scope_u; eauto]. gred.

Qed.

Lemma reds_reveal_hide (Γ : scope) (mp : mode) (t P p t' p' : term): 
  Γ⊨t↣*t' → Γ⊨p↣*p' → In (md Γ p) [ℙ;𝔾] →
  Γ⊨reveal (hide t) P p↣*app p' t'.
Proof.
  intros red_t red_p Hscope.
  induction red_t.
  - subst. induction red_p.
    * subst. apply red_trans_direct. gred.
    * eapply Trans.
      + apply red_reveal; gred.
      + erewrite red_md in Hscope; eauto.
  - eapply Trans; [ | eauto]. gred.
Qed.

(* Lemma reds_if_true *)
(* Lemma reds_if_false *)
(* Lemma reds_nat_elim_zero *)
(* Lemma reds_nat_elim_succ *)
(* Lemma reds_vec_elim_nil *)
(* Lemma reds_vec_elim_cons *)

Lemma reds_Prop (Γ : scope) (i : level): Γ⊨Sort ℙ i↣*Sort ℙ 0.
Proof.
  apply red_trans_direct. gred.
Qed.

Lemma reds_Pi (Γ : scope) (i j : level) (m mx : mode) (A A' B B' : term) :
  Γ⊨A↣*A' → mx :: Γ⊨B↣*B' → Γ⊨Pi i j m mx A B↣*Pi (red_lvl mx i) (red_lvl m j) m mx A' B'.
Proof.
  intros red_A red_B.
  induction red_A.
  - subst. induction red_B.
    * subst. apply red_trans_direct. gred.
    * eapply Trans; [gred | eassumption].
  - eapply Trans; [gred | eassumption].
Qed.

Lemma reds_lam (Γ : scope) (mx : mode) (A A' t t' : term) :
  Γ⊨A↣*A' → mx :: Γ⊨t↣*t' → Γ⊨lam mx A t↣*lam mx A' t'.
Proof.
  intros red_A red_t.
  induction red_A.
  - subst. end_things red_t.
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_app (Γ : scope) (u u' v v' : term) :
  Γ⊨u↣*u' → Γ⊨v↣*v' → Γ⊨app u v↣*app u' v'.
Proof.
  intros red_u red_v.
  induction red_u.
  - subst. end_things red_v.
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_Erased (Γ : scope) (A A' : term) :
  Γ⊨A↣*A' → Γ⊨Erased A↣*Erased A'.
Proof.
  intro red_A; end_things red_A.
Qed.

Lemma reds_hide (Γ : scope) (A A' : term) :
  Γ⊨A↣*A' → Γ⊨hide A↣*hide A'.
Proof.
  intro red_A; end_things red_A.
Qed.

Lemma reds_reveal (Γ : scope) (t t' P P' p p' : term) :
  Γ⊨t↣*t' → Γ⊨P↣*P' → Γ⊨p↣*p' → Γ⊨reveal t P p↣*reveal t' P' p'.
Proof.
  intros red_t red_P red_p.
  induction red_t.
  - subst. induction red_P.
    * subst. end_things red_p.
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_Reveal (Γ : scope) (t t' p p' : term) :
  Γ⊨t↣*t' → Γ⊨p↣*p' → Γ⊨Reveal t p↣*Reveal t' p'.
Proof.
  intros red_t red_p.
  induction red_t.
  - subst. end_things red_p.
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_gheq (Γ : scope) (A A' u u' v v' : term):
  Γ⊨A↣*A' → Γ⊨u↣*u' → Γ⊨v↣*v' → Γ⊨gheq A u v↣*gheq A' u' v'.
Proof.
  intros red_A red_u red_v.
  induction red_A.
  - subst. induction red_u.
    * subst. end_things red_v.
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_if (Γ : scope) (m : mode) (b b' P P' t t' f f' : term) : 
  Γ⊨b↣*b' → Γ⊨P↣*P' → Γ⊨t↣*t' → Γ⊨f↣*f' → Γ⊨tif m b P t f↣*tif m b' P' t' f'.
Proof.
  intros red_b red_P red_t red_f.
  induction red_b.
  - subst. induction red_P.
    * subst. induction red_t.
      + subst. end_things red_f.
      + eapply Trans; [ gred | eassumption].
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.


Lemma reds_succ (Γ : scope) (n n' : term):
  Γ⊨n↣*n' → Γ⊨tsucc n↣*tsucc n'.
Proof.
  intro red_A; end_things red_A.
Qed.

Lemma reds_nat_elim (Γ : scope) (m : mode) (n n' P P' z z' s s' : term) :
  Γ⊨n↣*n' → Γ⊨P↣*P' → Γ⊨z↣*z' → Γ⊨s↣*s' → Γ⊨tnat_elim m n P z s↣*tnat_elim m n' P' z' s'.
Proof.
  intros red_n red_P red_z red_s.
  induction red_n.
  - subst. induction red_P.
    * subst. induction red_z.
      + subst. end_things red_s.
      + eapply Trans; [ gred | eassumption].
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_vec (Γ : scope) (A A' n n' : term) :
  Γ⊨A↣*A' → Γ⊨n↣*n' → Γ⊨tvec A n↣*tvec A' n'.
Proof.
  intros red_A red_n.
  induction red_A.
  - subst. end_things red_n.
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_vnil (Γ : scope) (A A' : term) :
  Γ⊨A↣*A' → Γ⊨tvnil A↣*tvnil A'.
Proof.
  intro red_A; end_things red_A.
Qed.

Lemma reds_vcons (Γ : scope) (a a' n n' v v' : term) :
  Γ⊨a↣*a' → Γ⊨n↣*n' → Γ⊨v↣*v' → Γ⊨tvcons a n v↣*tvcons a' n' v'.
Proof.
  intros red_a red_n red_v.
  induction red_a.
  - subst. induction red_n.
    * subst. end_things red_v.
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_vec_elim (Γ : scope) (m : mode) (A A' n n' v v' P P' z z' s s' : term):
  Γ⊨A↣*A' → Γ⊨n↣*n' → Γ⊨v↣*v' → Γ⊨P↣*P' → Γ⊨z↣*z' → Γ⊨s↣*s' 
  → Γ⊨tvec_elim m A n v P z s↣*tvec_elim m A' n' v' P' z' s'.
Proof.
  intros red_A red_n red_v red_P red_z red_s.
  induction red_A.
  - subst. induction red_n.
    * subst. induction red_v.
      + subst. induction red_P.
        ++ subst. induction red_z.
           +++ subst. end_things red_s.
           +++ eapply Trans; [ gred | eassumption].
        ++ eapply Trans; [ gred | eassumption].
      + eapply Trans; [ gred | eassumption].
    * eapply Trans; [ gred | eassumption].
  - eapply Trans; [ gred | eassumption].
Qed.

Lemma reds_bot_elim (Γ : scope) (m : mode) (A A' p p' : term) :
  Γ⊨A↣*A' → Γ⊨p↣*p' → Γ⊨bot_elim m A p↣*bot_elim m A' p'.
Proof.
  intros red_A red_p.
  induction red_A.
  - subst. end_things red_p.
  - eapply Trans; [ gred | eassumption].
Qed.


(* ------------------------------------------------------------------------- *)
(** rewriting automation **)
Create HintDb gtt_reds discriminated.

Hint Resolve reds_beta reds_reveal_hide (*reds_if_true reds_if_false reds_nat_elim_zero*)
  (* reds_nat_elim_succ reds_vec_elim_nil reds_vec_elim_cons*) reds_Prop reds_Pi
  reds_lam reds_app reds_Erased reds_hide reds_reveal reds_Reveal reds_gheq
  reds_if reds_succ reds_nat_elim reds_vec reds_vnil reds_vcons reds_vec_elim
  reds_bot_elim (*reds_irr*)
  : gtt_reds.

Ltac greds :=
  unshelve typeclasses eauto with gtt_scope gtt_reds gtt_red shelvedb ; shelve_unifiable.
(** end rewriting automation **)


(* reds inversions *)

Lemma reds_lam_inv {Γ : scope} {m : mode} {A t u: term} :
  Γ⊨lam m A t↣* u → md Γ (lam m A t) ≠ ℙ → 
  (∃ A' t', u = lam m A' t' ∧ Γ ⊨ A ↣* A' ∧ m::Γ ⊨ t ↣* t').
Proof.
  intros red_lam not_Prop.
  remember (lam m A t) as t0 eqn:e0.
  induction red_lam as [|w u v H red_v IH] in A, t, t0, e0, red_lam, not_Prop.
  - exists A, t. 
    subst; repeat split; eauto using red_trans_direct, red_refl.
  - subst.
    red_lam_inv_auto A'' t'' e red_A red_t.
    assert (md Γ (lam m A'' t'') ≠ ℙ) as not_Prop'.
    { cbn in *; intro H. apply not_Prop. 
      erewrite red_md; eauto. }
    specialize (IH _ _ eq_refl not_Prop').
    destruct IH as [A' [t' [e [red_A'' red_t'']]]].
    exists A', t'. repeat split.
    * assumption.
    * eapply red_trans_trans; eauto using red_trans_direct.
    * eapply red_trans_trans; eauto using red_trans_direct.
Qed.

Lemma reds_Pi_inv {Γ : scope} {i j: level} {m mx : mode} {A B t: term} :
  Γ⊨Pi i j m mx A B↣* t → 
  (∃ A' B' i' j', t = Pi i' j' m mx A' B' ∧ Γ ⊨ A ↣* A' ∧ mx::Γ ⊨ B ↣* B').
Proof.
  intro red_Pi.
  remember (Pi i j m mx A B) as t0 eqn:e0.
  induction red_Pi as [|w u v H red_v IH] in A, B, i, j, t0, e0, red_Pi.
  - exists A, B, i, j. 
    subst; repeat split; eauto using red_trans_direct, red_refl.
  - subst. 
    apply red_Pi_inv in H.
    destruct H as [A''[B''[i''[j''[e []]]]]].
    specialize (IH _ _ _ _ e).
    destruct IH as [A' [B' [i' [j' [e' [red_A'' red_B'']]]]]].
    exists A', B', i', j'. repeat split.
    * assumption.
    * eapply red_trans_trans; eauto using red_trans_direct.
    * eapply red_trans_trans; eauto using red_trans_direct.
Qed.

Lemma reds_Sort_inv {Γ : scope} {i: level} {m : mode} {t: term} :
  Γ⊨Sort m i ↣* t → ∃ i', t= Sort m i'.
Proof.
  intro red_sort.
  remember (Sort m i) as t0 eqn:e0.
  induction red_sort as [|w u v H red_v IH] in i, t0, e0, red_sort.
  - subst; eauto.
  - subst. 
    apply red_Sort_inv in H.
    destruct H as [i' e].
    eauto.
Qed.

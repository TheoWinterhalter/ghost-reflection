From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT.reduction Require Import Injectivity Model.
From GhostTT.reduction.wrapping Require Import Core Properties.
From GhostTT.reduction.onestep Require Export Reduction.
From GhostTT Require Import Admissible.

Import ListNotations.

Set Default Goal Selector "!".

Section subjet_reduction.

  Ltac ttinv_destruct h :=
    destruct_exists h;
    let rec destruct_conj h :=
      lazymatch type of h with 
      | _ ∧ _ => let H := fresh "H" in 
          destruct h as [H h]; destruct_conj h
      |_ => idtac end
    in destruct_conj h.

  Local Notation 𝝢 := (Erased tnat).
  Local Notation "P ⁺¹" := (S ⋅ P) (at level 1).
  Local Notation "P ⁺²" := (S ⋅ S ⋅ P) (at level 1).
  Local Notation "P ⁺³" := (S ⋅ S ⋅ S ⋅ P) (at level 1).
  Local Notation "P ⁺⁴" := (S ⋅ S ⋅ S ⋅ S ⋅ P) (at level 1).

  Lemma subst_S1 {t u : term} :
    (S ⋅ t) <[ u··] = t.
  Proof.
    intros; asimpl; reflexivity.
  Qed.

  Lemma subst_Sn {t : term} {σ : nat → term} :
    (S ⋅ t) <[up_term σ] = S ⋅ t <[σ].
  Proof.
    intros; asimpl; reflexivity.
  Qed.


  Theorem subjet_reduction (Γ: context) (Ω t t': term) 
    (wfΓ : wf Γ) (red_t : t ↣ t') (type_t : Γ ⊢ t:Ω) :
    Γ⊢ t':Ω.
  Proof.
    destruct red_t 
    as [m A t0 u|t0 P p| m P t f|m P t f|m P z s|m P z s n|m A B P z s|m A a n0 n v P z s | i | i j m mx A B | ]
  in Γ, wfΓ, t, t', Ω, red_t, type_t.
  all: specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i_u type_Ω]].
  all: specialize (scoping_type wfΓ type_t) as scope_Ω.

  (** Congruences **)
  11: {specialize (typing_box type_t) as [B type_u].
    admit. }


  (** Computations **)
  all: ttinv type_t type_t.
  (* if_true if_false nat_elim_zero *)
  3-5: ttinv_destruct type_t; eauto using type_conv.


  (* Beta_red *)
  - (* destruction *)
    destruct type_t as [mx_u [m_t0 [i [j [A0 [B0 type_t]]]]]].
    destruct type_t as [scope_B0 [scope_lam [scope_u [scope_A0 type_t]]]].
    destruct type_t as [type_lam [type_u [type_A0 [type_B0 conv_Ω]]]].
    ttinv type_lam H.
    destruct H as [i0 [j0 [m0 [B H]]]].
    destruct H as [scope_A [scope_B [scope_t0 H]]].
    destruct H as [type_A [type_B [type_t0 conv_Pi]]].
    cbn in *; apply injectivity_Pi in conv_Pi as [e0 [e1 [conv_A conv_B]]]; subst.
    2,3: gscope; apply scoping_castrm; assumption.
    apply castrm_castrm_conv in conv_A, conv_B.

    (* conversion *)
    assert (Γ ⊢ B <[ u··] ε≡ Ω) as conv_Ω'.
    { eapply conv_trans; [ | exact conv_Ω].
      rewrite !castrm_subst.
      eapply conv_subst; eauto.
      fsimpl; cbn.
      eapply sscoping_one.
      exact (scoping_castrm (sc Γ) u mx_u scope_u). }

    (* typing *)
    refine (type_conv wfΓ _ _ conv_Ω' type_Ω).
    * erewrite scoping_md; eauto.
      eapply scoping_subst; eauto using sscoping_one, sscoping_comp_one.
    * eapply typing_subst; eauto.
      eapply styping_one; eauto.
      apply conv_sym in conv_A.
      exact (type_conv wfΓ scope_u type_u conv_A type_A).


      (* reveal_hide *) 
  - (* destruction *)
    destruct type_t as [i [j [m [A0 type_t]]]].
    destruct type_t as [scope_p [scope_hide [scope_P [scope_A0 type_t]]]].
    destruct type_t as [Hm [type_hide [type_P [type_p conv_Ω]]]].
    ttinv type_hide H.
    destruct H as [i0 [A H]].
    destruct H as [scope_A [scope_t0 H]].
    destruct H as [type_A [type_t0 conv_Erased]].
    specialize (validity Γ _ _ wfΓ type_hide) as [_ [i_h type_Erased]].
    ttinv type_Erased H.
    destruct H as [i_e [_ [type_A0 _]]].
    cbn in conv_Erased; apply injectivity_Erased in conv_Erased as conv_A; subst.
    2,3: gscope; apply scoping_castrm; assumption.
    apply castrm_castrm_conv in conv_A.
    clear type_Erased i_h conv_Erased.

    (* conversion *)
    assert (Γ ⊢ app (S ⋅ P) (hide (var 0)) <[t0··] ε≡ Ω) as conv_Ω'.
    { eapply conv_trans; [ | exact conv_Ω].
      asimpl. apply conv_refl. }

    (* typing *)
    refine (type_conv wfΓ _ _ conv_Ω' type_Ω).
    * do 2 (erewrite scoping_md; gscope).
    * apply (type_app wfΓ type_p).
      exact (type_conv wfΓ scope_t0 type_t0 conv_A type_A0).


      (* nat_elim_succ *)
  - (* destruction *)
    destruct type_t as [i [Hm type_t]].
    destruct type_t as [scope_succ [scope_P [scope_z [scope_s type_t]]]].
    destruct type_t as [type_succ [type_P [type_z [type_s conv_Ω]]]].
    ttinv type_succ H.
    destruct H as [i0 [type_n _]].

    (* conversion *)
    assert ( Γ ⊢ app (S ⋅ P) (tsucc (S ⋅ n)) <[(tnat_elim m n P z s)··] ε≡ Ω) as conv_Ω'.
    { eapply conv_trans; [ | exact conv_Ω].
      asimpl. apply conv_refl. }

    (* sub-typing *)
    assert (Γ ⊢ app s n : Pi i i m m (app P n) (app (S ⋅ P) (tsucc (S ⋅ n)))) as type_s_n. 
    { specialize (type_app wfΓ type_s type_n) as type_s_n.
      cbn in type_s_n. 
      rewrite subst_Sn, subst_S1 in type_s_n.
      exact type_s_n. }

    (* typing *)
    refine (type_conv wfΓ _ _ conv_Ω' type_Ω).
    * do 2 (erewrite scoping_md; gscope).
    * refine (type_app wfΓ type_s_n _). 
      gtype.


      (* vec_elim_nil *)
  - (* destruction *)
    destruct type_t as [i [j [Hm type_t]]].
    destruct type_t as [scope_nil [scope_P [scope_z [scope_s type_t]]]].
    destruct type_t as [type_nil [type_P [type_z [type_s type_t]]]].
    destruct type_t as [scope_hide [scope_A [type_A [type_hide conv_Ω]]]].
    ttinv type_nil H.
    destruct H as [i0 H].
    destruct H as [scope_B [type_B conv_vec]].
    cbn in conv_vec; apply injectivity_vec in conv_vec as [conv_B _]; subst.
    2,3: gscope; apply scoping_castrm; assumption.
    apply castrm_castrm_conv in conv_B.

    (* conversion *)
    assert (Γ ⊢ app (app P (hide tzero)) (tvnil A) ε≡ Ω) as conv_Ω'.
    { eapply conv_trans; [ | exact conv_Ω].
      cbn; gconv. exact (conv_sym Γ ε|B| ε|A| conv_B). }

    (* typing *)
    exact (type_conv wfΓ scope_z type_z conv_Ω' type_Ω).


    (* vec_elim_cons *) (* TLDR : just don't read. *)
  - (* destruction *)
    destruct type_t as [i [j [Hm type_t]]].
    destruct type_t as [scope_cons [scope_P [scope_z [scope_s type_t]]]].
    destruct type_t as [type_cons [type_P [type_z [type_s type_t]]]].
    destruct type_t as [scope_n [scope_A [type_A [type_n conv_Ω]]]].
    ttinv type_cons H.
    destruct H as [i0 [A0 H]].
    destruct H as [scope_a [scope_n0 [scope_v H]]].
    destruct H as [type_a [type_n0 [type_v [type_A0 [scope_A0 conv_vec]]]]].
    cbn in conv_vec; apply injectivity_vec in conv_vec as [conv_A0 conv_gS_n0]; subst.
    2,3: gscope; eauto using scoping_castrm.
    2: right; left; reflexivity.
    change (Γ ⊢ ε|gS n0| ε≡ ε|n|) in conv_gS_n0.
    apply castrm_castrm_conv in conv_A0, conv_gS_n0.
    specialize (cong_vec Γ _ _ _ _ conv_A0 (conv_refl Γ ε|n0|)) as conv_vec.
    change (Γ ⊢ tvec A0 n0 ε≡ tvec A n0) in conv_vec.
    specialize (type_vec Γ A n0 _ scope_A scope_n0 type_A type_n0) as type_vec.
    specialize (type_conv wfΓ scope_v type_v conv_vec type_vec) as type_v'.


    (* work on type_s and type_P *)
    (* unfold umax in type_s, type_P.
       cbn in type_s, type_P.
       assert ((if isProp m then 0 else if isProp m then j else Nat.max j j) = if isProp m then 0 else j) as e.
       { case (isProp m); [reflexivity| apply PeanoNat.Nat.max_id]. }
       rewrite e in *; clear e.
       assert (∀ j, Nat.max i (if isProp m then 0 else j) = if isProp m then i else Nat.max i j) as e.
       { intro. case (isProp m); [apply PeanoNat.Nat.max_0_r| reflexivity]. }
       rewrite e in *; clear e.
       assert (∀ i j, (if isProp m then 0 else if isProp m then i else j) = if isProp m then 0 else j ) as e.
       { intros. case (isProp m); reflexivity. }
       rewrite !e in *; clear e.
       remember (if isProp m then 0 else Nat.max i j) as k eqn:ek.
       remember (if isProp m then 0 else j) as l eqn:el.
       change (Γ ⊢ s : 
       Pi i k m 𝕋 A
       (Pi 0 k m 𝔾 𝝢
       (Pi i l m 𝕋 (tvec A⁺² (var 0))
       (Pi j j m m (app (app P⁺³ (var 1)) (var 0))
       (app (app P⁺⁴ (gS (var 2))) 
       (tvcons (var 3) (var 2) (var 1)))))))
       in type_s. *)
    remember (glength A n0 v) as gl eqn:e.
    remember (umax m m j j) as k2 eqn:ek2.
    (* 
    remember (umax 𝔾 m 0 (umax 𝕋 m i k2)) as k0 eqn:ek0.
    remember (umax 𝕋 m i k2) as k1 eqn:ek1.
       change (Γ ⊢ s : 
    Pi i k0 m 𝕋 A
    (Pi 0 k1 m 𝔾 𝝢
    (Pi i k2 m 𝕋 (tvec A⁺² (var 0))
    (Pi j j m m (app (app P⁺³ (var 1)) (var 0))
    (app (app P⁺⁴ (gS (var 2))) 
    (tvcons (var 3) (var 2) (var 1)))))))
       in type_s. *)

       (* sub-sub-sub-typing *)
       (* assert (Γ ⊢ app s a : 
          Pi 0 k1 m 𝔾 𝝢
          (Pi i k2 m 𝕋 (tvec A⁺¹ (var 0))
          (Pi j j m m (app (app P⁺² (var 1)) (var 0))
          (app (app P⁺³ (gS (var 2)))
          (tvcons a⁺³ (var 2) (var 1))))))
          as type_s_a.
          { *)
       specialize (type_conv wfΓ scope_a type_a conv_A0 type_A) as type_a'.
       specialize (type_app wfΓ type_s type_a') as type_s_a.
       cbn in type_s_a. 
       rewrite !subst_Sn, !subst_S1 in type_s_a.
       (* exact type_s_a. } *)

       (* TODO *)
       (* assumption hard to prove *)
       assert (Γ ⊢ gl ε≡ n0) as conv_gl. { admit. }
       assert (Γ ⊢ gl : 𝝢) as type_gl. { admit. }
       assert (Γ ⊢ gl ∷ 𝕋) as scope_gl. { admit. }

       (* sub-sub-typing *)
       assert (Γ ⊢ app (app s a) gl : 
       Pi i k2 m 𝕋 (tvec A n0)
       (Pi j j m m (app (app P⁺¹ n0⁺¹) (var 0))
       (app (app P⁺² (n⁺²))
       (tvcons a⁺² n0⁺² (var 1)))))
       as type_s_a_gl.
       { assert (Γ ⊢ 
         Pi i k2 m 𝕋 (tvec A gl) 
         (Pi j j m m (app (app P⁺¹ gl⁺¹) (var 0)) 
         (app (app P⁺² (gS gl⁺²)) (tvcons a⁺² gl⁺² (var 1))))
         ε≡ 
         Pi i k2 m 𝕋 (tvec A n0) 
         (Pi j j m m (app (app P⁺¹ n0⁺¹) (var 0)) 
         (app (app P⁺² (n⁺²)) (tvcons a⁺² n0⁺² (var 1)))))
         as conv_pi.
         { cbn; gconv.
           4-7: right; reflexivity.
           all: rewrite !castrm_ren.
           2: eapply (conv_trans _ _ (ε|gS gl|)⁺² ε|n|⁺²); [apply conv_refl | ].
           all: repeat (eapply conv_ren; eauto using rtyping_S).
           refine (conv_trans Γ ε|gS gl| ε|gS n0| ε|n| _ conv_gS_n0).
           gconv.
         }
         specialize (type_app wfΓ type_s_a type_gl) as type_s_a_gl.
         cbn in type_s_a_gl. 
         rewrite !subst_Sn, !subst_S1 in type_s_a_gl.
         change (Γ ⊢ app (app s a) gl : 
         Pi i k2 m 𝕋 (tvec A gl)
         (Pi j j m m (app (app P⁺¹ gl⁺¹) (var 0))
         (app (app P⁺² (gS gl⁺²))
         (tvcons a⁺² gl⁺² (var 1)))))
    in type_s_a_gl.
    refine (type_conv wfΓ _ type_s_a_gl conv_pi _).
    * gscope.
    * apply (type_pi wfΓ type_vec).
      subst k2.
      refine (type_pi (wf_cons wfΓ type_vec) _ _).
      all:admit. (* some app to type... *)
       }

       (* sub-typing *)
       (* assert (Γ ⊢ app (app (app s a) gl) v : 
          Pi j j m m (app (app P n0) v)
          (app (app P⁺¹ n⁺¹)
          (tvcons a⁺¹ n0⁺¹ v⁺¹)))
          as type_s_a_gl_v.
          { *)
       specialize (type_app wfΓ type_s_a_gl type_v') as type_s_a_gl_v.
       cbn in type_s_a_gl_v. 
       rewrite !subst_Sn, !subst_S1 in type_s_a_gl_v.
       (* exact type_s_a_gl_v.
          } *)

       (* conversion *)
       assert ( Γ ⊢ app (app P⁺¹ n⁺¹) (tvcons a⁺¹ n0⁺¹ v⁺¹) <[(tvec_elim m A n0 v P z s)··] ε≡ Ω) as conv_Ω'.
       { eapply conv_trans; [ | exact conv_Ω].
         asimpl. apply conv_refl. }

       (* typing *)
       refine (type_conv wfΓ _ _ conv_Ω' type_Ω).
    * subst; repeat (erewrite scoping_md; gscope); auto.
      (*   + intro H; inversion H.
         + eapply scoping_ren; eauto using rscoping_S.
         + do 2 (eapply scoping_ren; eauto using rscoping_S).
         + right; left; reflexivity. *)
    * refine (type_app wfΓ type_s_a_gl_v _). 
      subst; gtype.

      (* Sort *)
  - exact (type_conv wfΓ (scope_sort (sc Γ) ℙ 0) (type_sort Γ ℙ 0) type_t type_Ω).


    (* Pi *)
  - (* destruction *)
    destruct type_t as [scope_A [scope_B type_t]].
    destruct type_t as [type_A [type_B conv_Ω]].

    (* typing *)
    refine (type_conv wfΓ _ _ conv_Ω type_Ω).
    * gscope.
    * case m, mx; cbn; gtype.
      all: refine (type_conv _ _ _ _ _); eauto.
      all: try apply cong_Prop.
      all: try apply type_sort.
      all: eauto using wf_cons.
  Admitted.

End subjet_reduction.

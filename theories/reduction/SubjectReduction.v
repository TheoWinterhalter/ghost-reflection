From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping BasicMetaTheory.
From GhostTT Require Import Model.
From GhostTT.reduction Require Import ReductionProperties ReductionToCongruence Injectivity.
From GhostTT.reduction Require Export Reduction ReductionAndTransitivity.

Import ListNotations.

Set Default Goal Selector "!".

Lemma scoping_type {Γ: context} {A t: term}:
  wf Γ → Γ ⊢ t:A → sc Γ⊢ A∷𝕂.
Proof.
  intros wfΓ type_t.
  specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i type_A]].
  specialize (validity Γ _ _ wfΓ type_A) as [scope_A [j type_scope]].
  ttinv type_scope type_scope.
  apply injectivity_Sort in type_scope.
  rewrite type_scope in *.
  assumption.
Qed.

Lemma type_lam_Pi_inv {Γ : context} {m mx: mode} {i j : level} {f A B : term}:
  wf Γ → Γ ⊢ f : Pi i j m mx A B → (∃ A t, f = lam mx A t) ∨ (∃ n, f = var n).
Proof.
  intros wfΓ type_f.
  induction f.
  2-3: ttinv type_f Hconv; destruct_exists Hconv; repeat destruct Hconv as [_ Hconv]; admit.
  - eauto.
  - ttinv type_f Hconv; destruct_exists Hconv.
    repeat destruct Hconv as [_ Hconv].
    specialize (scoping_type wfΓ type_f) as scope_Pi.
    apply scope_pi_inv in scope_Pi.
    destruct scope_Pi as [scope_A [scope_B _]].
    cbn in Hconv.
    apply injectivity_Pi in Hconv; eauto using scoping_castrm.
    * left. do 2 eexists. admit.
Abort.

Ltac ttinv_destruct h HN:=
  ttinv h HN; destruct_exists HN;
  let rec destruct_conj HN :=
  lazymatch type of HN with 
  | _ ∧ _ => let H := fresh "H" in 
      destruct HN as [H HN]; destruct_conj HN
  |_ => idtac end
  in destruct_conj HN.

Theorem subjet_reduction (Γ: context) (A t t': term):
  wf Γ → (sc Γ) ⊨ t ↣ t' → Γ ⊢ t:A → mdc Γ t ≠ ℙ → Γ⊢ t':A.
Proof.
  intros wfΓ red_t type_t not_Prop.
  remember (sc Γ) as Γ0 eqn:e0.
  induction red_t in Γ, Γ0, e0, wfΓ, A, red_t, type_t, not_Prop.
  all: subst; cbn in *.
  (** Easy cases **)
  (* refl *)
  27: auto.
  (* t of mode ℙ *)
  27-30: contradiction.

  (** Extra hypothesis **)
  all: specialize (validity Γ _ _ wfΓ type_t) as [scope_t [i_u type_A]].
  all: specialize (scoping_type wfΓ type_t) as scope_A.
  all: ttinv_destruct type_t conv_A.

  (** Computations **)
  (* Beta_red *)
  1: admit.
  (* reveal_hide *) 
  1: admit.
  (* Sort *)
  7: {econstructor. 4: gtype. all: gtype. }
  (* Pi *)
  7: admit.
  (* recursive computation *)
  (* end case : if_true if_false nat_elim_zero *)
  1-3: solve [ refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A type_A); 
  [gscope |eauto using red_scope | gtype; reflexivity]].
  (* end_case : vec_elim_nil *)
  2: admit.
  (* recursion case *)
  1-2: admit.

  (* contexts *)
  (* conv_A correct *)
  4,5,10: solve [refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A type_A); 
  [gscope | gscope; eauto using red_scope | 
      gtype; eauto using red_scope;
      erewrite scoping_md; [ |eassumption]; 
          intro HC; inversion HC]].
  1: { refine (type_conv Γ i_u _ _ A _ _ (scoping_type wfΓ type_t) _ _ conv_A type_A);
    [gscope | gscope; eauto using red_scope | ].
    gtype; eauto using red_scope.
    all: try (erewrite scoping_md;[|eassumption]; intro HC; inversion HC).
    + econstructor; eauto using red_scope.
      apply IHred_t1; eauto.
      all: try (erewrite scoping_md;[|eassumption]; intro HC; inversion HC).
    + admit. (* Γ ≡ Δ → Γ ⊢ B:A → Δ ⊢ B:A *)
  }
  (* change type via type_conv and cons_A*)
  1: assert (Γ ⊢ Pi x x0 x1 mx A' x2 ε≡ A) as conv_A'.
  1:{ eapply conv_trans.
    2: eassumption.
    cbn; gconv.
    2-3: right; reflexivity.
    apply conv_sym.
    eapply reduction_to_conversion in red_t1; eauto. }
  2: assert (Γ ⊢ x4 <[ v'··] ε≡ A) as conv_A'.
  2:{ eapply conv_trans.
    2: eassumption.
    do 2 rewrite castrm_subst.
    eapply (conv_subst_r Γ (x::sc Γ)).
    + apply sscoping_castrm. 
      eauto using sscoping_one, red_scope.
    + apply sscoping_castrm. 
      eauto using sscoping_one, red_scope.
    + apply scoping_castrm. eassumption.
    + intro n; destruct n; cbn; gconv.
      apply conv_sym.
      eapply reduction_to_conversion in red_t2; eauto. }
  2: { refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A' type_A); gscope; eauto using red_scope.
    + admit.
    + admit.
    + eapply type_app.
      ++ eassumption.
      ++ eauto using red_scope.
      ++ eauto using red_scope.
      ++ gscope.
      ++ gtype. reflexivity.
      ++ admit.
      ++ assumption.
      ++ assumption. }
 -
      refine (type_conv Γ i_u _ _ A _ _ scope_A _ _ conv_A' type_A).
      1,2: cbn; gscope; eauto using red_scope.
      * eapply red_scope; eauto.
        erewrite scoping_md; eauto.
      * eapply type_lam; gscope; eauto using red_scope.
        + rewrite (scoping_md _ A0 𝕂); eauto; intro HC; inversion HC.
        +admit.
        + econstructor; eauto using red_scope.
          apply IHred_t1; eauto.
          rewrite (scoping_md _ A0 𝕂); eauto; intro HC; inversion HC.
        + admit.
          - refine (type_conv Γ i_u _ _ A _ _ (scoping_type wfΓ type_t) _ _ conv_A type_A); [gscope | gscope; eauto using red_scope | ].
      * cbn; destruct (mdc Γ p) in *; eauto.
      * admit.
      * apply type_reveal. gtype; eauto using red_scope.
        erewrite scoping_md; [intro HC| eassumption]. inversion HC.
          - refine (type_conv Γ i_u _ _ A _ _ (scoping_type wfΓ type_t) _ _ conv_A type_A); [gscope | gscope; eauto using red_scope | ].
            gtype; eauto using red_scope.
            erewrite scoping_md; eauto; intro HC; inversion HC.



      * 
        eapply type_lam. 

        econstructor; gscope; eauto using red_scope.
      * gtype.
      * gscope.
      * cbn in *; inversion scope_t; gscope.
        all: eauto using red_scope.
      * admit.
          - admit.
          - admit.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i' type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: apply type_sort.
      * constructor.
      * eauto using scoping_type.
      * constructor.
      * assumption.
      * eassumption.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i' type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: {constructor; subst; eauto using red_scope.
              + apply IHred_t1; eauto.
                ++ admit.
                ++ admit.
              + apply IHred_t2; eauto.
                ++ eapply wf_cons; eauto; admit.
                ++ admit.
                ++ admit.
            }
      * constructor.
      * eauto using scoping_type.
      * constructor; subst;eauto using red_scope.
      * cbn in *. 
        assert (umax mx m (red_lvl mx i) (red_lvl m j) = umax mx m i j) as e.
        { destruct m, mx; cbn.
          all: reflexivity. }
        rewrite e; assumption.
      * eassumption.
          - admit.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: { gtype; eauto using red_scope.
              + erewrite scoping_md; [ | eassumption].
                intro HC; inversion HC.
              + admit.
              + admit.
        + admit. }
      * gscope. eauto using red_scope.
      * eauto using scoping_type.
      * gscope; eauto using red_scope.
      * eapply conv_trans.
        + cbn. apply cong_Pi.
          ++ apply conv_sym. eauto using reduction_to_conversion.
          ++ gconv.
          ++ right. reflexivity.
          ++ right. reflexivity.
        + eassumption.
      * cbn in type_A.
        erewrite scoping_md in *; eauto.
        gscope.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            admit.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: { gtype; eauto using red_scope.
              erewrite scoping_md; eauto. }
            all: try eassumption.
      * gscope.
      * eauto using scoping_type.
      * gscope; eauto using red_scope.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: { gtype; eauto using red_scope.
              erewrite scoping_md; [|eauto]. 
              intro HC; inversion HC. }
            all: try eassumption.
      * gscope.
      * eauto using scoping_type.
      * gscope; eauto using red_scope.
          - specialize (validity Γ _ _ wfΓ type_t) as [_ [i type_A]].
            ttinv type_t type_t'.
            destruct_exists type_t'; destruct_conj type_t'.
            eapply type_conv.
            4: { gtype; eauto using red_scope; admit. }
            all: try eassumption.
      * gscope; eauto using red_scope.
      * eauto using scoping_type.
      * gscope; eauto using red_scope; admit.
      * admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
Admitted.

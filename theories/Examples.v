(*** Examples from the paper

  We show how we can discriminate booleans and thus natural numbers and thus
  erased natural numbers.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations RAsimpl ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory CScoping CTyping
  CCMetaTheory Admissible Erasure Revival Param Model.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Transparent close ignore epm_lift rpm_lift.

Definition discr_bool :=
  lam mType tbool (
    tif mKind (var 0) (lam mType tbool (Sort mProp 0)) top bot
  ).

Lemma type_discr_bool :
  [] ⊢ discr_bool : tbool ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0.
Proof.
  unfold discr_bool.
  eapply type_lam. 1: constructor. 1,2: gtype.
  assert (hw : wf [ (mType, tbool) ]).
  { eapply wf_cons. 1: constructor. gtype. }
  cbn. eapply type_conv. 1: auto. 1:{ gscope. reflexivity. }
  - gtype. 1: reflexivity.
    + eapply meta_conv.
      * gtype. reflexivity.
      * reflexivity.
    + eapply type_conv. all: gtype.
      * cbn. apply conv_sym. gconv.
      * {
        eapply meta_conv.
        - eapply type_app. 1: auto. 2: gtype.
          eapply type_lam. 1: auto. 1,3: gtype. gtype.
        - reflexivity.
      }
    + eapply type_conv. all: gtype.
      * cbn. apply conv_sym. gconv.
      * {
        eapply meta_conv.
        - eapply type_app. 1: auto. 2: gtype.
          eapply type_lam. 1: auto. 1,3: gtype. gtype.
        - reflexivity.
      }
  - cbn. gconv. reflexivity.
  - gtype.
Qed.

(* Anything goes actually *)
Lemma rtyping_triv :
  ∀ Γ, rtyping Γ id [].
Proof.
  intros Γ. intros x m A e.
  destruct x. all: discriminate.
Qed.

Lemma type_discr_bool_gen :
  ∀ Γ, Γ ⊢ discr_bool : tbool ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0.
Proof.
  intros Γ.
  pose proof type_discr_bool as h.
  eapply typing_ren in h.
  - exact h.
  - apply rtyping_triv.
Qed.

Opaque discr_bool.

Definition iszero :=
  lam mType tnat (
    tnat_elim mType (var 0) (lam mType tnat tbool)
      (* 0 *) ttrue
      (* S n *) (lam mType tnat (lam mType tbool tfalse))
  ).

Lemma type_iszero :
  [] ⊢ iszero : tnat ⇒[ 0 | 0 / mType | mType ] tbool.
Proof.
  gtype. 1: discriminate. 1: reflexivity.
  cbn.
  assert (hw : wf [ (mType, tnat) ]).
  { econstructor.
    - constructor.
    - gscope.
    - gtype.
  }
  assert (hwx : wf [ (mType, tnat) ; (mType, tnat) ]).
  { econstructor.
    - auto.
    - gscope.
    - gtype.
  }
  assert (h : [(mType, tnat); (mType, tnat)] ⊢ app (lam mType tnat tbool) (var 0) : Sort mType 0).
  { eapply meta_conv.
    - eapply type_app. 1: auto.
      + eapply type_lam. 1: auto. 1,3: gtype.
        gtype.
      + eapply meta_conv.
        * gtype. reflexivity.
        * reflexivity.
    - reflexivity.
  }
  assert (hw2 : wf [ (mType, app (lam mType tnat tbool) (var 0)) ; (mType, tnat) ; (mType, tnat) ]).
  { eapply wf_cons. all: eauto. }
  eapply type_conv. 1: auto. 1: gscope ; eauto ; discriminate.
  - eapply type_nat_elim. all: try solve [ gtype ].
    + discriminate.
    + gscope. reflexivity.
    + eapply meta_conv.
      * gtype. reflexivity.
      * reflexivity.
    + eapply type_conv. 1: auto. 1: gscope.
      * gtype.
      * apply conv_sym. gconv.
      * {
        eapply meta_conv.
        - eapply type_app. 1: auto. 2: gtype.
          eapply type_lam. 1: auto. 1,3: gtype.
          gtype.
        - cbn. reflexivity.
      }
    + eapply type_lam. 1: auto. 1: gtype.
      * {
        eapply meta_conv.
        - eapply type_pi. 1: auto.
          + cbn. auto.
          + cbn. eapply meta_conv.
            * {
              eapply type_app. 1: auto.
              - eapply type_lam. 1: auto. 1,3: gtype.
                gtype.
              - gtype.
                + reflexivity.
                + eapply meta_conv.
                  * gtype. reflexivity.
                  * reflexivity.
            }
            * reflexivity.
        - reflexivity.
      }
      * {
        eapply type_conv. 1: auto. 1: gscope.
        - eapply type_lam. 1: auto. 1,3: gtype. gtype.
        - cbn. apply conv_sym. gconv. all: try reflexivity.
          all: unfold ueq. all: auto.
        - cbn. eapply type_pi. 1: auto.
          + eapply meta_conv.
            * eapply type_app. 1: auto.
              2:{
                gtype. reflexivity.
              }
              cbn. eapply type_lam. 1: auto. 1,3: gtype.
              gtype.
            * reflexivity.
          + eapply meta_conv.
            * eapply type_app. 1: auto.
              2:{
                gtype.
                - reflexivity.
                - eapply meta_conv.
                  + gtype. reflexivity.
                  + reflexivity.
              }
              eapply type_lam. 1: auto. 1,3: gtype. gtype.
            * reflexivity.
      }
  - gconv. reflexivity.
  - gtype.
Qed.

Lemma type_iszero_gen :
  ∀ Γ, Γ ⊢ iszero : tnat ⇒[ 0 | 0 / mType | mType ] tbool.
Proof.
  intros Γ.
  pose proof type_iszero as h.
  eapply typing_ren in h.
  - exact h.
  - apply rtyping_triv.
Qed.

Opaque iszero.

Definition discr_nat :=
  lam mType tnat (
    app discr_bool (app iszero (var 0))
  ).

Lemma type_discr_nat :
  [] ⊢ discr_nat : tnat ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0.
Proof.
  unfold discr_nat.
  eapply type_lam. 1: constructor. 1,2: gtype.
  assert (hw : wf [ (mType, tnat) ]).
  { eapply wf_cons. 1: constructor. gtype. }
  cbn. eapply meta_conv.
  - eapply type_app. 1: auto.
    + eapply type_discr_bool_gen.
    + eapply meta_conv.
      * eapply type_app. 1: auto. 1: eapply type_iszero_gen.
        eapply meta_conv. 1: gtype ; reflexivity.
        reflexivity.
      * reflexivity.
  - reflexivity.
Qed.

Lemma type_discr_nat_gen :
  ∀ Γ, Γ ⊢ discr_nat : tnat ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0.
Proof.
  intros Γ.
  pose proof type_discr_nat as h.
  eapply typing_ren in h.
  - exact h.
  - apply rtyping_triv.
Qed.

Opaque discr_nat.

Definition erased_nat_discrP :=
  lam mGhost (Erased tnat) (
    Reveal (var 0) discr_nat
  ).

Lemma type_erased_nat_discrP :
  [] ⊢ erased_nat_discrP : Erased tnat ⇒[ 0 | 0 / mGhost | mKind ] Sort mProp 0.
Proof.
  cbn. eapply type_lam. 1: constructor. 1,2: gtype.
  eapply type_Reveal.
  - eapply wf_cons. 1: constructor. gtype.
  - eapply meta_conv.
    + gtype. reflexivity.
    + reflexivity.
  - eapply type_discr_nat_gen.
Qed.

Lemma type_erased_nat_discrP_gen :
  ∀ Γ, Γ ⊢ erased_nat_discrP : Erased tnat ⇒[ 0 | 0 / mGhost | mKind ] Sort mProp 0.
Proof.
  intros Γ.
  pose proof type_erased_nat_discrP as h.
  eapply typing_ren in h.
  - exact h.
  - apply rtyping_triv.
Qed.

Opaque erased_nat_discrP.

Lemma type_gS :
  ∀ Γ n,
    wf Γ →
    Γ ⊢ n : Erased tnat →
    Γ ⊢ gS n : Erased tnat.
Proof.
  intros Γ n hw hn.
  unfold gS.
  assert (hw2 : wf ((mType, tnat) :: Γ)).
  { eapply wf_cons. 1: auto. gtype. }
  eapply type_conv_alt. 1: auto.
  - eapply type_reveal. 1,3: eassumption.
    2:{
      eapply type_lam. all: cbn. 1: auto. all: gtype.
    }
    + cbn. auto.
    + eapply type_lam. all: cbn. 1: auto. 1: gtype.
      * {
        eapply meta_conv.
        - eapply type_app. 1: auto.
          2:{
            eapply type_hide. 1: auto.
            2:{ gtype. reflexivity. }
            cbn. gtype.
          }
          eapply type_lam. all: cbn. 1: auto. 1,3: gtype. gtype.
        - reflexivity.
      }
      * {
        eapply type_conv. 1: auto. 1:{ gscope. reflexivity. }
        - eapply type_hide. 1: auto.
          2:{
            gtype.
            - reflexivity.
            - eapply meta_conv.
              + gtype. reflexivity.
              + reflexivity.
          }
          gtype.
        - apply conv_sym. gconv. reflexivity.
        - eapply meta_conv.
          + eapply type_app. 1: auto.
            2:{
              eapply type_hide. 1: auto.
              2:{
                gtype. reflexivity.
              }
              cbn. gtype.
            }
            eapply type_lam. all: cbn. 1: auto. 1,3: gtype. gtype.
          + reflexivity.
      }
  - cbn. gconv.
    eapply scoping_castrm. eapply mode_coherence. 1,3: eauto.
    gtype.
  - eapply meta_conv.
    + eapply type_app. 1: auto. 2: eauto.
      eapply type_lam. 1: auto. 1,3: gtype. gtype.
    + reflexivity.
  - gtype.
Qed.

Definition star :=
  lam mProp bot (var 0).

Lemma type_star :
  [] ⊢ star : top.
Proof.
  gtype. all: reflexivity.
Qed.

Lemma type_star_gen :
  ∀ Γ, Γ ⊢ star : top.
Proof.
  intros Γ.
  pose proof type_star as h.
  eapply typing_ren in h.
  - exact h.
  - apply rtyping_triv.
Qed.

Definition discr :=
  lam mGhost (Erased tnat) (
    reveal (var 0)
      (lam mGhost (Erased tnat) (gheq (Erased tnat) (hide tzero) (gS (var 0)) ⇒[ 0 | 0 / mProp | mProp ] bot))
      (lam mType tnat (
        lam mProp (gheq (Erased tnat) (hide tzero) (hide (tsucc (var 0)))) (
          fromRev (tsucc (var 1)) discr_nat (
            ghcast (Erased tnat) (hide tzero) (hide (tsucc (var 1))) (var 0) erased_nat_discrP (
              toRev tzero discr_nat star
            )
          )
        )
      ))
  ).

Lemma type_discr :
  [] ⊢ discr :
    Pi 0 0 mProp mGhost (Erased tnat) (
      (gheq (Erased tnat) (hide tzero) (gS (var 0))) ⇒[ 0 | 0 / mProp | mProp ]
      bot
    ).
Proof.
  assert (hw : wf [ (mGhost, Erased tnat) ]).
  { eapply wf_cons. 1: constructor. gtype. }
  assert (hw2 : wf [ (mGhost, Erased tnat) ; (mGhost, Erased tnat) ]).
  { eapply wf_cons. 1: auto. gtype. }
  assert (hw3 : wf [ (mType, tnat) ; (mGhost, Erased tnat) ]).
  { eapply wf_cons. 1: auto. gtype. }
  assert (hw4 : wf [ (mGhost, Erased tnat) ; (mType, tnat) ; (mGhost, Erased tnat) ]).
  { eapply wf_cons. 1: auto. gtype. }
  assert (hge : [ (mType, tnat); (mGhost, Erased tnat) ] ⊢ gheq (Erased tnat) (hide tzero) (hide (tsucc (var 0))) : Sort mProp 0).
  { eapply type_gheq. 1: auto. 1,2: gtype.
    eapply type_hide. 1: auto. 1: gtype.
    eapply type_succ. 1:{ gscope. reflexivity. }
    eapply meta_conv.
    - gtype. reflexivity.
    - reflexivity.
  }
  assert (hw5 : wf [ (mProp, gheq (Erased tnat) (hide tzero) (hide (tsucc (var 0)))) ; (mType, tnat) ; (mGhost, Erased tnat) ]).
  { eapply wf_cons. all: eauto. }
  cbn. eapply type_lam. 1: constructor. 1: gtype.
  - eapply type_pi. 1: auto. 2: gtype.
    eapply type_gheq. 1: auto. all: gtype.
    eapply type_gS. 1: auto.
    eapply meta_conv.
    + gtype. reflexivity.
    + reflexivity.
  - assert (hg : [(mGhost, Erased tnat) ; (mGhost, Erased tnat)] ⊢ gheq (Erased tnat) (hide tzero) (gS (var 0)) : Sort mProp 0).
    { eapply type_gheq. 1: auto. 1,2: gtype.
      eapply type_gS. 1: auto.
      eapply meta_conv.
      - gtype. reflexivity.
      - reflexivity.
    }
    assert (hw6 : wf [(mType, tnat); (mGhost, Erased tnat); (mType, tnat); (mGhost, Erased tnat)]).
    { eapply wf_cons. 1: auto. gtype. }
    eapply type_conv_alt. 1: auto.
    + eapply type_reveal. 1: auto.
      2:{
        eapply meta_conv.
        - gtype. reflexivity.
        - reflexivity.
      }
      2:{
        eapply type_lam. all: cbn. 1: auto. 1,2: gtype.
        eapply type_pi. 1,2: auto.
        gtype.
      }
      1: cbn ; auto.
      cbn. eapply type_lam. 1: auto. 1: gtype.
      * {
        eapply meta_conv.
        - eapply type_app. 1: auto.
          + eapply type_lam. 1: auto. 1: gtype.
            2:{
              eapply type_pi. 1: auto.
              - eapply type_gheq. 1: auto. 1,2: gtype.
                eapply type_gS. 1: auto.
                eapply meta_conv.
                + gtype. reflexivity.
                + reflexivity.
              - gtype.
            }
            cbn. gtype.
          + eapply type_hide. 1: auto. 1: gtype.
            eapply meta_conv.
            * gtype. reflexivity.
            * reflexivity.
        - reflexivity.
      }
      * {
        eapply type_conv_alt. 1: auto.
        - eapply type_lam. 1,2: eauto.
          2:{
            eapply type_fromRev. 1: auto.
            1:{
              eapply type_succ. 1:{ gscope. reflexivity. }
              eapply meta_conv.
              - gtype. reflexivity.
              - reflexivity.
            }
            1: eapply type_discr_nat_gen.
            eapply type_conv_alt. 1: auto.
            - eapply type_ghcast. 1: auto.
              2:{
                eapply meta_conv.
                - gtype. reflexivity.
                - reflexivity.
              }
              2:{
                eapply meta_conv.
                - eapply type_erased_nat_discrP_gen.
                - cbn. f_equal.
              }
              1: discriminate.
              eapply type_conv_alt. 1: auto.
              + eapply type_toRev. 1: auto.
                * eapply type_zero.
                * eapply type_discr_nat_gen.
                * {
                  eapply type_conv. 1: auto. 1:{ gscope. reflexivity. }
                  - eapply type_star_gen.
                  - apply conv_sym. Transparent discr_nat discr_bool iszero.
                    cbn. eapply conv_trans.
                    1:{
                      eapply conv_beta.
                      - gscope.
                      - gscope. all: try reflexivity. discriminate.
                      - gscope.
                    }
                    cbn. eapply conv_trans.
                    1:{
                      eapply conv_beta.
                      - gscope.
                      - gscope. reflexivity.
                      - gscope.
                        + discriminate.
                        + reflexivity.
                    }
                    cbn. eapply conv_trans.
                    1:{
                      econstructor. 2-4: apply conv_refl.
                      eapply conv_beta.
                      - gscope.
                      - gscope. 2: reflexivity. discriminate.
                      - gscope.
                    }
                    cbn. eapply conv_trans.
                    1:{
                      econstructor. 2-4: apply conv_refl.
                      eapply conv_nat_elim_zero.
                      - discriminate.
                      - gscope.
                      - gscope.
                      - gscope.
                    }
                    apply conv_if_true.
                    gscope.
                  - eapply meta_conv.
                    + eapply type_app. 1: auto. 1: eapply type_discr_nat_gen.
                      eapply type_zero.
                    + reflexivity.
                }
              + apply conv_sym. Transparent erased_nat_discrP. cbn.
                eapply conv_trans.
                1:{
                  eapply conv_beta.
                  - gscope.
                  - gscope. all: try reflexivity. discriminate.
                  - gscope.
                }
                cbn. apply conv_refl.
              + eapply type_Reveal. 1: auto. 2: eapply type_discr_nat_gen.
                eapply type_hide. 1: auto. all: gtype.
              + eapply meta_conv.
                * eapply type_app. 1: auto.
                  1: eapply type_erased_nat_discrP_gen.
                  gtype.
                * reflexivity.
            - cbn. eapply conv_trans.
              1:{
                eapply conv_beta. all: gscope. all: try reflexivity.
                discriminate.
              }
              cbn. apply conv_refl.
            - eapply meta_conv.
              + eapply type_app. 1: auto. 1: eapply type_erased_nat_discrP_gen.
                eapply type_hide. 1: auto. 1: gtype.
                eapply type_succ. 1:{ gscope. reflexivity. }
                eapply meta_conv.
                * gtype. reflexivity.
                * reflexivity.
              + reflexivity.
            - eapply type_Reveal. 1: auto. 2: eapply type_discr_nat_gen.
              eapply type_hide. 1: auto. 1: gtype.
              eapply type_succ. 1:{ gscope. reflexivity. }
              eapply meta_conv.
              + gtype. reflexivity.
              + reflexivity.
          }
          eapply meta_conv.
          + eapply type_app. 1: auto. 1: eapply type_discr_nat_gen.
            eapply type_succ. 1:{ gscope. reflexivity. }
            eapply meta_conv.
            * gtype. reflexivity.
            * reflexivity.
          + reflexivity.
        - apply conv_sym. cbn. eapply conv_trans.
          1:{
            eapply conv_beta. all: gscope. all: try reflexivity.
            cbn. auto.
          }
          cbn. gconv.
          3,4: unfold ueq ; auto.
          + eapply conv_trans.
            1:{
              econstructor. all: gscope. all: try reflexivity.
              cbn. auto.
            }
            eapply conv_beta. all: gscope. all: reflexivity.
          + apply conv_sym. eapply conv_trans.
            1:{
              eapply conv_beta. all: gscope. all: try reflexivity.
              discriminate.
            }
            cbn. eapply conv_trans.
            1:{
              eapply conv_beta. all: gscope. all: try reflexivity.
              discriminate.
            }
            cbn. eapply conv_trans.
            1:{
              econstructor. 2-4: apply conv_refl.
              eapply conv_beta. all: gscope. all: try reflexivity.
              discriminate.
            }
            cbn. eapply conv_trans.
            1:{
              econstructor. 2-4: apply conv_refl.
              econstructor. all: gscope. all: try reflexivity.
              discriminate.
            }
            eapply conv_trans.
            1:{
              econstructor. 2-4: apply conv_refl.
              econstructor. 2: apply conv_refl.
              econstructor. all: gscope. reflexivity.
            }
            cbn. eapply conv_trans.
            1:{
              econstructor. 2-4: apply conv_refl.
              econstructor. all: gscope. 2: reflexivity.
              discriminate.
            }
            cbn. econstructor. gscope.
        - eapply type_pi. 1: auto. 1: auto.
          eapply meta_conv.
          + eapply type_app. 1: auto. 1: eapply type_discr_nat_gen.
            eapply type_succ. 1:{ gscope. reflexivity. }
            eapply meta_conv.
            * gtype. reflexivity.
            * reflexivity.
          + reflexivity.
        - eapply meta_conv.
          + eapply type_app. 1: auto.
            2:{
              eapply type_hide. 1: auto.
              2:{ gtype. reflexivity. }
              cbn. gtype.
            }
            cbn. eapply type_lam. 1: auto. 1: gtype.
            2:{
              eapply type_pi. 1: auto. 2: gtype.
              eapply type_gheq. 1: auto. 1,2: gtype.
              eapply type_conv. 1: auto.
              1:{ gscope. all: try reflexivity. cbn. auto. }
              - eapply type_reveal. 1: auto.
                2:{
                  eapply meta_conv.
                  - gtype. reflexivity.
                  - reflexivity.
                }
                2:{
                  eapply type_lam. all: cbn. 1: auto. 1-3: gtype.
                }
                1:{ cbn. auto. }
                cbn. eapply type_lam. 1: auto. 1: gtype.
                2:{
                  eapply type_conv. 1: auto.
                  1:{ gscope. reflexivity. }
                  - eapply type_hide. 1: auto.
                    2:{
                      eapply type_succ. 1:{ gscope. reflexivity. }
                      eapply meta_conv.
                      - gtype. reflexivity.
                      - reflexivity.
                    }
                    gtype.
                  - cbn. apply conv_sym. gconv. reflexivity.
                  - eapply meta_conv.
                    + eapply type_app. 1: auto.
                      * eapply type_lam. 1: auto. 1,3: gtype. gtype.
                      * eapply type_hide. 1: auto. 1: gtype.
                        eapply meta_conv. 1: gtype. all: reflexivity.
                    + reflexivity.
                }
                eapply meta_conv.
                + eapply type_app. 1: auto.
                  * eapply type_lam. 1: auto. 1,3: gtype. gtype.
                  * eapply type_hide. 1: auto. 1: gtype.
                    eapply meta_conv. 1: gtype. all: reflexivity.
                + reflexivity.
              - cbn. gconv. reflexivity.
              - gtype.
            }
            cbn. gtype.
          + reflexivity.
      }
    + cbn. eapply conv_trans.
      1:{
        econstructor. all: gscope. all: try reflexivity.
        cbn. auto.
      }
      cbn. apply conv_refl.
    + eapply meta_conv.
      * eapply type_app. 1: auto. 2:{ gtype. reflexivity. }
        cbn. eapply type_lam. 1: auto. 1: gtype.
        2:{
          eapply type_pi. 1: auto. 1: auto. gtype.
        }
        cbn. gtype.
      * reflexivity.
    + eapply type_pi. 1: auto. 2: gtype.
      eapply type_gheq. 1: auto. 1,2: gtype.
      eapply type_gS. 1: auto.
      eapply meta_conv. 1: gtype. all: reflexivity.
Qed.

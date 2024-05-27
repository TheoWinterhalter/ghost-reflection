(*** Examples from the paper

  We show how we can discriminate booleans and thus natural numbers.
  This in turn let us write head and tail functions.

***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
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

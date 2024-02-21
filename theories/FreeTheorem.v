(*** Proof of concept for free theorems obtained from parametricity

  We're going to look at only one example we hope is sufficient to showcase
  parametricity.
  We are going to show that our model justifies the following property:

  ∀ (f : erased bool → bool), f (hide true) = f (hide false)

  In other words, every function from erased booleans to proper booleans has
  to be the constant function.

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

(** The type of our alleged constant functions **)
Definition cst_ty :=
  Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool.

(** Impredicative encoding of equality for bool

  This spares us the effort of formalising yet another inductive type.
  We of course do not expect any trouble with the inductive version.

**)

Definition beq b b' :=
  Pi 0 0 mProp mKind (tbool ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0) (
    app (var 0) (S ⋅ b) ⇒[ 0 | 0 / mProp | mProp ] app (var 0) (S ⋅ b')
  ).

(** Sanity check **)
Lemma type_beq :
  ∀ Γ b b',
    wf Γ →
    Γ ⊢ b : tbool →
    Γ ⊢ b' : tbool →
    Γ ⊢ beq b b' : Sort mProp 0.
Proof.
  intros Γ b b' hΓ h h'.
  unfold beq. eapply type_pi_opt.
  - assumption.
  - eapply type_pi.
    + assumption.
    + constructor.
    + cbn. constructor.
  - intro hΓ'.
    eapply type_pi_opt.
    + assumption.
    + eapply meta_conv.
      * {
        eapply type_app.
        - assumption.
        - eapply meta_conv.
          + econstructor. reflexivity.
          + cbn. reflexivity.
        - eapply meta_conv.
          + eapply typing_ren. 1: apply rtyping_S.
            eassumption.
          + reflexivity.
      }
      * reflexivity.
    + intro hΓ''.
      eapply meta_conv.
      * {
        cbn.
        eapply type_app.
        - assumption.
        - eapply meta_conv.
          + econstructor. cbn. reflexivity.
          + cbn. reflexivity.
        - eapply meta_conv.
          + eapply typing_ren. 1: apply rtyping_S.
            eapply typing_ren. 1: apply rtyping_S.
            eassumption.
          + reflexivity.
      }
      * reflexivity.
Qed.

(** Our target property (the type we want inhabited in the model) **)
Definition er_bool_cst :=
  Pi 0 0 mProp mType cst_ty (
    beq (app (var 0) (hide ttrue)) (app (var 0) (hide tfalse))
  ).

Lemma type_er_bool_cst :
  [] ⊢ er_bool_cst : Sort mProp 0.
Proof.
  unfold er_bool_cst.
  eapply type_pi_opt.
  - constructor.
  - unfold cst_ty. eapply type_pi.
    + constructor.
    + eapply type_erased. 1: constructor.
      constructor.
    + cbn. constructor.
  - intro hwf.
    eapply type_beq. 1: assumption.
    + eapply meta_conv.
      * {
        eapply type_app.
        - assumption.
        - eapply meta_conv.
          + econstructor. reflexivity.
          + cbn. reflexivity.
        - eapply type_hide. 1: assumption.
          + constructor.
          + constructor.
      }
      * reflexivity.
    + eapply meta_conv.
      * {
        eapply type_app.
        - assumption.
        - eapply meta_conv.
          + econstructor. reflexivity.
          + cbn. reflexivity.
        - eapply type_hide. 1: assumption.
          + constructor.
          + constructor.
      }
      * reflexivity.
Qed.

Lemma constant_bool :
  ∑ prf, [] ⊢ᶜ prf : ⟦ [] | er_bool_cst ⟧p.
Proof.
  cbn.
  eexists. eapply ctype_conv.
  2:{
    unfold pPi. apply cconv_sym.
    econstructor.
    1:{ eapply cconv_trans. 1: constructor. constructor. }
    econstructor.
    1:{
      unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
      cbn. econstructor. 1: constructor.
      econv.
    }
    econstructor.
    1:{
      eapply cconv_trans. 1: constructor.
      econstructor. all: constructor.
    }
    econstructor.
    1:{
      unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
      cbn. econstructor. 1: constructor.
      econstructor. 1: econv.
      eapply cconv_trans. 1: constructor.
      cbn. econv.
    }
    econv.
  }
  2:{
    pose proof type_er_bool_cst as h.
    eapply param_typing in h. cbn in h.
    eapply param_pProp in h.
    eapply h.
  }
  unfold vreg. cbn.
  (** What remains to be prove now is the following:

    ∀ (fe : ebool) (fP : ∀ (b : ebool) (bP : pbool b), pbool fe)
      (P : ebool → unit) (PP : ∀ (b : ebool) (bP : pbool b), Prop),
      PP fe (fP etrue ptrue) →
      PP fe (fP efalse pfalse).

  **)
  eapply ctype_lam. 1: ertype.
  eapply ctype_lam.
  1:{
    ertype.
    - eapply ccmeta_conv.
      + ertype. eapply ccmeta_conv. 1: ertype.
        reflexivity.
      + reflexivity.
    - eapply ccmeta_conv.
      + ertype. eapply ccmeta_conv. 1: ertype.
        reflexivity.
      + reflexivity.
  }
  eapply ctype_lam. 1: ertype.
  eapply ctype_lam.
  1:{
    ertype. eapply ccmeta_conv.
    - ertype. eapply ccmeta_conv. 1: ertype.
      reflexivity.
    - reflexivity.
  }
  eapply ctype_lam.
  1:{
    eapply ccmeta_conv.
    - ertype.
      2:{
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv. 1: ertype.
          cbn. lhs_ssimpl. reflexivity.
        - cbn. reflexivity.
      }
      eapply ccmeta_conv.
      + ertype. eapply ccmeta_conv. 1: ertype.
        cbn. reflexivity.
      + cbn. reflexivity.
    - cbn. reflexivity.
  }
  instantiate (1 := cvar 0).
  econstructor.
  - ertype.
  - cbn. econstructor. 1: econv.
    eapply cconv_irr. all: escope.
    all: reflexivity.
  - eapply ccmeta_conv.
    + ertype.
      2:{
        eapply ccmeta_conv.
        - ertype. eapply ccmeta_conv. 1: ertype.
          cbn. lhs_ssimpl. reflexivity.
        - cbn. reflexivity.
      }
      eapply ccmeta_conv.
      * ertype. eapply ccmeta_conv. 1: ertype.
        cbn. reflexivity.
      * cbn. reflexivity.
    + reflexivity.
Qed.

(** Let's show it in Coq too so it's clearer what happens. **)

Inductive err_bool :=
| err_true
| err_false
| err.

Inductive pm_bool : err_bool → SProp :=
| pm_true : pm_bool err_true
| pm_false : pm_bool err_false.

Lemma goal :
  ∀ (fe : err_bool) (fP : ∀ (b : err_bool) (bP : pm_bool b), pm_bool fe)
    (P : err_bool → unit) (PP : ∀ (b : err_bool) (bP : pm_bool b), Prop),
    PP fe (fP err_true pm_true) →
    PP fe (fP err_false pm_false).
Proof.
  intros fe fP _ P h.
  exact h.
Qed.

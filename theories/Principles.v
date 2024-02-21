(*** Testing principles obtained from parametricity ***)

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

(** f : erased bool → bool has to be the constant function

  But do we get that from parametricity?
  It seems what we get for such an f is
  ∀ (b : ebool) (bP : pbool b), pbool ⟦ f ⟧ε

  This looks promising, maybe I should define some form of boolean equality?
  Like bool_eq b b' := if b then (if b' then True else False) else False.
  Maybe with True := False → False.

**)

Transparent close ignore epm_lift rpm_lift.

Eval lazy in  ⟦ [] | Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool ⟧p.

Definition cst_ty :=
  Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool.

Lemma erase_bool :
  ∀ f,
    [] ⊢ᶜ capp ⟦ [] | cst_ty ⟧p f ≡
    cPi cType ebool (cPi cProp (capp pbool (cvar 0)) (capp pbool (S ⋅ S ⋅ f))).
Proof.
  intros f.
  cbn. unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
  cbn. econv.
Qed.

Lemma constant_bool :
  ∀ f,
    [] ⊢ f : Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool →
    True.
Proof.
  intros f hf.
  eapply mode_coherence in hf as hm. 2: constructor.
  2:{ econstructor. all: repeat constructor. }
  eapply param_typing in hf as hfP.
  unfold ptype in hfP. remd in hfP. simpl relm in hfP. cbn match in hfP.
  eapply ctype_conv in hfP.
  2: eapply erase_bool.
  2:{ ertype. all: admit. }
Abort.

Definition bool_eq b b' :=
  tif mProp b (lam mType tbool (Sort mKind 0) (Sort mProp 0))
    (* then *) (
      tif mProp b' (lam mType tbool (Sort mKind 0) (Sort mProp 0))
        (* then *) top
        (* else *) bot
    )
    (* else *) (
      tif mProp b (lam mType tbool (Sort mKind 0) (Sort mProp 0))
        (* then *) bot
        (* else *) top
    ).

(* Sanity check *)
Lemma type_bool_eq :
  ∀ Γ b b',
    wf Γ →
    Γ ⊢ b : tbool →
    Γ ⊢ b' : tbool →
    Γ ⊢ bool_eq b b' : Sort mProp 0.
Proof.
  intros Γ b b' hΓ h h'.
  unfold bool_eq.
  eapply meta_conv.
  - eapply type_if. all: eauto.
    + discriminate.
    + eapply meta_conv.
      * {
        eapply type_lam.
        - assumption.
        - constructor.
        - constructor.
        - constructor.
      }
      * cbn. (* This is ill typed because we disallow large elimination!
        It should be possible to recover it for bool though.
      *)
        admit.
    + admit.
    + admit.
  - admit.
Abort.

Lemma constant_bool :
  ∑ prf,
    [] ⊢ᶜ prf : ⟦ [] |
      Pi 0 0 mProp mType cst_ty (
        bool_eq (app (var 0) ttrue) (app (var 0) tfalse)
      )
    ⟧p.
Proof.
  (* cbn - [cst_ty].
  eexists. eapply ctype_conv.
  2:{
    apply cconv_sym. eapply ccong_pPi.
    - cbn. eapply cconv_trans. 1: constructor.
      constructor.
    - apply erase_bool.
    -
  } *)
  cbn.
  eexists. eapply ctype_conv.
  2:{
    apply cconv_sym. unfold pPi. cbn. econstructor.
    - eapply cconv_trans. 1: constructor.
      constructor.
    - econstructor.
      + eapply cconv_trans. 1: constructor.
        cbn. econstructor. 1: constructor.
        econv.
      + econstructor.
        * econv.
        * {
          unfold plam. cbn. econstructor.
          - constructor.
          - econv.
        }
        * {
          econstructor.
          - econv.
          - unfold plam. cbn. econstructor.
            + constructor.
            + econv.
          - econv.
          - econv.
        }
        * econv.
  }
  2: admit.
  (*
    ∀ (b : ebool) (f : ∀ (b' : ebool) (bP' : pbool b'), pbool b),
      pif (f etrue ptrue) then (
        pif (f efalse pfalse) then True else False
      )
      else False

    This definition of bool_eq is wrong, so it translates to the wrong thing
    (conjunction) but it seems we already do synchronise things because f
    always lands in pbool b, so it is determined by its value.
  *)
  (* I'm a bit confused about the return type though. It looks as though
    the pif returns some pProp, which is not a type. Maybe let's try to type
    the type after all.
  *)
  (* eapply type_plam. 1,2: ertype.
  1:{
    eapply ccmeta_conv.
    - ertype. eapply ccmeta_conv. 1: ertype.
      reflexivity.
    - cbn. reflexivity.
  } *)
Abort.

(* Impredicative encoding of equality instead *)

Definition beq b b' :=
  Pi 0 0 mProp mKind (tbool ⇒[ 0 | 0 / mType | mKind ] Sort mProp 0) (
    app (var 0) (S ⋅ b) ⇒[ 0 | 0 / mProp | mProp ] app (var 0) (S ⋅ b')
  ).

Lemma type_pi_opt :
  ∀ Γ i j mx m A B,
    wf Γ →
    Γ ⊢ A : Sort mx i →
    (wf (Γ ,, (mx, A)) → Γ ,, (mx, A) ⊢ B : Sort m j) →
    Γ ⊢ Pi i j m mx A B : Sort m (umax mx m i j).
Proof.
  intros Γ i j mx m A B hΓ hA hB.
  eapply type_pi. all: auto.
  apply hB. eapply wf_cons. all: eauto.
Qed.

(* Sanity check *)
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

(* Our target property (the type we want inhabited in the model) *)
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

(* Let's show it in Coq too so it's clearer what happens. *)

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

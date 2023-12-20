(** Basic meta-theory before building the model **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Typing.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Definition rscoping (Γ : scope) (ρ : nat → nat) (Δ : scope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some m →
    nth_error Γ (ρ x) = Some m.

Inductive sscoping (Γ : scope) (σ : nat → term) : scope → Prop :=
| scope_nil : sscoping Γ σ []
| scope_cons :
    ∀ Δ m,
      sscoping Γ (↑ >> σ) Δ →
      scoping Γ (σ var_zero) m →
      sscoping Γ σ (m :: Δ).

Lemma scoping_ren :
  ∀ Γ Δ ρ t m,
    rscoping Γ ρ Δ →
    scoping Δ t m →
    scoping Γ (ren_term ρ t) m.
Proof.
  intros Γ Δ ρ t m hρ ht.
  assert (lem :
    ∀ Γ Δ ρ mx,
      rscoping Γ ρ Δ →
      rscoping (mx :: Γ) (0 .: ρ >> S) (mx :: Δ)
  ).
  { intros ? ? ? mx h' y my e.
    destruct y.
    - simpl in *. assumption.
    - simpl in *. apply h'. assumption.
  }
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ asimpl ; econstructor ; eauto ].
Qed.

Lemma sscoping_weak :
  ∀ Γ Δ σ m,
    sscoping Γ σ Δ →
    sscoping (m :: Γ) (σ >> ren_term ↑) Δ.
Proof.
  intros Γ Δ σ m h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + asimpl. eapply scoping_ren. 2: eassumption.
      intros x mx e. simpl. assumption.
Qed.

Lemma md_subst :
  ∀ Γ Δ σ t m,
    sscoping Γ σ Δ →
    scoping Δ t m →
    scoping Γ (t <[ σ ]) m.
Proof.
  intros Γ Δ σ t m hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ asimpl ; econstructor ; eauto ].
  - rename H into hx, Γ0 into Δ.
    asimpl. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
    destruct x.
    + simpl in *. inversion hx. subst. assumption.
    + apply IHhσ. simpl in hx. assumption.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply sscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
  - asimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * asimpl. apply sscoping_weak. assumption.
      * asimpl. constructor. reflexivity.
Qed.

(** Cast removal preserves modes **)

Lemma md_castrm :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (castrm t) m.
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ simpl ; econstructor ; eauto ].
  cbn. assumption.
Qed.

(** Cast removal commutes with renamings **)

Lemma castrm_ren :
  ∀ t ρ,
    ε| ρ ⋅ t | = ρ ⋅ ε| t |.
Proof.
  intros t ρ.
  induction t in ρ |- *.
  all: try reflexivity.
  all: solve [ simpl ; asimpl ; repeat core.unfold_funcomp ; f_equal ; auto ].
Qed.

(** Cast removal commutes with substitution **)

Lemma castrm_subst :
  ∀ t σ,
    ε| t <[ σ ] | = ε| t | <[ σ >> castrm ].
Proof.
  intros t σ.
  assert (∀ σ t,
    t <[ (var 0 .: σ >> ren1 ↑) >> castrm] =
    t <[ var 0 .: σ >> (castrm >> ren1 ↑) ]
  ).
  { intros θ u.
    apply subst_term_morphism2. intros n.
    destruct n.
    - asimpl. repeat core.unfold_funcomp. simpl. reflexivity.
    - asimpl. repeat core.unfold_funcomp. simpl.
      apply castrm_ren.
  }
  induction t in σ |- *. all: try reflexivity.
  all: try solve [ asimpl ; repeat core.unfold_funcomp ; simpl ; f_equal ; auto ].
  - asimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    asimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
  - asimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    asimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
Qed.

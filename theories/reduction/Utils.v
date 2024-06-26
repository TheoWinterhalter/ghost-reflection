(* Definition of multistep reduction rules which corresponds to the congruence relation *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl 
  TermMode Scoping BasicMetaTheory Univ TermNotations Typing.
From GhostTT.reduction Require Import Notations.

Set Default Goal Selector "!".

Definition mode_eq : ∀ (x y : mode), { x = y } + { x ≠ y }.
Proof.
  decide equality.
Defined.

Definition red_lvl (m : mode) (i : level) : level :=
  if mode_eq m ℙ then 0 else i.

Derive NoConfusion Subterm for term.

Lemma md_ren' {Γ Δ :scope} {t: term} {ρ: nat → nat} (e : ∀ n, nth (ρ n) Γ 𝕋 = nth n Δ 𝕋) : 
  md Δ t = md Γ (ρ ⋅ t).
Proof.
  induction t in Γ, Δ, t, ρ, e|- *.
  all: cbn; eauto.
  - cbn. match goal with H: ∀ _ _, _ → _ |- _ =>
    eapply H; eauto end.
    intro n; destruct n; cbn; auto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
Qed.

Lemma md_up_term {Γ : scope} {m: mode} {σ : nat → term} {n : nat} :
  md (m::Γ) (up_term σ (S n)) = md Γ (σ n).
Proof.
  asimpl; ssimpl.
  unfold shift.
  symmetry.
  apply md_ren'.
  induction n; eauto.
Qed.

Lemma md_subst' {Γ Δ :scope} {t: term} {σ: nat → term} (e : ∀ n, md Γ (σ n) = nth n Δ 𝕋) : 
  md Δ t = md Γ (t<[σ]).
Proof.
  induction t in Γ, Δ, t, σ, e|- *.
  all: cbn; eauto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
    intro n; destruct n; eauto.
    erewrite md_up_term. auto.
  - match goal with H: ∀ _ _, _ → _ |- _ =>
    erewrite H; eauto end.
Qed.


Lemma glenght_red_subst (A n v : term) (σ : nat → term) :
  (glength A n v)<[σ] = glength (A<[σ]) (n<[σ]) (v<[σ]).
Proof.
  change (tvec_elim 𝔾 (A <[ σ]) (n <[ σ]) (v <[ σ])
  (lam 𝔾 (Erased tnat) 
  (lam 𝕋 ((tvec (S ⋅ A) (var 0))<[up_term σ]) (Erased tnat))
  )
  (hide tzero)
  (lam 𝕋 (A<[σ])
  (lam 𝔾 (Erased tnat)
  (lam 𝕋 (tvec (S ⋅ S ⋅ A) (var 0) <[up_term (up_term σ)]) 
  (lam 𝔾 (Erased tnat) 
  (gS (var 0)) 
  <[(up_term (up_term (up_term σ)))])
  )
  )
  )
  = glength (A<[σ]) (n<[σ]) (v<[σ])).
  unfold glength.
  repeat f_equal.
  all: asimpl; reflexivity.
Qed.


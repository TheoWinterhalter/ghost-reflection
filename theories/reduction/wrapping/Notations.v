From Coq Require Import Utf8.
From GhostTT Require Import Scoping ContextDecl Typing.
From GhostTT.reduction Require Export Notations.
From GhostTT.reduction.wrapping Require Import Core.

Notation "□¹_term" := box_term_1 : wrap_scope.
Notation "□²_term" := box_term_2 : wrap_scope.
Notation "□_term" := box_term : wrap_scope.
Notation "C [□/ t ]" := (wrapping C t) : wrap_scope.
Notation "C [□¹/ t ]" := (wrapping (Box_1 C) t) : wrap_scope.
Notation "C [□²/ t ]" := (wrapping (Box_2 C) t) : wrap_scope.

Notation "Γ ⇜~ C" := (wrapping_context Γ C) : wrap_scope.
Notation "Γ ⇜ C" := (wrapping_scope Γ C) : wrap_scope.

Notation "Γ ⇜ C ⊢ t : A" := (typing (wrapping_context Γ C) t A) : wrap_scope.
Notation "Γ ⇜ C ⊢ t ∷ m" := (scoping (sc (wrapping_context Γ C)) t m) : wrap_scope. 
Notation "Γ ⇜ C ⊨ t ∷ m" := (scoping (wrapping_scope Γ C) t m) : wrap_scope.


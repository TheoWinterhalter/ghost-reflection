From Coq Require Import Utf8 List.
From Equations Require Import Equations.

From GhostTT.autosubst Require Import AST.
From GhostTT Require Import BasicAST ContextDecl.

Set Default Goal Selector "!".
Set Equations Transparent.

Reserved Notation "'ε|' u |" (at level 0).

Equations castrm : term → term := {
  ε| var x | := var x ;
  ε| Sort m l | := Sort m l ;
  ε| Pi m mx A B | := Pi m mx ε|A| ε|B| ;
  ε| lam mx A t | := lam mx ε|A| ε|t| ;
  ε| app u v | := app ε|u| ε|v| ;
  ε| Erased A | := Erased ε|A| ;
  ε| erase t | := erase ε|t| ;
  ε| reveal t P p | := reveal ε|t| ε|P| ε|p| ;
  ε| revealP t p | := revealP ε|t| ε|p| ;
  ε| gheq A u v | := gheq ε|A| ε|u| ε|v| ;
  ε| ghrefl A u | := ghrefl ε|A| ε|u| ;
  ε| ghcast e P t | := ε|t| ;
  ε| bot | := bot ;
  ε| bot_elim m A p | := bot_elim m ε|A| ε|p|
}
where "ε| u |" := (castrm u).


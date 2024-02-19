From Coq Require Import Utf8 List.
From Equations Require Import Equations.

From GhostTT.autosubst Require Import GAST.
From GhostTT Require Import BasicAST ContextDecl.

Set Default Goal Selector "!".
Set Equations Transparent.

Reserved Notation "'ε|' u |" (at level 0).

Equations castrm : term → term := {
  ε| var x | := var x ;
  ε| Sort m l | := Sort m l ;
  ε| Pi i j m mx A B | := Pi i j m mx ε|A| ε|B| ;
  ε| lam mx A B t | := lam mx ε|A| ε|B| ε|t| ;
  ε| app u v | := app ε|u| ε|v| ;
  ε| Erased A | := Erased ε|A| ;
  ε| hide t | := hide ε|t| ;
  ε| reveal t P p | := reveal ε|t| ε|P| ε|p| ;
  ε| Reveal t p | := Reveal ε|t| ε|p| ;
  ε| toRev t p u | := toRev ε|t| ε|p| ε|u| ;
  ε| fromRev t p u | := fromRev ε|t| ε|p| ε|u| ;
  ε| gheq A u v | := gheq ε|A| ε|u| ε|v| ;
  ε| ghrefl A u | := ghrefl ε|A| ε|u| ;
  ε| ghcast A u v e P t | := ε|t| ;
  ε| tbool | := tbool ;
  ε| ttrue | := ttrue ;
  ε| tfalse | := tfalse ;
  ε| tif m b P t f | := tif m ε|b| ε|P| ε|t| ε|f| ;
  ε| bot | := bot ;
  ε| bot_elim m A p | := bot_elim m ε|A| ε|p|
}
where "ε| u |" := (castrm u).


-- Universe levels and qualities
level : Type
mode : Type

-- Syntax

term(var) : Type

Sort : mode -> level -> term

Pi : level -> level -> mode -> mode -> term -> (bind term in term) -> term
lam : mode -> term -> (bind term in term) -> term
app : term -> term -> term

Erased : term -> term
hide : term -> term
reveal : term -> term -> term -> term
Reveal : term -> term -> term
toRev : term -> term -> term -> term
fromRev : term -> term -> term -> term

gheq : term -> term -> term -> term
ghrefl : term -> term -> term
ghcast : term -> term -> term -> term -> term -> term -> term

tbool : term
ttrue : term
tfalse : term
tif : mode -> term -> term -> term -> term -> term

tnat : term
tzero : term
tsucc : term -> term
tnat_elim : mode -> term -> term -> term -> term -> term

tvec : term -> term -> term
tvnil : term -> term
tvcons : term -> term -> term -> term
tvec_elim : mode -> term -> term -> term -> term -> term -> term -> term

bot : term
bot_elim : mode -> term -> term -> term

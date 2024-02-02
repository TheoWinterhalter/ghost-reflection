-- Universe levels and qualities
level : Type
mode : Type

-- Syntax

term(var) : Type

Sort : mode -> level -> term

Pi : level -> level -> mode -> mode -> term -> (bind term in term) -> term
lam : mode -> term -> (bind term in term) -> (bind term in term) -> term
app : term -> term -> term

Erased : term -> term
hide : term -> term
reveal : term -> term -> term -> term
Reveal : term -> term -> term

gheq : term -> term -> term -> term
ghrefl : term -> term -> term
ghcast : term -> term -> term -> term -> term -> term -> term

bot : term
bot_elim : mode -> term -> term -> term

-- Universe levels and qualities
level : Type
mode : Type

-- Syntax

term(var) : Type

Sort : mode -> level -> term

Pi : mode -> mode -> term -> (bind term in term) -> term
lam : mode -> term -> (bind term in term) -> term
app : term -> term -> term

Erased : term -> term
erase : term -> term
reveal : term -> term -> term -> term
revealP : term -> term -> term

gheq : term -> term -> term -> term
ghrefl : term -> term -> term
ghcast : term -> term -> term -> term

bot : term
bot_elim : mode -> term -> term -> term

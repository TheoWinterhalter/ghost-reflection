-- Universe levels and qualities
level : Type
cmode : Type

-- Syntax

cterm(cvar) : Type

cSort : cmode -> level -> cterm

cPi : cmode -> cterm -> (bind cterm in cterm) -> cterm
clam : cmode -> cterm -> (bind cterm in cterm) -> cterm
capp : cterm -> cterm -> cterm

cunit : cterm
ctt : cterm

ctop : cterm
cstar : cterm

cbot : cterm
cbot_elim : cmode -> cterm -> cterm -> cterm

-- Special inductive types

cty : level -> cterm
ctyval : cterm -> cterm -> cterm
ctyerr : cterm
cEl : cterm -> cterm
cErr : cterm -> cterm

squash : cterm -> cterm
sq : cterm -> cterm
sq_elim : cterm -> cterm -> cterm -> cterm

teq : cterm -> cterm -> cterm -> cterm
trefl : cterm -> cterm -> cterm
tJ : cterm -> cterm -> cterm

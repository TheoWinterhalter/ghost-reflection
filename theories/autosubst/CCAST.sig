-- Universe levels and qualities
level : Type
cmode : Type
mark : Type

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
ctyval : mark -> cterm -> cterm -> cterm
ctyerr : cterm
cEl : cterm -> cterm
cErr : cterm -> cterm

squash : cterm -> cterm
sq : cterm -> cterm
sq_elim : cterm -> cterm -> cterm -> cterm

teq : cterm -> cterm -> cterm -> cterm
trefl : cterm -> cterm -> cterm
tJ : cterm -> cterm -> cterm -> cterm

ebool : cterm
etrue : cterm
efalse : cterm
bool_err : cterm
eif : cmode -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm

pbool : cterm
ptrue : cterm
pfalse : cterm
pif : cterm -> cterm -> cterm -> cterm -> cterm

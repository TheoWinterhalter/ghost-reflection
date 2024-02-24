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

enat : cterm
ezero : cterm
esucc : cterm -> cterm
enat_elim : cterm -> cterm -> cterm -> cterm -> cterm

pnat : cterm
pzero : cterm
psucc : cterm -> cterm
pnat_elim : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
pnat_elimP : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm

evec : cterm -> cterm
evnil : cterm -> cterm
evcons : cterm -> cterm -> cterm
evec_elim : cterm -> cterm -> cterm -> cterm -> cterm -> cterm

pvec : cterm -> cterm -> cterm -> cterm -> cterm -> cterm
pvnil : cterm -> cterm
pvcons : cterm -> cterm -> cterm -> cterm
pvec_elim : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm
pvec_elimP : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm

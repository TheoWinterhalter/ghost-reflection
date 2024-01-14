-- Universe levels and qualities
level : Type
cmode : Type
role : Type

-- Syntax

cterm(_cvar) : Type

-- Variables are split in two constructors due to an Autosubst limitation
cvar_proj : role -> cterm -> cterm

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

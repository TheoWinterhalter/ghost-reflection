-- Universe levels and qualities
level : Type
cmode : Type

-- Syntax

cterm(cvar) : Type

cSort : cmode -> level -> cterm

cPi : cmode -> cterm -> (bind cterm in cterm) -> cterm
clam : cmode -> cterm -> (bind cterm in cterm) -> cterm
capp : cterm -> cterm -> cterm

cbot : cterm
cbot_elim : cmode -> cterm -> cterm -> cterm

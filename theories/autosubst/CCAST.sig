-- Universe levels and qualities
level : Type
cmode : Type

-- Syntax

cterm(var) : Type

cSort : cmode -> level -> cterm

cPi : level -> level -> cmode -> cmode -> cterm -> (bind cterm in cterm) -> cterm
clam : cmode -> cterm -> (bind cterm in cterm) -> (bind cterm in cterm) -> cterm
capp : cterm -> cterm -> cterm

cbot : cterm
cbot_elim : cmode -> cterm -> cterm -> cterm

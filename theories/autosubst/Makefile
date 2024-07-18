syntax:
	autosubst -f -s ucoq -v ge813 -allfv GAST.sig -o GAST.v
	sed -i '1s/^/From GhostTT Require Import BasicAST.\n/' GAST.v
	sed -i '2s/^/From GhostTT.autosubst /' GAST.v
	autosubst -f -s ucoq -v ge813 -allfv CCAST.sig -o CCAST.v
	sed -i '1s/^/From GhostTT Require Import BasicAST.\n/' CCAST.v
	sed -i '2s/^/From GhostTT.autosubst /' CCAST.v
	sed -i '10s/^/From GhostTT.autosubst /' unscoped.v

clean:
	rm *.v

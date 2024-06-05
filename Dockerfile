FROM coqorg/coq:8.18-ocaml-4.14-flambda

SHELL ["/bin/bash", "--login", "-o", "pipefail", "-c"]

# Add opam repo
RUN set -x \
  && eval $(opam env --switch=${COMPILER} --set-switch) \
  && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released

# update opam
RUN set -x \
  && opam update \
  && opam upgrade -y -v -j ${NJOBS}

# build Equations
RUN set -x \
  && eval $(opam env --switch=${COMPILER} --set-switch) \
  && opam install -y -v -j ${NJOBS} coq-equations.1.3+8.18

# build repo
RUN ["/bin/bash", "--login", "-c", "set -x \
  && git clone --depth=1 --branch=anonymous-icfp https://github.com/TheoWinterhalter/ghost-reflection.git \
  && cd ghost-reflection \
  && rm -rf .git \
  && rm -f Dockerfile \
  && opam install . --deps-only -y -v -j ${NJOBS} \
  && make -j ${NJOBS}"]

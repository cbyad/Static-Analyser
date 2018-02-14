FROM debian:stable

RUN \
  apt-get update && \
  apt-get install -y --no-install-recommends m4 libgmp3-dev libmpfr-dev ocaml-nox ocaml-native-compilers wget aspcud ca-certificates opam && \
  apt-get autoremove -y && \
  apt-get clean -y && \
  rm -rf /var/lib/apt/lists && \
  rm -rf /usr/share/doc && \
  adduser --disabled-password --gecos 'TAS Project' tas

COPY . /home/tas
RUN chown -R tas:tas /home/tas

USER tas
WORKDIR /home/tas

RUN \
  opam init -y && \
  opam config -y env && \
  opam install -y menhir zarith mlgmpidl apron && \
  rm -rf .opam/repo  

# Flottants primitifs en Coq (@ JFLA 2021)

* Érik Martin-Dorel (IRIT, UPS, Toulouse)
* Pierre Roux (ONERA, Toulouse)
* basé sur un travail de Guillaume Bertholon

## Fichier Coq (démo)

* [demo_coq_floats.v](./demo_coq_floats.v)

## Prérequis (instructions d'installation)

```bash
opam install coq-native  # optionnel
opam install coq.8.13.2

opam install coq-flocq

opam install coq-interval

opam pin add -n -y -k git coq-mathcomp-multinomials.1.5.4 https://github.com/erikmd/multinomials.git#make-1.5.4
opam pin add -n -y -k git coq-validsdp.dev https://github.com/validsdp/validsdp.git#master
opam install coq-validsdp -j2
```

## Article

* dans les [actes de JFLA 2021](https://hal.inria.fr/hal-03190426)

(*+ Flottants primitifs en Coq +*)

(*!********************************************!*)
(*!   Erik Martin-Dorel (IRIT, UPS, Toulouse)  !*)
(*!       & Pierre Roux (ONERA, Toulouse)      !*)
(*!                                            !*)
(*! basé sur un travail de Guillaume Bertholon !*)
(*!********************************************!*)

(** * Démonstration des flottants primitifs

      (réalisée avec Coq 8.13.2)

      Nécessite Coq >= 8.13 (et facultativement, coq-native) *)

From Coq Require Import ZArith Int63.

(** ** Un module de la librairie standard *)

(** On importe le module Floats de la librairie standard de Coq *)
From Coq Require Import Floats.

(** on obtient un type des flottants primitifs *)
Check float.

(** ** Constantes *)

(** les constantes sont interprétées comme
    le flottant le plus proche *)
Open Scope float_scope.

Check 0.5.

(** (§) avec warning si un arrondi est nécessaire *)
Check 0.1.

(** l'impression se fait avec 17 décimales, ce qui garantit
    que (parse o print) est injectif *)

(** néanmoins, ça peut donner des choses un peu étranges *)
Goal 0.99999999999999995 = 1.
Proof. reflexivity. Qed.

(** on peut voir la valeur exacte en hexadécimal *)
Set Printing All.
Check 0.1.
Unset Printing All.

(** on a trois valeurs spéciales *)
Check nan.
Check infinity.
Check neg_infinity.

(** et le 0 est signé *)
Check 0.
Check -0.

Goal 0 = -0.
Proof. Fail reflexivity. Abort.

(** (§) mais pas les NaNs (nan est unique) *)
Goal nan = -nan.
Proof. reflexivity. Qed.

(** ** Opérations primitives *)

(** *** Opérations arithmétiques *)

(** on dispose des opération arithmétiques standard
    (toutes en arrondi au plus proche (tie to even)) *)
Eval compute in - 0.5.
Eval compute in abs (- 0.5).
Eval compute in 1 + 0.5.
Eval compute in 1 - 0.5.
Eval compute in 0.5 * 3.
Eval compute in 3 / 2.
Eval compute in 1 / 0.
Eval compute in 1 / (-0).
Eval compute in sqrt 2.
Eval compute in sqrt (-2).

(** *** (§) Comparaison (pas équivalente à eq !) *)

Eval compute in 0.5 ?= 1.
Eval compute in 0.5 ?= 0.5.
Eval compute in infinity ?= 0.5.
Eval compute in 0 ?= (-0).
Eval compute in 1 ?= nan.
Eval compute in nan ?= nan.

(** et les fonctions booléennes *)
Eval compute in 0.5 <=? 1.
Eval compute in 1 <? 1.
Eval compute in 1 =? 1.

(** *** "Destructeurs" *)

(** - (§) classe *)
Eval compute in classify 0.5.
Print float_class.

(** - (§) mantisse (entre 0.5 et 1)
       et exposant (int63 non signé ; décalé de 2101) *)
Check frshiftexp.
Definition m_e := Eval compute in frshiftexp 15.
Print m_e.
Eval compute in 0.9375 * 16. (** 16 = 2^4 = 2^(2105 - 2101) *)

(** - mantisse comme un int63 *)
Eval compute in normfr_mantissa 0.9375.

(** - quelques fonctions pratiques (implémentées en Coq) *)
Eval compute in is_nan 0.
Eval compute in nan =? nan.
Eval compute in is_zero 0.
Eval compute in is_infinity 0.
Eval compute in get_sign (-0). (* true si < 0 (IEEE 754's sign bit) *)
Eval compute in frexp 15. (** frshiftexp dans Z au lieu de int63,
                              sans décalage *)
Eval compute in ulp 15. (** Unit in Last Place *)

(** *** "Constructeurs" (autres que les littéraux) *)

(** - à partir d'un entier non signé *)
Eval compute in of_int63 15.

(** - décalage d'exposant (décalé de 2101) *)
Check ldshiftexp.
Eval compute in ldshiftexp 10 2103. (** 10 * 2^(2103 - 2101) = 10*2^2 *)
Eval compute in ldshiftexp (fst m_e) (snd m_e).

(** - ldexp : ldexp sur Z au lieu de int63, sans décalage *)
Eval compute in ldexp 10 3.

(** *** (§) Prédécesseur et successeur *)

(** pour implémenter l'arithmétique d'intervalle *)
Eval compute in next_up 1.
Eval compute in next_down 1.
Eval compute in next_up neg_infinity.
Eval compute in next_down infinity.

(* et si le temps le permet, remarque sur
   quelques valeurs flottantes remarquables *)
Eval compute in classify (next_down infinity).
Eval compute in next_up 0.
Eval compute in classify (next_up 0).
Eval compute in next_up 1 - 1.

(** tout est implémenté aussi avec vm_compute et native_compute *)
Eval vm_compute in 1 + 0.5.
Eval native_compute in 1 + 0.5.
(* Nécessite coq-native (https://opam.ocaml.org/packages/coq-native/)
   sinon "fallback" vers vm_compute avec un warning *)
Eval vm_compute in sqrt 2.

(** ** Spécification *)

(** 1. On dispose d'un type spec_float *)
Print spec_float.

(** 2. de fonctions float <-> spec_float *)
Check Prim2SF.
Check SF2Prim.

(** 3. d'une implémentation de chaque fonction *)
Print SFopp.

(** 4. et d'un axiome de correction *)
Check opp_spec.
Check add_spec.

(** Cette spécification est extraite de la librairie Flocq.
    C'est un extrait minimal (seulement 400 lignes) mais peu commode.

    (§) En pratique on utilisera Flocq (>= 3.3)
    qui fait le lien avec les réels de la librairie standard.

    Nécessite d'installer le paquet : opam install coq-flocq
 *)
From Coq Require Import Reals.
Require Import Flocq.IEEE754.BinarySingleNaN Flocq.IEEE754.PrimFloat.

Check Prim2B.
Check B2R.
Check add_equiv.
Check Bplus_correct.

(** * Exemples d'utilisation *)

(** ** Librairie Coq.Interval: https://gitlab.inria.fr/coqinterval/interval

       Nécessite d'installer le paquet : opam install coq-interval
 *)

Require Import Coquelicot.Coquelicot Interval.Tactic.

Lemma Rump_Tucker :
  Rabs (RInt (fun x => sin (x + exp x)) 0 8 - 3474/10000) <= 1/10.
Proof.
(** flottants émulés (avec bigZ) : ~33 s *)
(* Time integral with (i_degree 6, i_fuel 1000, i_prec 53). *)
Undo.
(** flottants primitifs : ~1.8 s *)
Time integral with (i_degree 6, i_fuel 1000).
Undo.
(** flottants primitifs et native_compute : ~0.6 s *)
Time integral with (i_degree 6, i_fuel 1000, i_native_compute).
Qed. (* The Qed being immediate. *)

(** ** Librairie ValidSDP: https://github.com/validsdp/validsdp

       Nécessite d'installer coq-validsdp (to be released soon):

       opam pin add -n -y -k git coq-mathcomp-multinomials.1.5.4 https://github.com/erikmd/multinomials.git#make-1.5.4
       opam pin add -n -y -k git coq-validsdp.dev https://github.com/validsdp/validsdp.git#master
       opam install coq-validsdp -j2
*)

(** une "grosse" matrice

    Nécessite d'exécuter : coqc matrice.v
 *)
Require Import matrice.
Check A.

(** de taille 120x120 *)
Eval compute in length A.

(** on prouve qu'elle est semi-définie positive *)

Require Import ValidSDP.posdef_check.

(** d'abord avec des flottants émulés (bigZ) : ~3.6 s *)
Lemma with_bigint : posdef_seqF A.
Time posdef_check.
Qed.

Print Assumptions with_bigint.

(* Int63.mul : Int63.int -> Int63.int -> Int63.int *)
(* Int63.mul_spec : forall x y : Int63.int, Int63.to_Z (Int63.mul x y)
   = BinInt.Z.modulo (BinInt.Z.mul (Int63.to_Z x) (Int63.to_Z y)) Int63.wB *)

(** puis avec des flottants primitifs : ~0.2 s *)
Lemma with_prim_float : posdef_seqF A.
Time primitive_posdef_check.
Qed.

Print Assumptions with_prim_float.

(* mul_spec : forall x y : float, Prim2SF (x * y)
   = SF64mul (Prim2SF x) (Prim2SF y) *)

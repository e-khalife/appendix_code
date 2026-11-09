# Code-Level Formal Verification of Gradient Descent Convergence for Unconstrained Quadratic Programs

This repository contains the annotated C programs and the Rocq proofs of the paper. All of them are formally verified: WP discharges every proof obligation of the C programs, and Rocq checks every standalone proof and certificate.

## Contents

```text
rocq/
  certificate_H2.v   Q - mI and LI - Q are positive definite, i.e., (H2), for the case study
  eig_bounds.v       the eigenvalues of Q lie in [m, L] (Remark 1)
  vec_model.v        the axioms vec_of_get and vlin_get hold in a model (Section 4.2.2)
real_model/
  gd_Q_SD.c          Pathway SD
  gd_Q_SD_stop.c     Pathway SD, with the stopping criterion
  gd_Q_DC.c          Pathway DC
  gd_Q_DC_stop.c     Pathway DC, with the stopping criterion
float_model/
  the same four programs with the rounding errors of Section 6.2, with the suffix _float
```

Each C file includes its header, which contains the logic definitions and the lemmas. The constants are those of the case study (Section 7.3). Each of the two model folders also contains, in `reports/`, the WP report of each of its programs.

## The dimension d

The case study has d = 3, but the proof obligations and their proof times do not grow with d: the programs, their annotations, and the Rocq proofs are the same for every d. Only the certificates of m and L depend on d. We verified the programs for large d and obtained the same results.

## Running the verification

The C programs are verified with Frama-C 32.1 and its plugin WP, Why3 1.8.2, Alt-Ergo 2.5.4, CVC5 1.2.0, Z3 4.8.12, and Rocq 9.1.1. In the folder of a C file:

```sh
frama-c -wp -wp-rte -wp-model real -wp-cache none -wp-timeout 60 \
  -wp-prover alt-ergo,cvc5,z3,coq \
  -local-tactic -local-tactic-rocq-import Reals,Psatz \
  gd_Q_SD.c -then -report
```

The options `-local-tactic` and `-local-tactic-rocq-import` load a WP extension that attaches the Rocq proofs to the lemmas. The other C files are verified in the same way.

The standalone proofs are checked with `rocq compile eig_bounds.v` and `rocq compile vec_model.v`. The certificates use ValidSDP 1.0.4 with Coq 8.20, and are checked with `coqc certificate_H2.v`.

## Reading the reports

Each report ends with the status of every property, under `Status Report Summary`. Every property is validated, except the base and step axioms of the recursive sums and the axioms `vec_of_get` and `vlin_get`, which are considered valid (Section 4.2). In a first run, the first summary lists the lemmas proved in Rocq as timeouts, because the WP extension attaches their Rocq proofs after this summary. The next pass proves them.

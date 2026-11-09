(* eig_bounds.v

   The eigenvalue bounds of Remark 2.

   Pathway SD requires the eigenvalues of Q, i.e., the diagonal entries of D in a
   spectral decomposition Q = U^T D U, to lie in [m, L] (precondition spectrum, where
   eig(i) is the i-th diagonal entry of D). This script proves that every matrix Q that
   satisfies (H2) has this property: if m ||v||^2 <= v^T Q v <= L ||v||^2 for every
   vector v, and Q = U^T D U with U U^T = I, then m <= D_ii <= L for every i. Evaluating
   (H2) at the i-th row u_i of U gives the bounds, since u_i^T Q u_i = D_ii and
   ||u_i||^2 = 1. The proof uses only U U^T = I, holds for every dimension n, and holds
   over every numeric domain of MathComp, which includes the real numbers. Print
   Assumptions reports no axiom.

   Check with: rocq compile eig_bounds.v
*)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section EigBounds.

Variable R : numDomainType.
Variable n : nat.

Implicit Types (A U D : 'M[R]_n) (v : 'cV[R]_n).

(* the quadratic form v^T A v and the squared norm ||v||^2, as scalars *)
Definition qform A v : R := (v^T *m A *m v) 0 0.
Definition nform v : R := (v^T *m v) 0 0.

(* u_i: the i-th row of U, as a column vector *)
Definition urow U (i : 'I_n) : 'cV[R]_n := \col_k U i k.

(* the quadratic form of A at u_i is the (i,i) entry of U A U^T *)
Lemma qform_urow A U (i : 'I_n) : qform A (urow U i) = (U *m A *m U^T) i i.
Proof.
rewrite /qform /urow !mxE; apply: eq_bigr => l _; rewrite !mxE; congr (_ * _).
by apply: eq_bigr => k _; rewrite !mxE.
Qed.

(* the squared norm of u_i is the (i,i) entry of U U^T *)
Lemma nform_urow U (i : 'I_n) : nform (urow U i) = (U *m U^T) i i.
Proof. by rewrite /nform /urow !mxE; apply: eq_bigr => k _; rewrite !mxE. Qed.

(* with U U^T = I, the decomposition Q = U^T D U gives D = U Q U^T *)
Lemma D_of_decomp Q U D : U *m U^T = 1%:M -> Q = U^T *m D *m U -> D = U *m Q *m U^T.
Proof. by move=> HU ->; rewrite !mulmxA HU mul1mx -mulmxA HU mulmx1. Qed.

(* Remark 2: (H2), Q = U^T D U, and U U^T = I give m <= D_ii <= L *)
Theorem eig_bounds (m L : R) Q U D :
  U *m U^T = 1%:M ->
  Q = U^T *m D *m U ->
  (forall v, m * nform v <= qform Q v) ->
  (forall v, qform Q v <= L * nform v) ->
  forall i, m <= D i i <= L.
Proof.
move=> HU HQ Hlo Hhi i.
(* u_i has norm 1, and the quadratic form of Q at u_i is D_ii *)
have Hn : nform (urow U i) = 1 by rewrite nform_urow HU !mxE eqxx mulr1n.
have Hq : qform Q (urow U i) = D i i by rewrite qform_urow -(D_of_decomp HU HQ).
(* (H2) at u_i *)
apply/andP; split.
  by have := Hlo (urow U i); rewrite Hn Hq mulr1.
by have := Hhi (urow U i); rewrite Hn Hq mulr1.
Qed.

End EigBounds.

Print Assumptions eig_bounds.

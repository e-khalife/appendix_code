/* Problem constants (the only part the user edits) */
/* executable code */
#define d      3
#define ALPHA  0.027398
#define N      8
/* annotations only */
#define m      27.58
#define L      45.417
#define RHO    0.2444
#define R0     0.03464
#define TAU    1e-06
#define DELTA  7.4e-13

#include "gd_logic_SD_float.h"

/* Gradient descent on f(x) = 1/2 x^T Q x + p^T x, Pathway SD, floating-point version.
   Each iteration k:
        - g <- Q x + p     (g[i] = row i of Q dotted with x, plus p[i])
        - x <- x - ALPHA g
   The label `old` names the state at the start of the iteration, so
   vec_of{old}(x) is x^k and vec_of(x) is x^{k+1} after the update.
   The proof obligations are discharged in the real model. The invariant decay_float
   bounds the error by Rhat(k), and the assertion decay_next_float shows that the exact
   update lies DELTA inside Rhat(k+1), which leaves room for the rounding errors of the
   iteration. The postcondition is unchanged. */

/*@ requires \valid_read(Q + (0 .. d*d - 1)) && \valid_read(p + (0 .. d - 1));
    requires \valid(x + (0 .. d - 1)) && \valid(g + (0 .. d - 1));
    requires \separated(Q + (0 .. d*d - 1), p + (0 .. d - 1),
                        x + (0 .. d - 1), g + (0 .. d - 1));
    // the array Q holds the logic matrix q
    requires matrix: MatIs(Q);
    // (H1), with q = Ut D U and U orthogonal
    requires spectral: SpectralQ;
    // (H2) on the eigenvalues
    requires spectrum: \forall integer l; 0 <= l < d ==> m <= eig(l) <= L;
    // xopt is the optimal solution: q xopt + p = 0
    requires optimal: \forall integer l; 0 <= l < d ==>
                         RowDot(xopt,l,d) + p[l] == 0;
    // (H3) in squared form
    requires start: ErrSq(vec_of(x),d) <= R0 * R0;
    assigns x[0 .. d - 1], g[0 .. d - 1];
    // final error at most TAU, in squared form
    ensures converged: ErrSq(vec_of(x),d) <= TAU * TAU;
 */
void gd_Q(double *Q, double *p, double *x, double *g) {
  int i, j, k; double s;
  /*@ loop invariant range: 0 <= k <= N;
      // every eigen-coordinate of the error is within Rhat(k), rounding errors included
      loop invariant decay_float: \forall integer l; 0 <= l < d ==>
          \abs(EigErr(vec_of(x),l,d)) <= Rhat(k);
      loop assigns k, i, j, s, x[0 .. d - 1], g[0 .. d - 1];
      loop variant N - k;
   */
  for (k = 0; k < N; k++) { // iteration k
    old: ;
    /*@ loop invariant range: 0 <= i <= d;
        loop invariant gradient: \forall integer l; 0 <= l < i ==>
            g[l] == RowDot(vec_of{old}(x),l,d) - RowDot(xopt,l,d);
        loop assigns i, j, s, g[0 .. d - 1];
        loop variant d - i;
     */
    for (i = 0; i < d; i++) { // g <- Q x + p
      s = p[i];
      /*@ loop invariant range: 0 <= j <= d;
          loop invariant accumulator: s == RowDot(vec_of{old}(x),i,j) + p[i];
          loop assigns j, s;
          loop variant d - j;
       */
      for (j = 0; j < d; j++) {
        //@ assert unchangedQ: Q[i*d + j] == q(i,j);
        //@ assert unchangedx: x[j] == vget(vec_of{old}(x),j);
        s = s + Q[i*d + j] * x[j];
      }
      g[i] = s;
    }
    /*@ loop invariant range: 0 <= i <= d;
        loop invariant done: \forall integer l; 0 <= l < i ==> x[l] == \at(x[l], old) - ALPHA * g[l];
        loop invariant todo: \forall integer l; i <= l < d ==> x[l] == \at(x[l], old);
        loop assigns i, x[0 .. d - 1];
        loop variant d - i;
     */
    for (i = 0; i < d; i++) // x <- x - ALPHA g
      x[i] = x[i] - ALPHA * g[i];

    /* grad_diag: the gradient in the eigenbasis is diagonal, U g = D z^k */
    //@ assert grad_eig: \forall integer l; 0 <= l < d ==> EigGrad(vec_of(g),l,d) == eig(l) * EigErr(vec_of{old}(x),l,d);
    /* eigerr_linear: the update in the eigenbasis, z^{k+1} = z^k - ALPHA U g */
    //@ assert update_eig: \forall integer l; 0 <= l < d ==> EigErr(vec_of(x),l,d) == EigErr(vec_of{old}(x),l,d) - ALPHA * EigGrad(vec_of(g),l,d);
    /* hence z^{k+1} = (I - ALPHA D) z^k */
    //@ assert coord_step: \forall integer l; 0 <= l < d ==> EigErr(vec_of(x),l,d) == (1.0 - ALPHA * eig(l)) * EigErr(vec_of{old}(x),l,d);
    /* coord_step_bound: |z^{k+1}_l| <= RHO |z^k_l| */
    //@ assert coord_shrink: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= RHO * \abs(EigErr(vec_of{old}(x),l,d));
    /* Rhat_step: the exact update lies DELTA inside the bound of the next iteration */
    //@ assert decay_next_float: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= Rhat(1+k) - DELTA;
  }

  /* N_sufficient_float: every eigen-coordinate is within the per-coordinate budget TAU/sqrt(d) */
  /*@ assert final_coord: \forall integer l; 0 <= l < d ==>
        \abs(EigErr(vec_of(x),l,d)) <= TAU/\sqrt(d); */

  // elementwise to Euclidean: the squared eigen-coordinates are summed once
  /*@ ghost
      int tg = 0;
      /@ loop invariant range: 0 <= tg <= d;
         loop invariant agg_coord: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= TAU/\sqrt(d);
         loop invariant agg_sum: EigErrSq(vec_of(x),tg) <= tg * ((TAU/\sqrt(d)) * (TAU/\sqrt(d)));
         loop assigns tg;
         loop variant d - tg;
      @/
      for (; tg < d; tg++) {
        /@ assert agg_sq_coord: EigErr(vec_of(x),tg,d) * EigErr(vec_of(x),tg,d) <= (TAU/\sqrt(d)) * (TAU/\sqrt(d)); @/
        /@ assert agg_unfold: EigErrSq(vec_of(x),1+tg) == EigErrSq(vec_of(x),tg) + EigErr(vec_of(x),tg,d) * EigErr(vec_of(x),tg,d); @/
      }
      /@ assert tg_is_d: tg == d; @/
      /@ assert agg_exit: EigErrSq(vec_of(x),d) <= d * ((TAU/\sqrt(d)) * (TAU/\sqrt(d))); @/
  */
  //@ assert eig_total: EigErrSq(vec_of(x),d) <= TAU * TAU;
  // isometry: back to the Euclidean norm
  //@ assert err_total: ErrSq(vec_of(x),d) == EigErrSq(vec_of(x),d);
}

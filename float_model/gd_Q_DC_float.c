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

#include "gd_logic_DC_float.h"

/*@ requires \valid_read(Q + (0 .. d*d - 1)) && \valid_read(p + (0 .. d - 1));
    requires \valid(x + (0 .. d - 1)) && \valid(g + (0 .. d - 1));
    requires \separated(Q + (0 .. d*d - 1), p + (0 .. d - 1),
                        x + (0 .. d - 1), g + (0 .. d - 1));
    // the array Q holds the logic matrix q
    requires matrix: MatIs(Q);
    // (H1)
    requires symmetric: SymmetricQ;
    // (H2), read on the error v - xopt
    requires bounds: BoundsQ;
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
      // F <= Rhat(k) <= R0
      loop invariant Rhat_range: F <= Rhat(k) <= R0;
      // the error is within Rhat(k), rounding errors included (squared form)
      loop invariant decay_float: ErrSq(vec_of(x),d) <= Rhat(k) * Rhat(k);
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

    /* the update read on logic vectors, then the lemma contraction */
    //@ assert step: \forall integer l; 0 <= l < d ==> vget(vec_of(x),l) == vget(vec_of{old}(x),l) - ALPHA * (RowDot(vec_of{old}(x),l,d) - RowDot(xopt,l,d));
    //@ assert contract: ErrSq(vec_of(x),d) <= RHO * RHO * ErrSq(vec_of{old}(x),d);
    /* Rhat_step: the exact update lies DELTA inside the bound of the next iteration */
    //@ assert decay_next_float: ErrSq(vec_of(x),d) <= (Rhat(1+k) - DELTA) * (Rhat(1+k) - DELTA);
  }
}

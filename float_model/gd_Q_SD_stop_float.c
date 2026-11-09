/* Problem constants (the only part the user edits) */
#define d      3
#define ALPHA  0.027398
#define N      8
#define EPS    3.09e-06
/* annotations only */
#define m      27.58
#define L      45.417
#define RHO    0.2444
#define R0     0.03464
#define TAU    1e-06
/* rounding, from a static analysis (Sec. 6.2 and 6.3) */
#define DELTA  7.4e-13
#define ETA    7.4e-13

#include "gd_logic_SD_stop_float.h"

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
  int i, j, k; double s, dx, s2;
  k = 0; s2 = EPS*EPS + 1.0; // above EPS^2, so at least one iteration runs
  /*@ loop invariant range: 0 <= k <= N;
      // every eigen-coordinate of the error is within Rhat(k), rounding errors included
      loop invariant decay_float: \forall integer l; 0 <= l < d ==>
          \abs(EigErr(vec_of(x),l,d)) <= Rhat(k);
      // before the first iteration, the test passes
      loop invariant first: k == 0 ==> EPS * EPS < s2;
      // after an iteration whose computed step satisfies s2 <= EPS^2, the error is at most
      // (RHO (EPS + ETA) + ALPHA m DELTA) / (ALPHA m), rounding errors included (squared form)
      loop invariant stop_float: 0 < k ==> s2 <= EPS * EPS ==>
          (ALPHA * m) * (ALPHA * m) * ErrSq(vec_of(x),d)
          <= (RHO * (EPS + ETA) + ALPHA * m * DELTA) * (RHO * (EPS + ETA) + ALPHA * m * DELTA);
      loop assigns k, i, j, s, dx, s2, x[0 .. d - 1], g[0 .. d - 1];
      loop variant N - k;
   */
  while (k < N && s2 > EPS*EPS) { // iteration k
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
    grad: ;
    s2 = 0.0;
    /*@ loop invariant range: 0 <= i <= d;
        loop invariant done: \forall integer l; 0 <= l < i ==> x[l] == \at(x[l], old) - ALPHA * g[l];
        loop invariant todo: \forall integer l; i <= l < d ==> x[l] == \at(x[l], old);
        loop invariant kept: \forall integer l; 0 <= l < d ==> g[l] == \at(g[l], grad);
        // the squared step over the first i coordinates
        loop invariant step_norm: s2 == (ALPHA * ALPHA) * GradSq(vec_of{grad}(g),i);
        loop assigns i, dx, s2, x[0 .. d - 1];
        loop variant d - i;
     */
    for (i = 0; i < d; i++) { // x <- x - ALPHA g
      //@ assert unchangedg: g[i] == vget(vec_of{grad}(g),i);
      dx = ALPHA * g[i];
      x[i] = x[i] - dx;
      s2 = s2 + dx * dx; // squared step
    }

    /* grad_diag: the gradient in the eigenbasis is diagonal, U g = D z^k */
    //@ assert grad_eig: \forall integer l; 0 <= l < d ==> EigGrad(vec_of{grad}(g),l,d) == eig(l) * EigErr(vec_of{old}(x),l,d);
    /* eigerr_linear: the update in the eigenbasis, z^{k+1} = z^k - ALPHA U g */
    //@ assert update_eig: \forall integer l; 0 <= l < d ==> EigErr(vec_of(x),l,d) == EigErr(vec_of{old}(x),l,d) - ALPHA * EigGrad(vec_of{grad}(g),l,d);
    /* hence z^{k+1} = (I - ALPHA D) z^k */
    //@ assert coord_step: \forall integer l; 0 <= l < d ==> EigErr(vec_of(x),l,d) == (1.0 - ALPHA * eig(l)) * EigErr(vec_of{old}(x),l,d);
    /* coord_step_bound: |z^{k+1}_l| <= RHO |z^k_l| */
    //@ assert coord_shrink: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= RHO * \abs(EigErr(vec_of{old}(x),l,d));
    /* Rhat_step: the exact update lies DELTA inside the bound of the next iteration */
    //@ assert decay_next_float: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= Rhat(1+k) - DELTA;

    /* the stopping certificate, coordinate by coordinate. coord_grad_bound: since eig(l) >= m,
       m |z^k_l| <= |(U g)_l|, and with coord_shrink, m |z^{k+1}_l| <= RHO |(U g)_l| */
    //@ assert coord_grad_eig: \forall integer l; 0 <= l < d ==> m * \abs(EigErr(vec_of{old}(x),l,d)) <= \abs(eig(l) * EigErr(vec_of{old}(x),l,d));
    //@ assert coord_grad: \forall integer l; 0 <= l < d ==> m * \abs(EigErr(vec_of{old}(x),l,d)) <= \abs(EigGrad(vec_of{grad}(g),l,d));
    //@ assert coord_stop: \forall integer l; 0 <= l < d ==> m * \abs(EigErr(vec_of(x),l,d)) <= RHO * \abs(EigGrad(vec_of{grad}(g),l,d));
    /* sq_from_scaled_abs: the same bound, squared */
    //@ assert coord_stop_sq: \forall integer l; 0 <= l < d ==> (m * m) * (EigErr(vec_of(x),l,d) * EigErr(vec_of(x),l,d)) <= (RHO * RHO) * (EigGrad(vec_of{grad}(g),l,d) * EigGrad(vec_of{grad}(g),l,d));

    // elementwise to Euclidean: the squared coordinates are summed once
    /*@ ghost
        int ts = 0;
        /@ loop invariant range: 0 <= ts <= d;
           loop invariant stop_sum: (m * m) * EigErrSq(vec_of(x),ts) <= (RHO * RHO) * EigGradSq(vec_of{grad}(g),ts);
           loop assigns ts;
           loop variant d - ts;
        @/
        for (; ts < d; ts++) {
          /@ assert stop_unfold_err: EigErrSq(vec_of(x),1+ts) == EigErrSq(vec_of(x),ts) + EigErr(vec_of(x),ts,d) * EigErr(vec_of(x),ts,d); @/
          /@ assert stop_unfold_grad: EigGradSq(vec_of{grad}(g),1+ts) == EigGradSq(vec_of{grad}(g),ts) + EigGrad(vec_of{grad}(g),ts,d) * EigGrad(vec_of{grad}(g),ts,d); @/
        }
        /@ assert ts_is_d: ts == d; @/
        /@ assert stop_eig: (m * m) * EigErrSq(vec_of(x),d) <= (RHO * RHO) * EigGradSq(vec_of{grad}(g),d); @/
    */

    // isometry and isometry_grad: back to the Euclidean norms
    //@ assert stop_iso_err: ErrSq(vec_of(x),d) == EigErrSq(vec_of(x),d);
    //@ assert stop_iso_grad: GradSq(vec_of{grad}(g),d) == EigGradSq(vec_of{grad}(g),d);
    //@ assert stop_step: s2 == (ALPHA * ALPHA) * GradSq(vec_of{grad}(g),d);
    //@ assert stop_next: (ALPHA * m) * (ALPHA * m) * ErrSq(vec_of(x),d) <= (RHO * RHO) * s2;
    /* the exact iteration meets the bound of stop_float with the margins: a computed step
       s2 <= EPS^2 means an exact step s2 <= (EPS + ETA)^2, and the update adds at most DELTA */
    //@ assert stop_next_float: s2 <= (EPS + ETA) * (EPS + ETA) ==> (ALPHA * m) * (ALPHA * m) * ErrSq(vec_of(x),d) <= (RHO * (EPS + ETA)) * (RHO * (EPS + ETA));
    k++;
  }

  /* the two exits: the cap k == N, where N_sufficient_float bounds every eigen-coordinate by
     TAU/sqrt(d), or the test s2 <= EPS^2 after at least one iteration, where stop_float and
     EPS_sufficient_float give the postcondition */
  /*@ ghost
      if (k == N) {
        int tg = 0;
        /@ assert final_coord: \forall integer l; 0 <= l < d ==> \abs(EigErr(vec_of(x),l,d)) <= TAU/\sqrt(d); @/
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
        /@ assert eig_total: EigErrSq(vec_of(x),d) <= TAU * TAU; @/
        /@ assert err_total: ErrSq(vec_of(x),d) == EigErrSq(vec_of(x),d); @/
      }
      else {
        /@ assert early: 0 < k && s2 <= EPS * EPS; @/
      }
  */
}

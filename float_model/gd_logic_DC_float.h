/* gd_logic_DC_float.h (include it after the problem constants are defined)
 frama-c -wp -wp-rte -wp-model real -local-tactic -local-tactic-rocq-import Reals,Psatz -wp-timeout 120 -wp-prover alt-ergo,cvc5,z3,coq gd_Q_DC_float.c -then -report
*/

/* why3's real.PowerInt */
//@ import \wp::why3: real::PowerInt;

/* Rounding errors: DELTA bounds the rounding error of one iteration, F = DELTA/(1-RHO),
   and Rhat(k) = RHO^k R0 + F (1 - RHO^k) bounds the error after k iterations */
/*@ logic real F = DELTA / (1.0 - RHO);
    logic real Rhat(integer k) = PowerInt::power(RHO,k) * R0 + F * (1.0 - PowerInt::power(RHO,k));
 */

/* Conditions on the constants, proved once for the chosen values */
/*@ axiomatic Conditions {
      // (C1) 0 < ALPHA < 2/L
      lemma ALPHA_admissible: 0 < ALPHA < 2.0 / L;
      // (C2) max(|1 - ALPHA m|, |1 - ALPHA L|) <= RHO, with 0 < RHO < 1
      lemma RHO_admissible: \abs(1.0 - ALPHA * m) <= RHO && \abs(1.0 - ALPHA * L) <= RHO && 0 < RHO < 1;
      // 0 <= DELTA and F <= R0, so that Rhat(k) never exceeds R0
      lemma DELTA_admissible: 0 <= DELTA && F <= R0;
      // the recursion Rhat(0) = R0, Rhat(k+1) = RHO Rhat(k) + DELTA
      lemma Rhat_0: Rhat(0) == R0;
      lemma Rhat_step: \forall integer k; 0 <= k ==> Rhat(1+k) == RHO * Rhat(k) + DELTA;
      // (C3_F) Rhat(N) <= TAU, in squared form like N_sufficient (Rhat(N) >= F >= 0)
      lemma N_sufficient_float: Rhat(N) * Rhat(N) <= TAU * TAU;
    }
*/

// Vectors: vec is R^d, read through vget (its entries are only specified on [0, d)).
// vlin(a,u,b,v) = a u + b v, defined entrywise by vlin_get. It is used only by the Rocq proof
// of contraction, to apply BoundsQ to the errors RHO (y - xopt) +/- (x - xopt) (polarization).
/*@ axiomatic Vec {
      type vec;
      logic real vget(vec v, integer i);
      logic vec vlin(real a, vec u, real b, vec v);
      axiom vlin_get: \forall real a, b, integer i, vec u, v; 0 <= i < d ==>
        vget(vlin(a,u,b,v),i) == a * vget(u,i) + b * vget(v,i);
    }
 */

// Problem data (uninterpreted)
/*@ axiomatic Problem {
      // entry (i,j) of the matrix Q
      logic real q(integer i, integer j);
      // the optimal solution xopt (a logic vector)
      logic vec xopt;
      // q is symmetric
      predicate SymmetricQ = \forall integer i, j; 0 <= i < d && 0 <= j < d ==> q(i,j) == q(j,i);
    }
 */

/* The recursive sums:
     RowDot(v,i,t): first t terms of row i of q dotted with v; RowDot(v,i,d) = Q(i,:) * v.
     ErrSq(v,t): first t terms of ||v - xopt||_2^2.
     ErrQ(v,t): first t terms of (v - xopt)^T Q (v - xopt).
*/
/*@ axiomatic Sums {
      logic real RowDot(vec v, integer i, integer t);
      axiom RowDot_base: \forall vec v, integer i; RowDot(v,i,0) == 0.0;
      axiom RowDot_step: \forall vec v, integer i, t; 0 <= t < d ==>
        RowDot(v,i,1+t) == RowDot(v,i,t) + q(i,t) * vget(v,t);

      logic real ErrSq(vec v, integer t);
      axiom ErrSq_base: \forall vec v; ErrSq(v,0) == 0.0;
      axiom ErrSq_step: \forall vec v, integer t; 0 <= t < d ==>
        ErrSq(v,1+t) == ErrSq(v,t) + (vget(v,t) - vget(xopt,t)) * (vget(v,t) - vget(xopt,t));

      logic real ErrQ(vec v, integer t);
      axiom ErrQ_base: \forall vec v; ErrQ(v,0) == 0.0;
      axiom ErrQ_step: \forall vec v, integer t; 0 <= t < d ==>
        ErrQ(v,1+t) == ErrQ(v,t) + (vget(v,t) - vget(xopt,t)) * (RowDot(v,t,d) - RowDot(xopt,t,d));
    }
 */

/*@ // (H2): m I <= q <= L I, read on the error v - xopt
    predicate BoundsQ = \forall vec v; m * ErrSq(v,d) <= ErrQ(v,d) <= L * ErrSq(v,d);
    // every gradient step of size a shrinks the squared error r^2-fold
    predicate Contracts(real a, real r) = \forall vec vx, vy;
      (\forall integer c; 0 <= c < d ==> vget(vx,c) == vget(vy,c) - a * (RowDot(vy,c,d) - RowDot(xopt,c,d))) ==>
      ErrSq(vx,d) <= r * r * ErrSq(vy,d);
 */

/* Glue: C objects to ACSL logic */
/* vec_of{K}(a) is the vector held by a[0..d-1] in state K.
   vec_of_get is the only axiom that mentions memory.
   The read-only array Q is linked to q entrywise by MatIs. */
/*@ axiomatic Glue {
      logic vec vec_of{K}(double *a) reads a[0 .. d - 1];
      axiom vec_of_get{K}: \forall double *a, integer i; 0 <= i < d ==> vget(vec_of{K}(a), i) == \at(a[i],K);
    }
    predicate MatIs{K}(double *aq) = \forall integer i, j;
      0 <= i < d && 0 <= j < d ==> \at(aq[i*d + j],K) == q(i,j);
 */

/* the lemma (proved in Rocq below) */
/*@ axiomatic Lemmas {
      // one gradient step of size ALPHA contracts the error by RHO
      lemma contraction: SymmetricQ ==> BoundsQ ==> Contracts(ALPHA, RHO);
    }
 */


/* Rocq scripts */

/*@ rocq_strategy Csum:
      "(* finite sums over nat, and the algebra needed below *)",
      "pose (csum := fix rec (f : nat -> R) (n : nat) {struct n} : R := match n with O => 0%R | S k => (rec f k + f k)%R end);",
      "assert (csumS : forall f n, csum f (S n) = (csum f n + f n)%R) by reflexivity;",
      "assert (csum_ext : forall f g n, (forall k, (k < n)%nat -> f k = g k) -> csum f n = csum g n) by (intros f g n; induction n as [|k IH]; intros Hfg; [ reflexivity | rewrite !csumS; rewrite IH; [ rewrite (Hfg k); [ reflexivity | lia ] | intros q Hq; apply Hfg; lia ] ]);",
      "assert (csum_zero : forall f n, (forall k, (k < n)%nat -> f k = 0%R) -> csum f n = 0%R) by (intros f n; induction n as [|k IH]; intros Hf; [ reflexivity | rewrite csumS, IH, (Hf k); [ lra | lia | intros; apply Hf; lia ] ]);",
      "assert (csum_mull : forall c f n, csum (fun k => (c * f k)%R) n = (c * csum f n)%R) by (intros c f n; induction n as [|k IH]; [ simpl; lra | rewrite !csumS, IH; lra ]);",
      "assert (csum_mulr : forall c f n, csum (fun k => (f k * c)%R) n = (csum f n * c)%R) by (intros c f n; induction n as [|k IH]; [ simpl; lra | rewrite !csumS, IH; lra ]);",
      "assert (csum_add : forall f g n, csum (fun k => (f k + g k)%R) n = (csum f n + csum g n)%R) by (intros f g n; induction n as [|k IH]; [ simpl; lra | rewrite !csumS, IH; lra ]);",
      "assert (csum_swap : forall (F : nat -> nat -> R) n p, csum (fun a => csum (F a) p) n = csum (fun b => csum (fun a => F a b) n) p) by (intros F n; induction n as [|q IH]; intros p; [ simpl; rewrite csum_zero; [ reflexivity | intros; reflexivity ] | rewrite csumS, IH, <- csum_add; apply csum_ext; intros k Hk; rewrite csumS; reflexivity ]);",
      "assert (csum_delta : forall f n s, (s < n)%nat -> (forall k, (k < n)%nat -> k <> s -> f k = 0%R) -> csum f n = f s) by (intros f n; induction n as [|q IH]; intros s Hs Hf; [ lia | rewrite csumS; assert (Hc : s = q \/ (s < q)%nat) by lia; destruct Hc as [-> | Hsq]; [ rewrite csum_zero; [ lra | intros k Hk; apply Hf; lia ] | rewrite (IH s Hsq), (Hf q); [ lra | lia | lia | intros k Hk Hks; apply Hf; lia ] ] ]);",
      "assert (csum_pull : forall (x y : R) (G : nat -> R) n, (x * (csum G n * y))%R = csum (fun w => (x * (G w * y))%R) n) by (intros x y G n; induction n as [|k IH]; [ simpl; ring | rewrite !csumS, <- IH; ring ]);" ;
*/

/*@ rocq_proof contraction:
      "intros H1 H2;",
      "assert (HSym : P_SymmetricQ) by assumption; assert (HB : P_BoundsQ) by assumption;",
      "unfold P_SymmetricQ in HSym; unfold P_BoundsQ in HB; cbv zeta in HSym, HB;",
      "lazymatch goal with |- P_Contracts ?ALP ?RHO0 =>",
      "unfold P_Contracts; intros V1 V2 HGd; cbv zeta;",
      "lazymatch goal with |- (L_ErrSq ?VX ?DZ <= ?RHS)%R =>",
      "lazymatch RHS with context [ L_ErrSq ?VY DZ ] =>",
      \by(Csum),
      "(* the defining axioms, oriented atom = definition whichever way Qed printed them *)",
      "assert (Hvl : forall (a b : R) (u v : A_vec) (i : Z), (0 <= i)%Z -> (i < DZ)%Z -> L_vget (L_vlin a u b v) i = (a * L_vget u i + b * L_vget v i)%R) by (intros a b u v i Hi1 Hi2; pose proof Q_vlin_get as Hq; cbv zeta in Hq; first [ rewrite Hq by lia; ring | rewrite <- Hq by lia; ring ]);",
      "assert (Rbase : forall (v : A_vec) (i : Z), L_RowDot v i 0%Z = 0%R) by (intros v i; pose proof Q_RowDot_base as Hq; first [ apply Hq | symmetry; apply Hq ]);",
      "assert (Rstep : forall (v : A_vec) (i t : Z), (0 <= t)%Z -> (t < DZ)%Z -> L_RowDot v i (1 + t)%Z = (L_RowDot v i t + L_q i t * L_vget v t)%R) by (intros v i t Ht1 Ht2; pose proof Q_RowDot_step as Hq; cbv zeta in Hq; first [ rewrite Hq by lia; ring | rewrite <- Hq by lia; ring ]);",
      "assert (Ebase : forall (v : A_vec), L_ErrSq v 0%Z = 0%R) by (intros v; pose proof Q_ErrSq_base as Hq; first [ apply Hq | symmetry; apply Hq ]);",
      "assert (Estep : forall (v : A_vec) (t : Z), (0 <= t)%Z -> (t < DZ)%Z -> L_ErrSq v (1 + t)%Z = (L_ErrSq v t + (L_vget v t - L_vget L_xopt t) * (L_vget v t - L_vget L_xopt t))%R) by (intros v t Ht1 Ht2; pose proof Q_ErrSq_step as Hq; cbv zeta in Hq; first [ rewrite Hq by lia; ring | rewrite <- Hq by lia; ring ]);",
      "assert (Qbase : forall (v : A_vec), L_ErrQ v 0%Z = 0%R) by (intros v; pose proof Q_ErrQ_base as Hq; first [ apply Hq | symmetry; apply Hq ]);",
      "assert (Qstep : forall (v : A_vec) (t : Z), (0 <= t)%Z -> (t < DZ)%Z -> L_ErrQ v (1 + t)%Z = (L_ErrQ v t + (L_vget v t - L_vget L_xopt t) * (L_RowDot v t DZ - L_RowDot L_xopt t DZ))%R) by (intros v t Ht1 Ht2; pose proof Q_ErrQ_step as Hq; cbv zeta in Hq; first [ rewrite Hq by lia; ring | rewrite <- Hq by lia; ring ]);",
      "(* RowDot, ErrSq, ErrQ as csum *)",
      "assert (Brow : forall (w : A_vec) (p0 : Z) (n0 : nat), (n0 <= Z.to_nat DZ)%nat -> L_RowDot w p0 (Z.of_nat n0) = csum (fun b0 => (L_q p0 (Z.of_nat b0) * L_vget w (Z.of_nat b0))%R) n0) by (intros w p0 n0; induction n0 as [|k0 IH0]; intros Hn0; [ apply Rbase | rewrite csumS, <- IH0 by lia; replace (Z.of_nat (S k0)) with (1 + Z.of_nat k0)%Z by lia; rewrite Rstep by lia; cbv beta; ring ]);",
      "assert (Berr : forall (w : A_vec) (n0 : nat), (n0 <= Z.to_nat DZ)%nat -> L_ErrSq w (Z.of_nat n0) = csum (fun c0 => ((L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)) * (L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)))%R) n0) by (intros w n0; induction n0 as [|k0 IH0]; intros Hn0; [ apply Ebase | rewrite csumS, <- IH0 by lia; replace (Z.of_nat (S k0)) with (1 + Z.of_nat k0)%Z by lia; rewrite Estep by lia; cbv beta; ring ]);",
      "assert (Bq : forall (w : A_vec) (n0 : nat), (n0 <= Z.to_nat DZ)%nat -> L_ErrQ w (Z.of_nat n0) = csum (fun c0 => ((L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)) * (L_RowDot w (Z.of_nat c0) DZ - L_RowDot L_xopt (Z.of_nat c0) DZ))%R) n0) by (intros w n0; induction n0 as [|k0 IH0]; intros Hn0; [ apply Qbase | rewrite csumS, <- IH0 by lia; replace (Z.of_nat (S k0)) with (1 + Z.of_nat k0)%Z by lia; rewrite Qstep by lia; cbv beta; ring ]);",
      "assert (Browf : forall (w : A_vec) (p0 : Z), L_RowDot w p0 DZ = csum (fun b0 => (L_q p0 (Z.of_nat b0) * L_vget w (Z.of_nat b0))%R) (Z.to_nat DZ)) by (intros w p0; rewrite <- (Brow w p0 (Z.to_nat DZ)) by lia; rewrite Z2Nat.id by lia; reflexivity);",
      "assert (Berrf : forall (w : A_vec), L_ErrSq w DZ = csum (fun c0 => ((L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)) * (L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)))%R) (Z.to_nat DZ)) by (intros w; rewrite <- (Berr w (Z.to_nat DZ)) by lia; rewrite Z2Nat.id by lia; reflexivity);",
      "assert (Bqf : forall (w : A_vec), L_ErrQ w DZ = csum (fun c0 => ((L_vget w (Z.of_nat c0) - L_vget L_xopt (Z.of_nat c0)) * (L_RowDot w (Z.of_nat c0) DZ - L_RowDot L_xopt (Z.of_nat c0) DZ))%R) (Z.to_nat DZ)) by (intros w; rewrite <- (Bq w (Z.to_nat DZ)) by lia; rewrite Z2Nat.id by lia; reflexivity);",
      "(* errors of the two iterates, their images by q, and W s with error RHO ey + s ex *)",
      "pose (ey := fun k : nat => (L_vget VY (Z.of_nat k) - L_vget L_xopt (Z.of_nat k))%R);",
      "pose (ex := fun k : nat => (L_vget VX (Z.of_nat k) - L_vget L_xopt (Z.of_nat k))%R);",
      "pose (qy := fun k : nat => (L_RowDot VY (Z.of_nat k) DZ - L_RowDot L_xopt (Z.of_nat k) DZ)%R);",
      "pose (qx := fun k : nat => (L_RowDot VX (Z.of_nat k) DZ - L_RowDot L_xopt (Z.of_nat k) DZ)%R);",
      "pose (W := fun s0 : R => L_vlin RHO0 VY 1%R (L_vlin s0 VX (1 - RHO0 - s0)%R L_xopt));",
      "assert (Hw : forall (s0 : R) (k0 : nat), (k0 < Z.to_nat DZ)%nat -> (L_vget (W s0) (Z.of_nat k0) - L_vget L_xopt (Z.of_nat k0) = RHO0 * ey k0 + s0 * ex k0)%R) by (intros s0 k0 Hk0; unfold W, ey, ex; cbv beta; rewrite !Hvl by lia; ring);",
      "assert (Hwq : forall (s0 : R) (k0 : nat), (L_RowDot (W s0) (Z.of_nat k0) DZ - L_RowDot L_xopt (Z.of_nat k0) DZ = RHO0 * qy k0 + s0 * qx k0)%R) by (intros s0 k0; unfold qy, qx; cbv beta; rewrite !Browf; transitivity (csum (fun b0 => (RHO0 * (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget VY (Z.of_nat b0)) + s0 * (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget VX (Z.of_nat b0)) + (1 - RHO0 - s0) * (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget L_xopt (Z.of_nat b0)))%R) (Z.to_nat DZ) - csum (fun b0 => (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget L_xopt (Z.of_nat b0))%R) (Z.to_nat DZ))%R; [ f_equal; apply csum_ext; intros b0 Hb0; unfold W; cbv beta; rewrite !Hvl by lia; ring | rewrite !csum_add, !csum_mull; ring ]);",
      "(* the squared error and the q-energy of W s *)",
      "assert (HN : forall s0 : R, (L_ErrSq (W s0) DZ = RHO0 * RHO0 * csum (fun k => (ey k * ey k)%R) (Z.to_nat DZ) + 2 * RHO0 * s0 * csum (fun k => (ey k * ex k)%R) (Z.to_nat DZ) + s0 * s0 * csum (fun k => (ex k * ex k)%R) (Z.to_nat DZ))%R) by (intros s0; rewrite Berrf; transitivity (csum (fun k => (RHO0 * RHO0 * (ey k * ey k) + 2 * RHO0 * s0 * (ey k * ex k) + s0 * s0 * (ex k * ex k))%R) (Z.to_nat DZ)); [ apply csum_ext; intros k0 Hk0; cbv beta; rewrite (Hw s0 k0 Hk0); ring | rewrite !csum_add, !csum_mull; ring ]);",
      "assert (HQ : forall s0 : R, (L_ErrQ (W s0) DZ = RHO0 * RHO0 * csum (fun k => (ey k * qy k)%R) (Z.to_nat DZ) + RHO0 * s0 * (csum (fun k => (ey k * qx k)%R) (Z.to_nat DZ) + csum (fun k => (ex k * qy k)%R) (Z.to_nat DZ)) + s0 * s0 * csum (fun k => (ex k * qx k)%R) (Z.to_nat DZ))%R) by (intros s0; rewrite Bqf; transitivity (csum (fun k => (RHO0 * RHO0 * (ey k * qy k) + RHO0 * s0 * (ey k * qx k) + RHO0 * s0 * (ex k * qy k) + s0 * s0 * (ex k * qx k))%R) (Z.to_nat DZ)); [ apply csum_ext; intros k0 Hk0; cbv beta; rewrite (Hw s0 k0 Hk0), (Hwq s0 k0); ring | rewrite !csum_add, !csum_mull; ring ]);",
      "(* q symmetric: ey . q ex = ex . q ey *)",
      "assert (Hqy : forall k0 : nat, qy k0 = csum (fun b0 => (L_q (Z.of_nat k0) (Z.of_nat b0) * ey b0)%R) (Z.to_nat DZ)) by (intros k0; unfold qy; cbv beta; rewrite !Browf; transitivity (csum (fun b0 => (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget VY (Z.of_nat b0) + (-1) * (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget L_xopt (Z.of_nat b0)))%R) (Z.to_nat DZ)); [ rewrite csum_add, csum_mull; ring | apply csum_ext; intros b0 Hb0; unfold ey; cbv beta; ring ]);",
      "assert (Hqx : forall k0 : nat, qx k0 = csum (fun b0 => (L_q (Z.of_nat k0) (Z.of_nat b0) * ex b0)%R) (Z.to_nat DZ)) by (intros k0; unfold qx; cbv beta; rewrite !Browf; transitivity (csum (fun b0 => (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget VX (Z.of_nat b0) + (-1) * (L_q (Z.of_nat k0) (Z.of_nat b0) * L_vget L_xopt (Z.of_nat b0)))%R) (Z.to_nat DZ)); [ rewrite csum_add, csum_mull; ring | apply csum_ext; intros b0 Hb0; unfold ex; cbv beta; ring ]);",
      "assert (Hsym : csum (fun k => (ey k * qx k)%R) (Z.to_nat DZ) = csum (fun k => (ex k * qy k)%R) (Z.to_nat DZ)) by (transitivity (csum (fun k => csum (fun b0 => (ey k * (L_q (Z.of_nat k) (Z.of_nat b0) * ex b0))%R) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros k0 Hk0; cbv beta; rewrite (Hqx k0); rewrite <- csum_mull; reflexivity | rewrite csum_swap; apply csum_ext; intros b0 Hb0; cbv beta; rewrite (Hqy b0); rewrite <- csum_mull; apply csum_ext; intros k0 Hk0; cbv beta; rewrite (HSym (Z.of_nat k0) (Z.of_nat b0)) by lia; ring ]);",
      "(* the step ex = ey - ALPHA qy gives |ex|^2 = ey . ex - ALPHA ex . qy *)",
      "assert (Hst : csum (fun k => (ex k * ex k)%R) (Z.to_nat DZ) = (csum (fun k => (ey k * ex k)%R) (Z.to_nat DZ) + (- ALP) * csum (fun k => (ex k * qy k)%R) (Z.to_nat DZ))%R) by (rewrite <- csum_mull, <- csum_add; apply csum_ext; intros k0 Hk0; cbv beta; assert (Ek : (ex k0 = ey k0 - ALP * qy k0)%R) by (unfold ex, ey, qy; cbv beta; pose proof (HGd (Z.of_nat k0)) as E0; cbv zeta in E0; specialize (E0 ltac:(lia) ltac:(lia)); lra); rewrite Ek; ring);",
      "(* sums of squares are nonnegative *)",
      "assert (Hpos : forall s0 : R, (0 <= L_ErrSq (W s0) DZ)%R) by (intros s0; rewrite Berrf; assert (Gp : forall (g0 : nat -> R) (n0 : nat), (forall k, (k < n0)%nat -> (0 <= g0 k)%R) -> (0 <= csum g0 n0)%R) by (intros g0 n0; induction n0 as [|k1 IH1]; intros Hg; [ assert (G0 : csum g0 0%nat = 0%R) by reflexivity; lra | rewrite csumS; assert (G1 : (0 <= g0 k1)%R) by (apply Hg; lia); assert (G2 : (0 <= csum g0 k1)%R) by (apply IH1; intros k2 Hk2; apply Hg; lia); lra ]); apply Gp; intros k0 Hk0; cbv beta; match goal with |- (0 <= ?X * ?X)%R => apply (Rle_0_sqr X) end);",
      "assert (HF : L_ErrSq VX DZ = csum (fun k => (ex k * ex k)%R) (Z.to_nat DZ)) by (rewrite Berrf; apply csum_ext; intros k0 Hk0; reflexivity);",
      "assert (HA : L_ErrSq VY DZ = csum (fun k => (ey k * ey k)%R) (Z.to_nat DZ)) by (rewrite Berrf; apply csum_ext; intros k0 Hk0; reflexivity);",
      "(* polarization: the bounds at W 1 and W (-1); lra also checks max(1 - ALPHA m, ALPHA L - 1) <= RHO *)",
      "destruct (HB (W 1%R)) as [Hb1 Hb2]; destruct (HB (W (-1)%R)) as [Hb3 Hb4];",
      "pose proof (HN 1%R) as HN1; pose proof (HN (-1)%R) as HN2; pose proof (HQ 1%R) as HQ1; pose proof (HQ (-1)%R) as HQ2;",
      "pose proof (Hpos 1%R) as Hp1; pose proof (Hpos (-1)%R) as Hp2;",
      "lra",
      "end end end." ;
*/

/* (C3_F): numeric certificate for the iteration count, after unfolding Rhat and F */
/*@ rocq_proof N_sufficient_float:
      "try unfold L_Rhat; try unfold L_F;",
      "(* prove 0 <= Rhat(N) <= TAU, then square; otherwise evaluate the squared form directly *)",
      "first [ match goal with |- (?A * ?A <= ?C * ?C)%R => assert (HA : (0 <= A <= C)%R) by (simpl; lra); apply Rmult_le_compat; lra end | simpl; lra ]." ;
*/

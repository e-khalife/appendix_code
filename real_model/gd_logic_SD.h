/* gd_logic_SD.h (include it after the problem constants are defined)
   verification command:
 frama-c -wp -wp-rte -wp-model real -local-tactic -local-tactic-rocq-import Reals,Psatz -wp-timeout 120 -wp-prover alt-ergo,cvc5,z3,coq gd_Q_SD.c -then -report
*/

/*@ axiomatic NumericLemmas {
      // one-step contraction of each decoupled scalar recursion
      lemma coord_step_bound: \forall real lam, v; m <= lam <= L ==> \abs((1.0 - ALPHA * lam) * v) <= RHO * \abs(v);
      // a bound on |u| bounds u^2
      lemma sq_from_abs: \forall real u, w; 0 <= w ==> \abs(u) <= w ==> u * u <= w * w;
      // sqrt(d)^2 = d and sqrt(d) > 0
      lemma sqrtd_sq:  \sqrt(d) * \sqrt(d) == d;
      lemma sqrtd_pos: 0 < \sqrt(d);
      // the per-coordinate budget TAU/sqrt(d): nonnegative, and d budgets squared give TAU^2
      lemma budget_nonneg: 0 <= TAU / \sqrt(d);
      lemma budget_exact: d * ((TAU / \sqrt(d)) * (TAU / \sqrt(d))) == TAU * TAU;
    }
*/

/* why3's real.PowerInt */
//@ import \wp::why3: real::PowerInt;

/* Conditions (C1)-(C3) on the constants, proved once for the chosen values */
/*@ axiomatic Conditions {
      // (C1) 0 < ALPHA < 2/L
      lemma ALPHA_admissible: 0 < ALPHA < 2.0 / L;
      // (C2) max(|1 - ALPHA m|, |1 - ALPHA L|) <= RHO, with 0 < RHO < 1
      lemma RHO_admissible: \abs(1.0 - ALPHA * m) <= RHO && \abs(1.0 - ALPHA * L) <= RHO && 0 < RHO < 1;
      // (C3_SD) RHO^N R0 <= TAU / sqrt(d)
      lemma N_sufficient: PowerInt::power(RHO,N) * R0 <= TAU / \sqrt(d);
    }
*/

// Vectors: vec is R^d, read through vget (its entries are only specified on [0, d)).
/*@ axiomatic Vec {
      type vec;
      logic real vget(vec v, integer i);
    }
 */

// Spectral data (uninterpreted)
/*@ axiomatic Spectral {
      // entry (i,j) of the matrix Q
      logic real q(integer i, integer j);
      // entry (i,j) of the orthogonal matrix U (rows = eigenvectors)
      logic real U(integer i, integer j);
      // eigenvalue i
      logic real eig(integer i);
      // the optimal solution xopt (a logic vector)
      logic vec xopt;

      // first t terms of entry (i,j) of Ut D U
      logic real SpecSum(integer i, integer j, integer t);
      axiom SpecSum_base: \forall integer i, j; SpecSum(i,j,0) == 0.0;
      axiom SpecSum_step: \forall integer i, j, t; 0 <= t < d ==>
        SpecSum(i,j,1+t) == SpecSum(i,j,t) + U(t,i) * eig(t) * U(t,j);

      // first t terms of row i dotted with row j
      logic real RowOrth(integer i, integer j, integer t);
      axiom RowOrth_base: \forall integer i, j; RowOrth(i,j,0) == 0.0;
      axiom RowOrth_step: \forall integer i, j, t; 0 <= t < d ==>
        RowOrth(i,j,1+t) == RowOrth(i,j,t) + U(i,t) * U(j,t);

      // first t terms of column i dotted with column j
      logic real ColOrth(integer i, integer j, integer t);
      axiom ColOrth_base: \forall integer i, j; ColOrth(i,j,0) == 0.0;
      axiom ColOrth_step: \forall integer i, j, t; 0 <= t < d ==>
        ColOrth(i,j,1+t) == ColOrth(i,j,t) + U(t,i) * U(t,j);

      // U Ut = I
      predicate RowsOrthonormal = \forall integer i, j; 0 <= i < d && 0 <= j < d ==> RowOrth(i,j,d) == (i == j ? 1.0 : 0.0);
      // Ut U = I
      predicate ColsOrthonormal = \forall integer i, j; 0 <= i < d && 0 <= j < d ==> ColOrth(i,j,d) == (i == j ? 1.0 : 0.0);
      predicate U_orthogonal = RowsOrthonormal && ColsOrthonormal;
      // q = Ut D U (elementwise)
      predicate SpectralEq = \forall integer i, j; 0 <= i < d && 0 <= j < d ==> q(i,j) == SpecSum(i,j,d);
      // q is symmetric
      predicate SymmetricQ = \forall integer i, j; 0 <= i < d && 0 <= j < d ==> q(i,j) == q(j,i);

      // the spectral decomposition hypothesis
      predicate SpectralQ = SymmetricQ && U_orthogonal && SpectralEq;
    }
 */


/* The recursive sums:
     RowDot(v,i,t): first t terms of row i of q dotted with v; RowDot(v,i,d)  = Q(i,:) * v.
     EigErr(v,i,t): first t terms of coordinate i of U (v - xopt); EigErr(v,i,d) = U(i,:) * (v - xopt)
     EigGrad(v,i,t): first t terms of coordinate i of U v; EigGrad(v,i,d) = (U v)_i (named for its use on the gradient g)
     ErrSq(v,t): squared Euclidean error over the first t coordinates; ErrSq(x,d) = ||x-xopt||_2^2.
     EigErrSq(v,t): squared eigenbasis error over the first t coordinates; EigErrSq(x,d) = ||U(x-xopt)||_2^2.
*/
/*@ axiomatic Sums {
      logic real RowDot(vec v, integer i, integer t);
      axiom RowDot_base: \forall vec v, integer i; RowDot(v,i,0) == 0.0;
      axiom RowDot_step: \forall vec v, integer i, t; 0 <= t < d ==>
        RowDot(v,i,1+t) == RowDot(v,i,t) + q(i,t) * vget(v,t);

      logic real EigErr(vec v, integer i, integer t);
      axiom EigErr_base: \forall vec v, integer i; EigErr(v,i,0) == 0.0;
      axiom EigErr_step: \forall vec v, integer i, t; 0 <= t < d ==>
        EigErr(v,i,1+t) == EigErr(v,i,t) + U(i,t) * (vget(v,t) - vget(xopt,t));

      logic real EigGrad(vec v, integer i, integer t);
      axiom EigGrad_base: \forall vec v, integer i; EigGrad(v,i,0) == 0.0;
      axiom EigGrad_step: \forall vec v, integer i, t; 0 <= t < d ==>
        EigGrad(v,i,1+t) == EigGrad(v,i,t) + U(i,t) * vget(v,t);

      logic real ErrSq(vec v, integer t);
      axiom ErrSq_base: \forall vec v; ErrSq(v,0) == 0.0;
      axiom ErrSq_step: \forall vec v, integer t; 0 <= t < d ==>
        ErrSq(v,1+t) == ErrSq(v,t) + (vget(v,t) - vget(xopt,t)) * (vget(v,t) - vget(xopt,t));

      logic real EigErrSq(vec v, integer t);
      axiom EigErrSq_base: \forall vec v; EigErrSq(v,0) == 0.0;
      axiom EigErrSq_step: \forall vec v, integer t; 0 <= t < d ==>
        EigErrSq(v,1+t) == EigErrSq(v,t) + EigErr(v,t,d) * EigErr(v,t,d);
    }
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

/* the lemmas (proved in Rocq below) */
/*@ axiomatic Lemmas {

      // vg = Q v - Q xopt and Q = Ut D U, U Ut = I give U vg = D U (v - xopt)
      lemma grad_diag: \forall vec vg, v, integer i; 0 <= i < d ==> SpectralEq ==> RowsOrthonormal ==>
        (\forall integer c; 0 <= c < d ==> vget(vg,c) == RowDot(v,c,d) - RowDot(xopt,c,d)) ==>
        EigGrad(vg,i,d) == eig(i) * EigErr(v,i,d);

      // vx = vy - ALPHA*vg gives U (vx - xopt) = U (vy - xopt) - ALPHA * U vg
      lemma eigerr_linear: \forall vec vg, vx, vy, integer i; 0 <= i < d ==>
        (\forall integer c; 0 <= c < d ==> vget(vx,c) == vget(vy,c) - ALPHA * vget(vg,c)) ==>
        EigErr(vx,i,d) == EigErr(vy,i,d) - ALPHA * EigGrad(vg,i,d);

      // orthogonal maps preserve norms (needs Ut U = I)
      lemma isometry: \forall vec v; ColsOrthonormal ==> EigErrSq(v,d) == ErrSq(v,d);

      // one square is at most the whole sum of squares
      lemma coord_sq_le_total: \forall vec v, integer i; 0 <= i < d ==> EigErr(v,i,d) * EigErr(v,i,d) <= EigErrSq(v,d);

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

/*@ rocq_proof grad_diag:
      "intros;",
      "match goal with HSQ : P_SpectralEq, HRO : P_RowsOrthonormal, Hgc : forall c : Numbers.BinNums.Z, _ |- _ =>",
      "unfold P_SpectralEq in HSQ; unfold P_RowsOrthonormal in HRO;",
      "first [ match goal with |- (L_EigGrad _ _ _ = _) => idtac end | symmetry ];",
      "match goal with |- (L_EigGrad ?VG ?i ?DZ = (L_eig ?i * L_EigErr ?V ?i ?DZ)%R) =>",
      \by(Csum),
      "(* the sums as csum *)",
      "assert (Beig : forall (p : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_EigErr V p (Z.of_nat n) = csum (fun c => (L_U p (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) n) by (intros p n; induction n as [|k IH]; intros Hn; [ apply Q_EigErr_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_EigErr_step V p (Z.of_nat k)) by lia; ring ]);",
      "assert (Bgrad : forall (n : nat), (n <= Z.to_nat DZ)%nat -> L_EigGrad VG i (Z.of_nat n) = csum (fun s => (L_U i (Z.of_nat s) * L_vget VG (Z.of_nat s))%R) n) by (intros n; induction n as [|k IH]; intros Hn; [ apply Q_EigGrad_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_EigGrad_step VG i (Z.of_nat k)) by lia; ring ]);",
      "assert (Browdot : forall (w : A_vec) (p : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_RowDot w p (Z.of_nat n) = csum (fun c => (L_q p (Z.of_nat c) * L_vget w (Z.of_nat c))%R) n) by (intros w p n; induction n as [|k IH]; intros Hn; [ apply Q_RowDot_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_RowDot_step w p (Z.of_nat k)) by lia; ring ]);",
      "assert (Bspec : forall (b c0 : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_SpecSum b c0 (Z.of_nat n) = csum (fun w => ((L_eig (Z.of_nat w) * L_U (Z.of_nat w) c0) * L_U (Z.of_nat w) b)%R) n) by (intros b c0 n; induction n as [|k IH]; intros Hn; [ apply Q_SpecSum_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_SpecSum_step b c0 (Z.of_nat k)) by lia; ring ]);",
      "assert (Brow : forall (p q : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_RowOrth p q (Z.of_nat n) = csum (fun w => (L_U p (Z.of_nat w) * L_U q (Z.of_nat w))%R) n) by (intros p q n; induction n as [|k IH]; intros Hn; [ apply Q_RowOrth_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_RowOrth_step p q (Z.of_nat k)) by lia; ring ]);",
      "(* row s of Q applied to V - xopt *)",
      "assert (Hgrad : forall s : nat, (s < Z.to_nat DZ)%nat -> (L_RowDot V (Z.of_nat s) DZ + (-1) * L_RowDot L_xopt (Z.of_nat s) DZ)%R = csum (fun c => (L_q (Z.of_nat s) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) (Z.to_nat DZ)) by (intros s Hs; change DZ with (Z.of_nat (Z.to_nat DZ)); rewrite (Browdot V (Z.of_nat s) (Z.to_nat DZ) ltac:(lia)); rewrite (Browdot L_xopt (Z.of_nat s) (Z.to_nat DZ) ltac:(lia)); rewrite <- csum_mull; rewrite <- csum_add; apply csum_ext; intros c Hc0; ring);",
      "(* q = Ut D U, entrywise *)",
      "assert (Hq : forall s c0 : nat, (s < Z.to_nat DZ)%nat -> (c0 < Z.to_nat DZ)%nat -> L_q (Z.of_nat s) (Z.of_nat c0) = csum (fun w => ((L_eig (Z.of_nat w) * L_U (Z.of_nat w) (Z.of_nat c0)) * L_U (Z.of_nat w) (Z.of_nat s))%R) (Z.to_nat DZ)) by (intros s c0 Hs Hc0; pose proof (HSQ (Z.of_nat s) (Z.of_nat c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E; first [ rewrite E | rewrite <- E ]; change DZ with (Z.of_nat (Z.to_nat DZ)); apply (Bspec (Z.of_nat s) (Z.of_nat c0) (Z.to_nat DZ)); lia);",
      "(* factor the w-th term *)",
      "assert (Hterm : forall w : nat, csum (fun s => csum (fun c => (L_U i (Z.of_nat s) * (((L_eig (Z.of_nat w) * L_U (Z.of_nat w) (Z.of_nat c)) * L_U (Z.of_nat w) (Z.of_nat s)) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ) = (csum (fun s => (L_U i (Z.of_nat s) * L_U (Z.of_nat w) (Z.of_nat s))%R) (Z.to_nat DZ) * (L_eig (Z.of_nat w) * csum (fun c => (L_U (Z.of_nat w) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) (Z.to_nat DZ)))%R) by (intros w; transitivity (csum (fun s => ((L_U i (Z.of_nat s) * L_U (Z.of_nat w) (Z.of_nat s)) * (L_eig (Z.of_nat w) * csum (fun c => (L_U (Z.of_nat w) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) (Z.to_nat DZ)))%R) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; transitivity (csum (fun c => ((L_U i (Z.of_nat s) * L_U (Z.of_nat w) (Z.of_nat s) * L_eig (Z.of_nat w)) * (L_U (Z.of_nat w) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)); [ apply csum_ext; intros c Hc0; ring | rewrite csum_mull; ring ] | apply csum_mulr ]);",
      "(* main chain: U vg = U Q (V - xopt) = (U Ut) D U (V - xopt) = D U (V - xopt) *)",
      "change DZ with (Z.of_nat (Z.to_nat DZ)) at 1; rewrite (Bgrad (Z.to_nat DZ) ltac:(lia));",
      "transitivity (csum (fun s => (L_U i (Z.of_nat s) * (L_RowDot V (Z.of_nat s) DZ + (-1) * L_RowDot L_xopt (Z.of_nat s) DZ))%R) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; cbv beta; pose proof (Hgc (Z.of_nat s) ltac:(lia) ltac:(lia)) as E; first [ rewrite E | rewrite <- E ]; ring | ];",
      "transitivity (csum (fun s => csum (fun c => (L_U i (Z.of_nat s) * (L_q (Z.of_nat s) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; cbv beta; rewrite (Hgrad s Hs); rewrite csum_mull; reflexivity | ];",
      "transitivity (csum (fun s => csum (fun c => (L_U i (Z.of_nat s) * (csum (fun w => ((L_eig (Z.of_nat w) * L_U (Z.of_nat w) (Z.of_nat c)) * L_U (Z.of_nat w) (Z.of_nat s))%R) (Z.to_nat DZ) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; apply csum_ext; intros c Hc0; cbv beta; rewrite (Hq s c Hs Hc0); reflexivity | ];",
      "transitivity (csum (fun s => csum (fun c => csum (fun w => (L_U i (Z.of_nat s) * (((L_eig (Z.of_nat w) * L_U (Z.of_nat w) (Z.of_nat c)) * L_U (Z.of_nat w) (Z.of_nat s)) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; apply csum_ext; intros c Hc0; cbv beta; apply csum_pull | ];",
      "transitivity (csum (fun s => csum (fun w => csum (fun c => (L_U i (Z.of_nat s) * (((L_eig (Z.of_nat w) * L_U (Z.of_nat w) (Z.of_nat c)) * L_U (Z.of_nat w) (Z.of_nat s)) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros s Hs; cbv beta; apply csum_swap | ];",
      "rewrite csum_swap;",
      "transitivity (csum (fun w => (csum (fun s => (L_U i (Z.of_nat s) * L_U (Z.of_nat w) (Z.of_nat s))%R) (Z.to_nat DZ) * (L_eig (Z.of_nat w) * csum (fun c => (L_U (Z.of_nat w) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) (Z.to_nat DZ)))%R) (Z.to_nat DZ)); [ apply csum_ext; intros w Hw; cbv beta; apply (Hterm w) | ];",
      "transitivity (csum (fun w => (L_RowOrth i (Z.of_nat w) (Z.of_nat (Z.to_nat DZ)) * (L_eig (Z.of_nat w) * csum (fun c => (L_U (Z.of_nat w) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) (Z.to_nat DZ)))%R) (Z.to_nat DZ)); [ apply csum_ext; intros w Hw; cbv beta; rewrite (Brow i (Z.of_nat w) (Z.to_nat DZ)) by lia; reflexivity | ];",
      "(* U Ut = I collapses the sum over w to w = i *)",
      "rewrite (csum_delta _ (Z.to_nat DZ) (Z.to_nat i)); [ cbv beta; rewrite Z2Nat.id by lia; rewrite <- (Beig i (Z.to_nat DZ)) by lia; change (Z.of_nat (Z.to_nat DZ)) with DZ; pose proof (HRO i i) as Ho; cbv zeta in Ho; destruct (Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hd _]; rewrite (Hd eq_refl); ring | lia | intros k Hk Hki; cbv beta; pose proof (HRO i (Z.of_nat k)) as Ho; cbv zeta in Ho; destruct (Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hnd]; change (Z.of_nat (Z.to_nat DZ)) with DZ; rewrite Hnd by lia; ring ]",
      "end end." ;
*/

/*@ rocq_proof eigerr_linear:
      "intros;",
      "match goal with |- ((L_EigErr ?VX ?i ?D + ?K * L_EigGrad ?VG ?i ?D)%R = L_EigErr ?VY ?i ?D) =>",
      "match goal with Hc : forall c : Numbers.BinNums.Z, _ |- _ =>",
      "assert (G : forall n : nat, (Z.of_nat n <= D)%Z -> ((L_EigErr VX i (Z.of_nat n) + K * L_EigGrad VG i (Z.of_nat n))%R = L_EigErr VY i (Z.of_nat n)));",
      "[ intros n0; induction n0 as [|k0 IH0]; intros Hn0;",
      "  [ change (Z.of_nat 0) with 0%Z; rewrite !Q_EigErr_base, Q_EigGrad_base; ring",
      "  | replace (Z.of_nat (S k0)) with (1 + Z.of_nat k0)%Z by lia; rewrite <- (Q_EigErr_step VX i (Z.of_nat k0)) by lia; rewrite <- (Q_EigGrad_step VG i (Z.of_nat k0)) by lia; rewrite <- (Q_EigErr_step VY i (Z.of_nat k0)) by lia;",
      "    pose proof (Hc (Z.of_nat k0) ltac:(lia) ltac:(lia)) as E; first [ rewrite E | rewrite <- E ]; rewrite <- IH0 by lia; ring ]",
      "| change D with (Z.of_nat (Z.to_nat D)); apply G; lia ]",
      "end end." ;
*/

/*@ rocq_proof isometry:
      "intros;",
      "match goal with Hortho : P_ColsOrthonormal |- (L_EigErrSq ?V ?DZ = L_ErrSq ?V ?DZ) =>",
      "unfold P_ColsOrthonormal in Hortho;",
      \by(Csum),
      "assert (Beig : forall (p : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_EigErr V p (Z.of_nat n) = csum (fun c => (L_U p (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) n) by (intros p n; induction n as [|k IH]; intros Hn; [ apply Q_EigErr_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_EigErr_step V p (Z.of_nat k)) by lia; ring ]);",
      "assert (Berr : forall (n : nat), (n <= Z.to_nat DZ)%nat -> L_ErrSq V (Z.of_nat n) = csum (fun c => ((L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)))%R) n) by (intros n; induction n as [|k IH]; intros Hn; [ apply Q_ErrSq_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; pose proof (Q_ErrSq_step V (Z.of_nat k)) as Hst; cbv zeta in Hst; rewrite <- Hst by lia; ring ]);",
      "assert (Bsq : forall (n : nat), (n <= Z.to_nat DZ)%nat -> L_EigErrSq V (Z.of_nat n) = csum (fun i0 => (L_EigErr V (Z.of_nat i0) DZ * L_EigErr V (Z.of_nat i0) DZ)%R) n) by (intros n; induction n as [|k IH]; intros Hn; [ apply Q_EigErrSq_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; pose proof (Q_EigErrSq_step V (Z.of_nat k)) as Hst; cbv zeta in Hst; rewrite <- Hst by lia; ring ]);",
      "assert (Bcol : forall (p q : Z) (n : nat), (n <= Z.to_nat DZ)%nat -> L_ColOrth p q (Z.of_nat n) = csum (fun i0 => (L_U (Z.of_nat i0) p * L_U (Z.of_nat i0) q)%R) n) by (intros p q n; induction n as [|k IH]; intros Hn; [ apply Q_ColOrth_base | rewrite csumS, <- IH by lia; replace (Z.of_nat (S k)) with (1 + Z.of_nat k)%Z by lia; rewrite <- (Q_ColOrth_step p q (Z.of_nat k)) by lia; ring ]);",
      "(* Ut U = I : sum_i U(i,s) EigErr_i = entry s of V - xopt *)",
      "assert (Hcollapse : forall s : nat, (s < Z.to_nat DZ)%nat -> csum (fun i0 => (L_U (Z.of_nat i0) (Z.of_nat s) * L_EigErr V (Z.of_nat i0) DZ)%R) (Z.to_nat DZ) = (L_vget V (Z.of_nat s) + (-1) * L_vget L_xopt (Z.of_nat s))%R) by (intros s Hs; transitivity (csum (fun i0 => csum (fun c => (L_U (Z.of_nat i0) (Z.of_nat s) * (L_U (Z.of_nat i0) (Z.of_nat c) * (L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c))))%R) (Z.to_nat DZ)) (Z.to_nat DZ)); [ apply csum_ext; intros i0 Hi; cbv beta; change DZ with (Z.of_nat (Z.to_nat DZ)); rewrite (Beig (Z.of_nat i0) (Z.to_nat DZ)) by lia; rewrite csum_mull; reflexivity | rewrite csum_swap; transitivity (csum (fun c => ((L_vget V (Z.of_nat c) + (-1) * L_vget L_xopt (Z.of_nat c)) * L_ColOrth (Z.of_nat s) (Z.of_nat c) DZ)%R) (Z.to_nat DZ)); [ apply csum_ext; intros c Hc0; cbv beta; change DZ with (Z.of_nat (Z.to_nat DZ)); rewrite (Bcol (Z.of_nat s) (Z.of_nat c) (Z.to_nat DZ)) by lia; rewrite <- csum_mull; apply csum_ext; intros i0 Hi; cbv beta; ring | rewrite (csum_delta _ (Z.to_nat DZ) s); [ cbv beta; pose proof (Hortho (Z.of_nat s) (Z.of_nat s)) as Ho; cbv zeta in Ho; destruct (Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hd _]; rewrite (Hd eq_refl); ring | lia | intros k Hk Hks; cbv beta; pose proof (Hortho (Z.of_nat s) (Z.of_nat k)) as Ho; cbv zeta in Ho; destruct (Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hnd]; rewrite Hnd by lia; ring ] ] ]);",
      "(* main chain *)",
      "change DZ with (Z.of_nat (Z.to_nat DZ)); rewrite (Bsq (Z.to_nat DZ) ltac:(lia)), (Berr (Z.to_nat DZ) ltac:(lia));",
      "transitivity (csum (fun s => ((L_vget V (Z.of_nat s) + (-1) * L_vget L_xopt (Z.of_nat s)) * csum (fun i0 => (L_U (Z.of_nat i0) (Z.of_nat s) * L_EigErr V (Z.of_nat i0) DZ)%R) (Z.to_nat DZ))%R) (Z.to_nat DZ));",
      "[ transitivity (csum (fun i0 => csum (fun s => ((L_U (Z.of_nat i0) (Z.of_nat s) * (L_vget V (Z.of_nat s) + (-1) * L_vget L_xopt (Z.of_nat s))) * L_EigErr V (Z.of_nat i0) DZ)%R) (Z.to_nat DZ)) (Z.to_nat DZ));",
      "  [ apply csum_ext; intros i0 Hi; cbv beta; rewrite csum_mulr; change DZ with (Z.of_nat (Z.to_nat DZ)) at 1; rewrite (Beig (Z.of_nat i0) (Z.to_nat DZ)) at 1 by lia; reflexivity",
      "  | rewrite csum_swap; apply csum_ext; intros s Hs; cbv beta; rewrite <- csum_mull; apply csum_ext; intros i0 Hi; cbv beta; ring ]",
      "| apply csum_ext; intros s Hs; cbv beta; rewrite (Hcollapse s Hs); ring ]",
      "end." ;
*/

/*@ rocq_proof coord_sq_le_total:
      "intros;",
      "match goal with |- (?r * ?r <= L_EigErrSq ?V ?D)%R =>",
      "match goal with Hr := L_EigErr V ?i D |- _ =>",
      "assert (G : forall n : nat, (Z.of_nat n <= D)%Z -> (0 <= L_EigErrSq V (Z.of_nat n))%R /\ ((i < Z.of_nat n)%Z -> (r * r <= L_EigErrSq V (Z.of_nat n))%R));",
      "[ intros n0; induction n0 as [|k0 IH0]; intros Hn0;",
      "  [ change (Z.of_nat 0) with 0%Z; rewrite Q_EigErrSq_base; split; [ lra | intros; lia ]",
      "  | destruct (IH0 ltac:(lia)) as [IH1 IH2]; pose proof (Q_EigErrSq_step V (Z.of_nat k0)) as Hst; cbv zeta in Hst; specialize (Hst ltac:(lia) ltac:(lia));",
      "    replace (Z.of_nat (S k0)) with (1 + Z.of_nat k0)%Z by lia; rewrite <- Hst;",
      "    assert (Hsq : (0 <= L_EigErr V (Z.of_nat k0) D * L_EigErr V (Z.of_nat k0) D)%R) by nra;",
      "    split; [ lra | intros Hi; assert (Hc : (i < Z.of_nat k0)%Z \/ i = Z.of_nat k0) by lia; destruct Hc as [Hc | Hc]; [ specialize (IH2 Hc); lra | assert (Hrr : r = L_EigErr V (Z.of_nat k0) D) by (rewrite <- Hc; reflexivity); rewrite Hrr; lra ] ] ]",
      "| destruct (G (Z.to_nat D) ltac:(lia)) as [_ Hf]; change D with (Z.of_nat (Z.to_nat D)); apply Hf; lia ]",
      "end end." ;
*/

/* (C3_SD): numeric certificate for the iteration count */
/*@ rocq_proof N_sufficient:
      "match goal with |- (?A <= ?C / sqrt ?D)%R => assert (Hd : (0 <= D)%R) by lra; assert (Hs : (sqrt D * sqrt D = D)%R) by (apply sqrt_sqrt; exact Hd); assert (Hp : (0 < sqrt D)%R) by (apply sqrt_lt_R0; lra); assert (Hc : ((C / sqrt D * sqrt D)%R = C)) by (field; apply Rgt_not_eq; exact Hp); apply Rmult_le_reg_r with (r := sqrt D); [ exact Hp | ]; rewrite Hc; assert (HC : (0 <= C)%R) by lra; apply Rsqr_incr_0_var; [ | exact HC ]; unfold Rsqr; replace ((A * sqrt D) * (A * sqrt D))%R with ((A * A) * (sqrt D * sqrt D))%R by ring; rewrite Hs; simpl; lra end." ;
*/


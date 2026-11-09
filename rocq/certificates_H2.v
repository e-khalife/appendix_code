(* (H2) for the case study, with m = 27.58 and L = 45.417. The entries are those of
   the binary64 data Q, with m and L rounded outward to binary64:
   m' = 27.580000000000002 >= m and L' = 45.416999999999994 <= L, so that
   Q - m I >= Q - m' I > 0 and L I - Q >= L' I - Q > 0. *)
From Bignums Require Import BigZ.
From Interval Require Import Float.Specific_ops.
From mathcomp Require Import seq.
From ValidSDP Require Import posdef_check.
Local Open Scope bigZ_scope.

(* Q - m' I *)
Lemma Q_minus_mI : posdef_seqF
  [:: [:: Float 2420157184545491 (-48); Float (-1130629384751813) (-49); Float (-2421613579916471) (-48)];
      [:: Float (-1130629384751813) (-49); Float 1401288502715677 (-48); Float 2270211062393845 (-50)];
      [:: Float (-2421613579916471) (-48); Float 2270211062393845 (-50); Float 2423246497572013 (-48)]].
Proof. posdef_check. Qed.

(* L' I - Q *)
Lemma LI_minus_Q : posdef_seqF
  [:: [:: Float 1300255987521239 (-47); Float 1130629384751813 (-49); Float 2421613579916471 (-48)];
      [:: Float 1130629384751813 (-49); Float 904845164218073 (-46); Float (-2270211062393845) (-50)];
      [:: Float 2421613579916471 (-48); Float (-2270211062393845) (-50); Float 649355665503989 (-46)]].
Proof. posdef_check. Qed.

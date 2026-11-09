(* vec_model.v

   Consistency of the axioms on logic vectors.

   The specification represents the vectors of R^d by the logic type vec, whose entries
   are given by vget(v,i). Two axioms relate vec to the rest of the specification. The
   axiom vec_of_get states that the i-th entry of vec_of{K}(a), the vector stored in the
   array a in the program state K, is the value of a[i] in that state. In Pathway DC, the
   axiom vlin_get states that the i-th entry of vlin(a,u,b,v) is a u_i + b v_i.

   This script builds a model in which both axioms hold. Vectors are functions from
   integers to reals, a program state maps each address to the real stored there,
   vec_of reads the array a[0 .. d-1], and vlin combines two vectors entrywise. Hence
   these axioms cannot make the specification inconsistent. The model holds for every
   dimension d, and Print Assumptions reports only axioms of the real numbers of the
   Rocq standard library. The other axioms of the specification, the base and step
   pairs of the recursive sums, define new functions by recursion on the number of
   terms, so they extend this model.

   Check with: rocq compile vec_model.v
*)

From Stdlib Require Import ZArith Reals.

Open Scope R_scope.

Section VecModel.

(* the dimension of the program; any value works *)
Variable d : Z.

(* vec: the vectors of R^d, as functions from integers to reals, and vget reads an entry *)
Definition vec : Type := Z -> R.
Definition vget (v : vec) (i : Z) : R := v i.

(* a program state maps each address to the real stored there; the array a starts at
   the address a, so a[i] is stored at a + i *)
Definition state : Type := Z -> R.

(* vec_of{K}(a): the vector stored in a[0 .. d-1] in the state K, and 0 outside [0, d) *)
Definition vec_of (K : state) (a : Z) : vec :=
  fun i => if andb (0 <=? i)%Z (i <? d)%Z then K (a + i)%Z else 0.

(* the axiom vec_of_get holds *)
Lemma vec_of_get : forall (K : state) (a i : Z),
  (0 <= i < d)%Z -> vget (vec_of K a) i = K (a + i)%Z.
Proof.
  intros K a i [Hlo Hhi]. unfold vget, vec_of.
  (* on [0, d), the guard is true, so vec_of reads a[i] *)
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  rewrite Hlo, Hhi. reflexivity.
Qed.

(* vec_of reads nothing outside a[0 .. d-1], as its reads clause states: two states
   that agree on a[0 .. d-1] give the same vector *)
Lemma vec_of_reads : forall (K1 K2 : state) (a : Z),
  (forall i, (0 <= i < d)%Z -> K1 (a + i)%Z = K2 (a + i)%Z) ->
  forall i, vget (vec_of K1 a) i = vget (vec_of K2 a) i.
Proof.
  intros K1 K2 a Hagree i. unfold vget, vec_of.
  destruct (andb (0 <=? i)%Z (i <? d)%Z) eqn:Hi.
  - (* inside [0, d), the two states agree *)
    apply andb_prop in Hi. destruct Hi as [Hlo Hhi].
    apply Hagree. split; [apply Z.leb_le | apply Z.ltb_lt]; assumption.
  - (* outside [0, d), both entries are 0 *)
    reflexivity.
Qed.

(* vlin(a,u,b,v): the linear combination a u + b v, entrywise *)
Definition vlin (a : R) (u : vec) (b : R) (v : vec) : vec :=
  fun i => a * vget u i + b * vget v i.

(* the axiom vlin_get holds *)
Lemma vlin_get : forall (a b : R) (i : Z) (u v : vec),
  (0 <= i < d)%Z -> vget (vlin a u b v) i = a * vget u i + b * vget v i.
Proof. intros. reflexivity. Qed.

End VecModel.

(* both axioms hold in one model, for every dimension d *)
Theorem vector_axioms_consistent : forall d : Z,
  (forall (K : state) (a i : Z),
     (0 <= i < d)%Z -> vget (vec_of d K a) i = K (a + i)%Z) /\
  (forall (a b : R) (i : Z) (u v : vec),
     (0 <= i < d)%Z -> vget (vlin a u b v) i = a * vget u i + b * vget v i).
Proof. intros d. split; [ apply vec_of_get | apply vlin_get ]. Qed.

Print Assumptions vector_axioms_consistent.

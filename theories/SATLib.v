From Coq Require Import Int63 List ZArith.
From SMTCoq Require Import Trace PArray State.
Import Sat_Checker ListNotations.

Section SATLib.

Fixpoint copy_list_to_array {A} (cl : list A) (i : int) (acc : array A) : array A :=
  match cl with
  | [] => acc
  | x::cl => copy_list_to_array cl (i + 1)%int63 (set acc i x)
  end.

Definition compile_clause (cl : list Int63.int) : array int :=
  let len := of_Z (Z.of_nat (List.length cl)) in
  let arr := make len 0%int63 in
  copy_list_to_array cl 0 arr.

Definition compile_cnf (cnf : list (list Int63.int)) : array (array int) :=
  let len := of_Z (Z.of_nat (List.length cnf)) in
  let dft_clause := make 1%int63 0%int63 in
  let arr := make len dft_clause in
  copy_list_to_array (List.map compile_clause cnf) 0 arr.

Definition eval_clause (rho : Valuation.t) (cl : list Int63.int) :=
  List.existsb rho cl.

Definition eval_cnf (rho : Valuation.t) (cnf : list (list Int63.int)) :=
  List.forallb (eval_clause rho) cnf.

Theorem compile_clause_correct:
  forall cl rho, 
    eval_clause rho cl = C_interp_or rho (compile_clause cl).
Proof.
  induction cl; intros.
  - simpl. unfold compile_clause, copy_list_to_array.
    unfold C_interp_or. simpl.
    rewrite Misc.afold_left_orb_false; auto.
    intros. rewrite Misc.length_amap, length_make in H.
    destruct (0 ≤? max_length)%int63 eqn:He; try easy.
    now apply Misc.ltb_0 in H.
  - simpl. unfold compile_clause. simpl Datatypes.length.
Admitted.

Theorem compile_cnf_correct:
  forall cnf rho, 
    eval_cnf rho cnf = valid rho (compile_cnf cnf).
Proof.
Admitted.

End SATLib.
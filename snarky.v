Require Import Coq.ZArith.ZArith.

Inductive ty : Type :=
  | Unit : ty
  | Prod : ty -> ty -> ty
  | Arrow : ty -> ty -> ty
  | Field : ty.

Inductive tm : Type :=
  | U : tm
  | Pair : tm -> tm -> tm
  | Lit : Z -> tm
  | Var : nat -> tm
  | Lam : tm -> tm
  | App : tm -> tm -> tm
  | Choose : tm
  | Add : tm -> tm -> tm
  | Assert_in : tm -> tm -> tm -> tm -> tm
  | Let_in : tm -> tm -> tm.

Inductive is_value : tm -> Prop :=
  | VU : is_value U
  | VPair : forall x y, is_value x -> is_value y -> is_value (Pair x y)
  | VLit : forall x, is_value (Lit x)
  | VLam : forall e, is_value (Lam e). 

Definition value : Type := { t : tm | is_value t }.

Theorem is_value_pair : forall (v1 v2 : value), is_value (Pair (proj1_sig v1) (proj1_sig v2)).
Proof.
intros.
apply VPair.
apply (proj2_sig v1).
apply (proj2_sig v2).
Qed.

Definition pair_value (v1 v2 : value) : value :=
 exist is_value (Pair (proj1_sig v1) (proj1_sig v2)) (is_value_pair v1 v2).

Definition lit_value (x : Z) : value :=
  exist is_value (Lit x) (VLit x).

Definition lam_value (e : tm) : value :=
  exist is_value (Lam e) (VLam e).

Require Coq.Lists.List.
Open Scope Z_scope.
Inductive big_step (C : list value) : tm -> value -> Prop :=
  | BSU : big_step C U (exist is_value U VU)
  | BSPair : forall t1 t2 v1 v2, big_step C t1 v1 -> big_step C t2 v2 -> big_step C (Pair t1 t2) 
    (pair_value v1 v2)
  | BSLit : forall n, big_step C (Lit n) (lit_value n)
  | BSAdd : forall t1 t2 v1 v2, big_step C t1 (lit_value v1) -> big_step C t2 (lit_value v2)
    -> big_step C (Add t1 t2) (lit_value (v1 + v2))
  | BSChoose : forall v, big_step C Choose (lit_value v)
  | BSAssert_in : forall t1 t2 t3 v1 v2 v3 k vk, 
    big_step C t1 (lit_value v1) ->
    big_step C t2 (lit_value v2) ->
    big_step C t3 (lit_value v3) ->
    (v1 * v2 = v3) ->
    big_step C k vk ->
    big_step C (Assert_in t1 t2 t3 k) vk
  | BSLam : forall e, big_step C (Lam e) (lam_value e)
  | BSApp : forall tf ef tx vx vy, 
    big_step C tx vx ->
    big_step C tf (lam_value ef) ->
    big_step (cons vx C) ef vy ->
    big_step C (App tf tx) vy
  | BSVar : forall n v, Coq.Lists.List.nth_error C n = Some v -> big_step C (Var n) v
  | BSLet_in : forall tx vx ty vy,
    big_step C tx vx ->
    big_step (vx :: C) ty vy ->
    big_step C (Let_in tx ty) vy.

Definition choose_bit : tm :=
  Let_in Choose (Assert_in (Var 0) (Var 0) (Var 0) (Var 0)).

Theorem choose_bit_BS : big_step nil choose_bit (lit_value 0).
Proof.
unfold choose_bit.
apply BSLet_in with (vx := lit_value 0).
apply BSChoose.
apply BSAssert_in with (v1 := 0) (v2 := 0) (v3 := 0).
apply BSVar. reflexivity.
apply BSVar. reflexivity.
apply BSVar. reflexivity.
reflexivity.
apply BSVar. reflexivity.
Qed.

Theorem plus_cancel : forall x y : nat, Nat.add x y = x -> y = Nat.zero.
Proof.
intros.
induction x.
apply H.
apply IHx.
simpl in H.
inversion H. rewrite H1. apply H1.
Qed.

Theorem mul_zero : forall x y : nat, Nat.mul x (S y) = Nat.zero -> x = Nat.zero.
Proof.
intros.
induction x.
reflexivity.
simpl in H.
inversion H.
Qed.

Theorem nat_bit_root : forall n : nat, Nat.mul n n = n -> n = Nat.zero \/ n = Nat.one.
Proof.
intros.
destruct n.
unfold Nat.mul in H. left. reflexivity.
right. apply f_equal. simpl in H. injection H. intros.
remember (plus_cancel n (Nat.mul n (S n)) H0) as H1.
apply mul_zero with (x := n) (y := n).
apply H1.
Qed.

Require Import Coq.ZArith.Znat.

Lemma pos_to_nat_nonzero : forall n, Pos.to_nat n = Nat.zero -> False.
Proof.

  Lemma iterlem : forall p, forall m, exists k, Pos.iter_op Nat.add p (S m) = S k.
  intro p.
  induction p.
  simpl. intro m. 

  exists (Nat.add m (Pos.iter_op Nat.add p (S (m + S m)))). trivial.
  simpl. intro m. apply IHp. simpl. intro m. exists m. trivial.
  Qed.

intros. 
remember (iterlem n Nat.zero) as H1. destruct H1.
assert (Pos.iter_op Nat.add n (S Nat.zero) = Pos.to_nat n).
trivial. clear HeqH1.
rewrite H0 in e. rewrite H in e. inversion e.
Qed.

Theorem bit_root : forall x, x * x = x -> x = 0 \/ x = 1.
Proof.
intros.
Lemma pos_mul : forall a b c, 0<=a -> 0<=b -> (a * b) = c -> Nat.mul (Z.to_nat a) (Z.to_nat b) = (Z.to_nat c).
intros. symmetry.
rewrite <- H1.
apply Z2Nat.inj_mul. trivial. trivial.
Qed.
Lemma positive_mul : forall a b c, (a * b)%positive = c -> Nat.mul (Pos.to_nat a) (Pos.to_nat b) = Pos.to_nat c.
intros.
rewrite <- Z2Nat.inj_pos.
rewrite <- Z2Nat.inj_pos.
rewrite <- Z2Nat.inj_pos.
apply pos_mul.
compute. intros. inversion H0. compute. intros. inversion H0.
simpl. apply f_equal. apply H.
Qed.

destruct x.
left. trivial. simpl in H.

right. injection H.
intros.
remember (positive_mul p p p H0) as H1.
remember (nat_bit_root (Pos.to_nat p) H1) as Hnat.
destruct Hnat. inversion e.
remember (pos_to_nat_nonzero p H3).
inversion f.
clear HeqHnat.
rewrite <- Z2Nat.inj_pos in e.
assert (Nat.one = Z.to_nat (Z.pos 1)).
trivial.
rewrite H2 in e.
apply Z2Nat.inj in e. apply e. compute. intro. inversion H3.
compute. intro. inversion H3.
simpl in H. inversion H.
Qed.

Theorem choose_bit_correct : forall v, big_step nil choose_bit v -> v = lit_value 0 \/ v = lit_value 1.
Proof.
intros.
unfold choose_bit in H.
inversion H.
inversion H4.
assert (lit_value v1 = vx).
  inversion H9. compute in H16. inversion H16. trivial. clear H9.
assert (lit_value v2 = vx).
  inversion H10. compute in H16. inversion H16. trivial. clear H10.
assert (lit_value v3 = vx).
  inversion H12. compute in H16. inversion H16. trivial. clear H12.
assert (v1 = v2).
  rewrite <- H15 in H9. inversion H9. trivial.
assert (v2 = v3).
  rewrite <- H9 in H10. inversion H10. trivial.
rewrite <- H16 in H13. rewrite <- H12 in H13.
remember (bit_root v1 H13) as HH. clear HeqHH.
inversion H14. compute in H18. inversion H18. rewrite <- H15 in H21.
destruct HH. left. rewrite <- H21. apply f_equal. symmetry. rewrite <-  H20. trivial.
right. rewrite <- H21. apply f_equal. apply H20.
Qed.

Definition sqrt_exn :=
  Lam (Let_in Choose (Assert_in (Var 0) (Var 0) (Var 1) (Var 0))).

Theorem sqrt_exn_sound
  : forall C nx vy, big_step C (App sqrt_exn (Lit nx)) vy ->
exists ny, vy = lit_value ny /\ (ny * ny) = nx.
Proof.
intros.
unfold sqrt_exn in H. inversion H.
inversion H3. rewrite <- H8 in H5.
inversion H5. inversion H12.
assert (lit_value v1 = vx0).
  inversion H17. compute in H24. inversion H24. trivial.
assert (lit_value v2 = vx0).
  inversion H18. compute in H25. inversion H25. trivial.
assert (v1 = v2).
  assert (lit_value v1 = lit_value v2).
  rewrite H23. rewrite H24. trivial.
  inversion H25. trivial.

exists v1. split.
  inversion H12. inversion H35. compute in H37. inversion H37. clear H37. rewrite <- H40. rewrite H23. trivial.

  rewrite <- H25 in H21.
  assert (v3 = nx).
    inversion H20. compute in H27. inversion H27.
    inversion H2.
  rewrite H30 in H29. inversion H29. trivial.
  rewrite <- H26. assumption.
Qed.

Theorem sqrt_exn_complete
  : forall nx ny, ny * ny = nx -> forall C, big_step C (App sqrt_exn (Lit nx)) (lit_value ny).
Proof.
intros.
Definition ef := (Let_in Choose (Assert_in (Var 0) (Var 0) (Var 1) (Var 0))).
apply BSApp with (ef := ef) (vx := lit_value nx).
apply BSLit.
unfold sqrt_exn. apply BSLam.
unfold ef.
apply BSLet_in with (vx := lit_value ny).
apply BSChoose.
apply BSAssert_in with (v1 := ny) (v2 := ny) (v3 := nx);
try apply BSVar; try trivial.
Qed.
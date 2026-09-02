Require Import Coq.ZArith.Znumtheory.
Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.
Require Import Lia.
Open Scope Z_scope.
Require Import Classical.
Require Export ZArith_base.
Require Import Zbool ZArithRing Zcomplements Setoid Morphisms.
Local Open Scope Z_scope.

Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zorder.
Require Import ZArith_dec.

(* Exponentiation *)

Require Import Coq.ZArith.Zpower.

(* Permutations *)

Require Import Coq.Sorting.Permutation.
Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Import ListNotations. 

Set Implicit Arguments.


(* Basic propositional logic lemmas *)

Theorem contra_implies_OG :  forall (P Q : Prop), (~Q -> ~P) -> (P -> Q) . 
Proof.
    unfold not. intros P Q. intros A B.
    destruct (classic Q) as [Q_holds|NQ_holds].
    apply Q_holds.
    apply False_ind.
    apply A.
    apply NQ_holds.
    apply B.
Qed.

Theorem OG_implies_contra : forall p q:Prop, (p->q)->(~q->~p).
Proof. tauto. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  tauto. Qed.

Theorem double_neg_conv : forall P : Prop,
    ~~P -> P.
Proof.
  tauto. Qed.

  Theorem deMorgan : forall P Q : Prop,
    ~P /\ ~Q  -> ~(P \/ Q).
Proof.
    firstorder.
Qed.

(* Basic number theoretic lemmas concerning modular arithmetic. *)

Lemma Zdivide_mod_conv:
    forall a b,  a mod b <> 0 -> ~ (b | a).
Proof. 
    intros. apply contra_implies_OG with (P := (a mod b <> 0)); auto.
    firstorder. apply double_neg_conv in H0. apply double_neg. apply Zdivide_mod. auto.
Qed.

Lemma Zmod_divide_conv:
    forall a b, b <> 0 -> ~ (b | a) -> a mod b <> 0.
Proof.
    intros. apply contra_implies_OG with (P :=  ~ (b | a)); auto.
    firstorder. apply double_neg_conv in H1. apply double_neg. apply Zmod_divide; 
    auto.
Qed.

Lemma mod_is_homomorphic:
    forall a b n, n > 0 ->  ((a mod n) + (b mod n)) mod n = (a + b) mod n.
Proof.
    intros.
    assert (a = n*(a/n) + (a mod n)) as Hadiv1.
    apply Z_div_mod_eq_full.
    assert (b = n*(b/n) + (b mod n)) as Hadiv2.
    apply Z_div_mod_eq_full.
    assert (a + b = n * (a / n) + a mod n + (n * (b / n)  + b mod n)) as Hadd.
    rewrite <- Hadiv1. 
    rewrite <- Hadiv2. auto. 
    rewrite Z.add_shuffle1 with 
    (n := n * (a / n))(m := a mod n)(p := n * (b / n))(q := b mod n) in Hadd.
    rewrite <- Z.mul_add_distr_l with
    (n := n)(m := (a / n))(p := (b / n)) in Hadd.
    remember (a mod n + b mod n) as r3.
    assert (r3 = n * (r3/n) + (r3 mod n)) as Hrem.
    apply Z_div_mod_eq_full.
    rewrite Hrem in Hadd.
    rewrite Z.add_assoc 
    with (n := n * (a / n + b / n))(m := (n * (r3 / n)))(p := r3 mod n)
    in Hadd.
    remember (a/n + b/n) as q2.
    rewrite <- Z.mul_add_distr_l with
    (n := n)(m := q2)(p := r3/n) in Hadd.
    remember (q2 + r3 / n) as q3.
    assert (a + b = n * ((a + b)/n) + (a + b) mod n).
    apply Z_div_mod_eq_full.
    assert (0 <= r3 mod n < n).
    apply Z_mod_lt. auto.
    assert (q3 = ((a + b)/n) /\ r3 mod n = (a + b) mod n).
    apply Zdiv_mod_unique with (b := n).
    assert (Z.abs n = n).
    apply Z.abs_eq. lia.
    rewrite H2. apply H1.
    assert (Z.abs n = n).
    apply Z.abs_eq. lia.
    rewrite H2. apply Z_mod_lt. auto.
    rewrite <- Hadd. rewrite <- H0. auto.
    firstorder.
Qed.

Lemma mod_is_homomorphic_minus:
    forall a b n, n > 1 ->  ((a mod n) - (b mod n)) mod n = (a - b) mod n.
Proof.
    intros.
    rewrite Zminus_mod_idemp_r with (a := a mod n)(b := b)(n := n).
    rewrite Zminus_mod_idemp_l with (a := a)(b := b)(n := n).
    auto.
Qed.

Lemma mod_is_homomorphic_mult:
    forall a b n, n > 1 ->  ((a mod n) * (b mod n)) mod n = (a * b) mod n.
Proof.
    intros.
    rewrite Zmult_mod_idemp_r with (b := (a mod n))(a := b)(n := n).
    rewrite Zmult_mod_idemp_l with (a := a)(b := b)(n := n).
    auto.
Qed.

Lemma mod_is_well_defined:
    forall a b n, n > 1 -> a = b -> a mod n = b mod n.
Proof.
    firstorder.
    rewrite H0.
    auto.
Qed.

Lemma mod_zero_product:
    forall v n, v*n mod n = 0.
Proof.
    intros. 
    assert (n | (v * n)) as Hdiv. apply Z.divide_factor_r.
    apply Zdivide_mod. auto.
Qed.

Lemma add_zero_mod:
    forall v n, v mod n + 0 = v mod n.
Proof.
    intros; lia.
Qed.

Lemma simplify_modmod:
    forall v n, n > 0 -> v mod n = (v mod n) mod n.
Proof.
    intros. assert (n | n) as Htrivial. apply Z.divide_refl. apply Zmod_div_mod; try lia; auto. 
Qed.

Lemma inverses_exists_mod_rel_prime:
    forall u n, n > 1 -> rel_prime u n -> exists v, (v * u) mod n = 1 mod n.
Proof.
    intros. apply rel_prime_bezout in H0. inversion H0.
    apply mod_is_well_defined with (a := u0 * u + v * n)(b := 1)(n := n) in H1; 
    auto.
    rewrite <- mod_is_homomorphic with (a := u0 * u)(b := v * n) in H1; auto.
    rewrite mod_zero_product in H1.  
    rewrite add_zero_mod in H1. 
    rewrite <- simplify_modmod in H1.
    eexists. eauto. lia. lia.
Qed.

Lemma mult_both_sides:
    forall a b c n, n > 1 -> b mod n = c mod n -> (a * b) mod n = (a * c) mod n.
Proof.
    intros. rewrite <- mod_is_homomorphic_mult; auto. rewrite H0. 
    rewrite mod_is_homomorphic_mult; auto. 
Qed.

Lemma exp_nonzero:
    forall (a : Z)(k : nat), a <> 0 -> Zpower_nat a k <> 0.
Proof.
    intros.
    induction k.
    simpl. discriminate.
    simpl.
    apply Z.neq_mul_0. firstorder.
Qed.

Lemma mult_by_x_unchanged_identity:
    forall a b, a * b = a /\ a <> 0 -> b = 1.
Proof.
    firstorder.
    apply Z.mul_id_l with (n := b)(m := a).
    auto. lia.
Qed.

(* The following shows that the nonzero integers mod p form a group, namely 
  the product of nonzero elements remains nonzero. *)

Lemma no_zero_divisors_mod_p:
  forall a x p:Z, prime p /\ a mod p <> 0 /\ x mod p <> 0 -> (a * x) mod p <> 0.
Proof.
  intros. inversion H. inversion H1.
  assert (~(p | a)).
  apply Zdivide_mod_conv. auto.
  assert (~(p | x)).
  apply Zdivide_mod_conv. auto.
  assert (~(p | a) /\ ~(p | x)). auto.
  assert (~((p | a) \/ (p | x))). firstorder.
  assert (~((p | a) \/ (p | x)) -> ~(p | a * x)).
  apply OG_implies_contra. apply prime_mult. auto.
  apply H8 in H7. apply Zmod_divide_conv with (a := a*x). 
  apply prime_ge_2 in H0 as Hge. lia. auto.
Qed.

(* Here are the two main number theoretic lemma which drives the proof: namely, 
   they show that (1) inverses modulo a prime exist (2) and inverses are unique *)

Lemma inverses_exists_mod_prime:
   forall u p, p > 1 -> prime p -> 0 <> u mod p -> exists v, (v * u) mod p = 1 mod p.
Proof.
   intros. assert (~(p | u)). apply Zdivide_mod_conv. auto. 
   assert (rel_prime p u). apply prime_rel_prime; auto.
   apply inverses_exists_mod_rel_prime; auto. apply rel_prime_sym. auto.
Qed.

Lemma units_form_gp_mod_prime:
    forall a b p, prime p -> rel_prime a p -> rel_prime b p ->
    exists w, (a * w) mod p = b mod p /\ rel_prime w p. 
Proof.
    intros. apply rel_prime_bezout in H0. inversion H0.
    assert(b * (u * a + v * p) = b).
    rewrite H2. lia.
    apply mod_is_well_defined with 
    (a := b * (u * a + v * p))(b := b)(n := p) in H3.
    assert(b * (u * a + v * p) = b * u * a + b * v * p).
    lia. rewrite H4 in H3.
    rewrite <- mod_is_homomorphic with (a := b * u * a)(b := b * v * p) in H3.
    rewrite mod_zero_product in H3.  
    rewrite add_zero_mod in H3. 
    rewrite <- simplify_modmod in H3. 
    assert(b * u * a = a * (b * u)). lia. 
    rewrite H5 in H3. 
    apply prime_ge_2 in H. assert(rel_prime p u).
    assert(Bezout p u 1).
    assert(v * p + a * u = 1). lia.
    apply Bezout_intro in H6. assumption. 
    apply bezout_rel_prime. assumption. 
    apply rel_prime_bezout in H1. inversion H1.
    assert(v0 * p + u0 * b = 1). lia.
    apply Bezout_intro in H8.
    apply bezout_rel_prime in H8.
    assert(rel_prime p (u * b)).
    apply rel_prime_mult. assumption. assumption.
    assert (b * u = u * b). lia. rewrite <- H10 in H9.
    remember (b * u) as w. 
    apply rel_prime_bezout in H9. inversion H9.
    assert(v1 * w + u1 * p = 1). lia. apply Bezout_intro in H12.
    apply bezout_rel_prime in H12. 
    assert((a * w) mod p = b mod p /\ rel_prime w p). 
    split. assumption. assumption. eexists. apply H13.
    apply prime_ge_2 in H. lia.
    apply prime_ge_2 in H. lia.
    apply prime_ge_2 in H. lia.
Qed.

Lemma units_form_gp_mod_prime':
    forall a b p, prime p /\ rel_prime a p /\ 1 <= b <= p-1 ->
    exists w, (a * w) mod p = b mod p /\ rel_prime w p. 
Proof.
    intros. inversion H. 
    assert(exists w, (a * w) mod p = b mod p /\ rel_prime w p).
    apply units_form_gp_mod_prime. assumption.
    inversion H1. assumption. 
    inversion H. inversion H3.
    apply rel_prime_le_prime. assumption. lia. 
    inversion H2. clear H2.
    assert((a * (x mod p)) mod p = b mod p /\ 
    rel_prime (x mod p) p).
    split.
    rewrite Zmult_mod_idemp_r. inversion H3. assumption.
    apply rel_prime_mod. lia. inversion H3. assumption.
    remember (x mod p) as w. eexists. 
    assert(b mod p = b). apply Zmod_small. lia. apply H2.
Qed.

Lemma inverses_are_unique_mod_prime:
   forall a b c p, prime p -> 0 <> a mod p -> 
   (a * b) mod p = (a * c) mod p -> b mod p = c mod p.
Proof.
   intros. apply prime_ge_2 in H as Hge.
   assert (exists v, (v * a) mod p = 1 mod p).
   apply inverses_exists_mod_prime with (u := a); auto; try lia. 
   elim H2. firstorder. apply mult_both_sides with (a := x) in H1 as Hmult.
   rewrite Z.mul_assoc in Hmult.
   rewrite <- mod_is_homomorphic_mult in Hmult. rewrite H3 in Hmult.
   rewrite mod_is_homomorphic_mult in Hmult. rewrite Z.mul_1_l in Hmult.
   rewrite Z.mul_assoc in Hmult. rewrite <- mod_is_homomorphic_mult in Hmult.
   rewrite H3 in Hmult. rewrite mod_is_homomorphic_mult in Hmult. rewrite Z.mul_1_l in Hmult.
   auto. all : lia.
Qed.

(* Here, we define functions we will use later over the course of the proof. 
   Namely, we will need lists of integers from 1 to n, and we will also need to
   multiple every number in the list by some nonzero a in Z/pZ. *)

Definition times_a (a x p : Z) : Z :=
    (a * x) mod p.

Definition times_a_map (a p : Z) : (Z -> Z) :=
    fun x => times_a a x p. 

Fixpoint factorial_list (p : nat) : list nat :=
    match p with 
    | O => []
    | (S n) => cons (S n) (factorial_list n)
    end.

Fixpoint mod_n_list (n : nat) : list Z := 
    match n with
    | O => []
    | (S k) => cons (Z.of_nat (S k)) (mod_n_list k)
    end.   

Lemma length_mod_n_list:
    forall (n : nat), length (mod_n_list n) = n.
Proof.
    induction n. auto. simpl.
    rewrite IHn. auto.
Qed.

(* We will also want lemmas that show the list of integers we wrote is indeed
   every integer from 1 to n *)

Lemma mod_n_list_leq_n:
    forall (n : nat)(i : Z), In i (mod_n_list n) -> 1 <= i <= Z.of_nat n. 
Proof.
    induction n. contradiction.
    intros. simpl. destruct (mod_n_list (S n)) eqn: Hmod in H. contradiction.
    simpl in Hmod. apply in_inv in H. inversion Hmod. destruct H. 
    rewrite H in H1. lia.
    rewrite <- H2 in H.
    apply IHn in H. lia.
Qed.

Lemma if_leq_n_in_mod_n_list:
    forall (n : nat)(i : Z), 1 <= i <= Z.of_nat n -> In i (mod_n_list n).
Proof.
    induction n. intros. lia.
    intros. simpl. 
    assert (1 <= i <= Z.of_nat n \/ i = Z.pos (Pos.of_succ_nat n)).
    lia. 
    destruct H0 as [Heq|Hless]. apply IHn in Heq. firstorder.
    firstorder.
Qed.

Lemma mod_n_iff_less_n:
    forall (n : nat)(i : Z), In i (mod_n_list n) <-> 1 <= i <= Z.of_nat n.
Proof.
    firstorder. apply mod_n_list_leq_n in H. lia.
    apply mod_n_list_leq_n in H. lia.
    assert (1 <= i <= Z.of_nat n).
    lia. apply if_leq_n_in_mod_n_list in H1. auto.
Qed. 

Lemma in_mod_list_nonzero:
    forall (n : nat)(x : Z), 
    prime (Z.of_nat (S n)) /\ In x (mod_n_list n) ->
    x mod (Z.of_nat (S n)) <> 0.
Proof.
    intros. inversion H. clear H. apply mod_n_iff_less_n in H1.
    assert (1 <= x < Z.of_nat (S n)). lia.
    apply rel_prime_le_prime in H as Hrp.
    apply Zrel_prime_neq_mod_0. all : auto. lia.
Qed.

(* Here, we prove various lemmas about lists of integers. Namely, we show that
   if all the numbers in the list are nonzero, their product is nonzero as well.
   We also build up to show that permuting the list doesn't change the product. 
   We start by defining a function which takes the product across a list of 
   integers. *)

Fixpoint prod_list (l : list Z) : Z :=
    match l with 
    | nil => 1 
    | cons a l' => a * (prod_list l')
    end.

Lemma prod_mod_n_list_succ:
    forall (n : nat), 
    prod_list (mod_n_list (S n)) =  Z.of_nat (S n) * prod_list (mod_n_list n).
Proof.
    induction n. simpl. auto. rewrite IHn. auto.
Qed.

Lemma prod_list_mod_n_nonzero:
    forall (n : nat)(m : Z), prime m /\ (Z.of_nat n) < m -> 
    0 <> prod_list (mod_n_list n) mod m .
Proof.
    intros. induction n.
    simpl. assert (1 mod m = 1). apply Zmod_small. inversion H. 
    apply prime_ge_2 in H0. lia. rewrite H0. discriminate.
    assert (prod_list (mod_n_list (S n)) =  Z.of_nat (S n) * prod_list (mod_n_list n)).
    apply prod_mod_n_list_succ. rewrite H0. inversion H.
    assert (Z.of_nat n < m) by lia.
    assert (prod_list (mod_n_list n) mod m <> 0). apply Z.neq_sym. apply IHn. tauto.
    apply Z.neq_sym. apply no_zero_divisors_mod_p. 
    assert (0 <= Z.of_nat (S n) < m) by lia.
    apply Zmod_small in H5.
    assert (Z.of_nat (S n) mod m <> 0) by lia. tauto.
Qed.

Lemma prod_is_associative':
    forall (n m : nat)(l l' : list Z), length l = n /\ length l' = m -> 
    prod_list (l ++ l') = prod_list l * prod_list l'.
Proof.
    (* Intuitively, you should induct on the length of l ++ l' *)
    induction n. firstorder.
    unfold length in H. 
    destruct l. assert (prod_list [] = 1) as Hempty.
    simpl. auto. rewrite Hempty. 
    assert ([] ++ l' = l').
    simpl. auto. rewrite H1. lia.
    discriminate.
    firstorder.
    destruct l eqn: Hlist. discriminate.
    simpl. simpl in H. apply eq_add_S with (n:= length l0) (m:= n) in H.
    rewrite IHn with (l := l0)(l' := l')(m := m).
    lia. firstorder.    
Qed.

Lemma prod_is_associative:
    forall (l l' : list Z), prod_list (l ++ l') = prod_list l * prod_list l'.
Proof.
    intros. apply prod_is_associative' with (n := length l)(m := length l'). auto.
Qed.


Lemma permuting_prod_unchanged:
    forall (l' l : list Z), Permutation l l' -> prod_list l = prod_list l'.
Proof.
    induction l'.
    simpl. intros. apply Permutation_sym in H as Hsym.
    apply Permutation_nil in Hsym. rewrite Hsym. simpl; auto.
    intros. apply Permutation_vs_cons_inv in H as Hcons. 
    firstorder. rewrite H0. 
    assert (Permutation l' (x ++ x0)).
    rewrite H0 in H. apply Permutation_sym in H.
    apply Permutation_cons_app_inv in H as Hx.
    apply Hx. apply Permutation_sym in H1.
    rewrite prod_is_associative. simpl. 
    assert (prod_list x * (a * prod_list x0) = a * prod_list x * prod_list x0). lia. 
    rewrite H2. 
    assert (prod_list x * prod_list x0 = prod_list (x ++ x0)).
    rewrite <- prod_is_associative with (l := x)(l' := x0). auto.
    assert (a * prod_list x * prod_list x0 = a * (prod_list x * prod_list x0)).
    lia. rewrite H4. rewrite H3. apply IHl' with (l := (x ++ x0)) in H1. 
    rewrite H1. auto.
Qed.

(* Along similar lines, we show that if you scale every element in a list by
   a, the product across the list is the product of the original list scaled by
   a^(len list). *)

Lemma factor_out_power:
    forall (l : list Z)(a p : Z), p > 1 ->
    prod_list (map (times_a_map a p) l) mod p = 
    ((Zpower_nat a (length l)) * prod_list l) mod p.
Proof.
    induction l.
    intros.
    simpl. auto.
    intros. simpl.
    remember (times_a_map a0 p a) as A.
    remember (prod_list ( map (times_a_map a0 p) l)) as B.
    remember (Zpower_nat a0 (length l)) as C. 
    remember (prod_list l) as D.
    assert (B mod p = C * D mod p).
    specialize IHl with (a:=a0)(p := p). firstorder. rewrite <- HeqB in H0.
    rewrite <- HeqC in H0. apply H0.
    unfold times_a_map in HeqA. unfold times_a in HeqA.
    rewrite HeqA.
    assert ((a0 * C * (a * D)) = (a0 * a) * C * D). lia. rewrite H1.
    rewrite Zmult_mod_idemp_l. rewrite <- mod_is_homomorphic_mult; auto.
    rewrite H0. rewrite mod_is_homomorphic_mult; auto.
    assert (a0 * a * (C * D) = a0 * a * C * D).
    lia. rewrite H2. auto.
Qed.

(* At some point, we will want to show that multiplication by nonzero a permutes
   the set of nonzero elements in Z/pZ. We will need to prove that the set of
   integers from 1 to n contains no duplicates. *)

Lemma mod_n_list_nodup:
    forall (n : nat), NoDup (mod_n_list n).
Proof.
    induction n. simpl. apply NoDup_nil.
    simpl. apply NoDup_cons.
    assert (Z.pos(Pos.of_succ_nat n) > (Z.of_nat n)). lia.
    assert (~(1 <= Z.pos(Pos.of_succ_nat n) <= Z.of_nat n)).
    lia.
    apply OG_implies_contra with (p := In (Z.pos (Pos.of_succ_nat n)) (mod_n_list n))
    (q := (1 <= Z.pos(Pos.of_succ_nat n) <= Z.of_nat n)). apply mod_n_list_leq_n.
    auto. auto.
Qed.

(* We will also need various lemmas about the list of integers from 1 to n 
   after multiplying every element by some nonzero a in Z/pZ. *)

Lemma times_a_leq_n:
    forall (n : nat)(a x : Z), prime (Z.of_nat n) /\
    a mod (Z.of_nat n) <> 0 /\ x mod (Z.of_nat n) <> 0 -> 
    1 <= times_a_map a (Z.of_nat(n)) x < (Z.of_nat n). 
Proof.
    intros. unfold times_a_map. unfold times_a. simpl in H.
    assert (0 <= (a * x) mod (Z.of_nat n) < (Z.of_nat n)).
    apply Z_mod_lt. inversion H. inversion H1. apply prime_ge_2 in H0. lia.
    assert ((a * x) mod Z.of_nat (n) <> 0).
    apply no_zero_divisors_mod_p in H. apply H.
    lia.
Qed.

Lemma times_a_in_mod_n:
    forall (n : nat)(a x : Z), 
    prime (Z.of_nat (S n)) /\ In a (mod_n_list n) /\ In x (mod_n_list n) -> 
    In (times_a_map a (Z.of_nat (S n)) x) (mod_n_list n).
Proof.
    intros. inversion H. inversion H1. clear H. clear H1.
    assert (a mod Z.of_nat (S n) <> 0) as Hanz. 
    apply in_mod_list_nonzero. auto.
    assert (x mod Z.of_nat (S n) <> 0) as Hxnz.
    apply in_mod_list_nonzero. auto.
    assert (1 <= times_a_map a (Z.of_nat(S n)) x < (Z.of_nat (S n))).
    apply times_a_leq_n. auto. apply mod_n_iff_less_n. lia.
Qed.

Lemma times_a_map_inj:
    forall (a m x y : Z), 
    x mod m <> y mod m /\ a mod m <> 0 /\ prime m -> 
    times_a_map a m x <> times_a_map a m y.
Proof.
    intros. 
    unfold times_a_map.
    unfold times_a.
    apply OG_implies_contra with (q := ~(x mod m <> y mod m)). 
    intros.
    apply inverses_are_unique_mod_prime in H0.
    inversion H.
    contradiction.
    inversion H. inversion H2. assumption.
    inversion H. inversion H2.
    assert (0 <> a mod m).
    lia. assumption.
    apply double_neg.
    inversion H.
    assumption.
Qed.


Lemma succ_not_in_times_a_list:
    forall (n k: nat)(a m: Z), 
    prime m /\ a mod m <> 0 /\ m > (Z.of_nat n) /\
    (Z.of_nat k) < (Z.of_nat n) ->
    ~In (times_a_map a m (Z.of_nat n))
    (map (times_a_map a m) (mod_n_list k)).
Proof.
    intros. induction k. simpl in H. simpl. auto. 
    simpl.
    assert (S k <> n).
    lia. apply deMorgan with 
    (P := times_a_map a m (Z.pos (Pos.of_succ_nat k)) =
    times_a_map a m (Z.of_nat n))
    (Q := In (times_a_map a m (Z.of_nat n))
    (map (times_a_map a m) (mod_n_list k))).
    split.
    assert (0 <= Z.of_nat(S k) < m). lia.
    assert (0 <= Z.of_nat(n) < m). lia.
    apply Zmod_small in H1.
    apply Zmod_small in H2.
    assert (Z.of_nat (S k) <> Z.of_nat n). lia.
    assert (Z.of_nat(S k) mod m <> (Z.of_nat n) mod m).
    rewrite <- H2 in H3.
    rewrite <- H1 in H3. auto.
    apply times_a_map_inj with 
    (a := a)(m := m)(x := Z.of_nat(S k))(y := Z.of_nat n).
    split. auto.
    split. inversion H. inversion H6. assumption. apply H. 
    apply IHk. firstorder. lia.
Qed.

(* Putting the above together, we can argue that there are no duplicates in the
   list of integers after multiplying every element by some nonozero a in Z/pZ. 
   It follows from the number theoretic lemmas we proved earlier that inverses
   exist and are unique. In other words, multiplication by a is a bijection for
   nonzero a in Z/pZ. *)

Lemma times_a_list_nodup:
    forall (n : nat)(a m: Z), 
    prime m /\ a mod m <> 0 /\ m > (Z.of_nat n) ->
    NoDup(map (times_a_map a m) (mod_n_list n)).
Proof.
    induction n. simpl. intros. apply NoDup_nil.
    intros. simpl. assert (NoDup (map (times_a_map a m) (mod_n_list n))).
    apply IHn. assert (m > Z.of_nat n). lia. firstorder. 
    assert (~In (times_a_map a m (Z.pos (Pos.of_succ_nat n)) ) 
    (map (times_a_map a m) (mod_n_list n))). 
    apply succ_not_in_times_a_list with (k := n)(n := S n).
    assert (Z.of_nat n < Z.of_nat (S n)) by lia. tauto.
    apply NoDup_cons. auto. auto.
Qed.

(* In this section, we want to show that you are in the list of integers from 
   1 to n if and only if you are in the integers a, 2a, ..., (p-1)a modulo p
   for a prime p. We start with the forward direction: *)

Lemma in_mod_implies_in_times_a:
    forall (n : nat)(a x m: Z),
    prime m /\ rel_prime a m /\ Z.of_nat(n) < m /\
    In x (mod_n_list n) ->
    In x (map (times_a_map a m) (mod_n_list (Z.to_nat(m - 1)))).
Proof.
    induction n. intros. simpl in H. lia.
    intros. inversion H. inversion H1. inversion H3.
    clear H. clear H1. clear H3. simpl in H5.
    destruct H5 as [Ha|Hb].
    apply in_map_iff.
    unfold times_a_map.
    unfold times_a.
    assert(exists w, (a * w) mod m = x mod m /\ rel_prime w m).
    apply units_form_gp_mod_prime'.
    split. assumption.
    split. assumption. lia. inversion H. inversion H1. 
    assert (In (x0 mod m) (mod_n_list (Z.to_nat (m-1)))).
    assert (rel_prime (x0 mod m) m).
    apply rel_prime_mod. lia. assumption.
    assert(0 <= (x0 mod m) < m). apply Z_mod_lt. lia.
    assert(x0 mod m <> 0). apply Zrel_prime_neq_mod_0. lia.
    assumption.
    assert(1 <= x0 mod m <= m - 1). lia.
    apply if_leq_n_in_mod_n_list with (n := Z.to_nat(m-1))(i := (x0 mod m)).
    assert(Z.of_nat(Z.to_nat(m-1)) = m-1). lia. lia.
    assert( (a * (x0 mod m)) mod m = x mod m).
    rewrite Zmult_mod_idemp_r. assumption.
    assert(Z.pos(Pos.of_succ_nat n) = Z.of_nat(S n)). lia.
    rewrite H8 in Ha.
    assert(x < m). lia.
    assert(x mod m = x). 
    assert(0 <= x). lia. assert(0 <= x < m). lia. apply Zmod_small.
    assumption. rewrite H10 in H7.
    remember(x0 mod m) as w.
    assert(((a * w) mod m = x) /\ 
    (In w (mod_n_list (Z.to_nat (m - 1))))). 
    split. assumption. assumption.
    eexists. apply H11.
    apply IHn.  
    split. assumption.
    split. assumption. split. lia. assumption.
Qed.

Lemma in_mod_implies_in_times_a':
    forall (n : nat)(a x : Z),
    prime (Z.of_nat(S n)) /\ rel_prime a (Z.of_nat(S n)) /\ 
    Z.of_nat(n) < (Z.of_nat(S n)) /\ In x (mod_n_list n) ->
    In x (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n)).
Proof.
    intros. 
    assert(In x (map (times_a_map a (Z.of_nat (S n))) 
    (mod_n_list (Z.to_nat (Z.of_nat (S n) - 1))))).
    assert((Z.to_nat (Z.of_nat (S n) - 1)) = n). lia.
    apply in_mod_implies_in_times_a with (m := Z.of_nat(S n))(n := n)
    (a := a)(x := x). split. inversion H. assumption.
    inversion H. assumption.  
    assert(Z.to_nat (Z.of_nat (S n) - 1) = n). lia.
    rewrite H1 in H0. assumption.
Qed.

(* Here, we prove the reverse direction. *)

Lemma in_times_a_imp_nonzero:
    forall (n : nat)(a x m : Z), 
    prime m /\ Z.of_nat(n) < m /\ rel_prime a m /\
    In x (map (times_a_map a m) (mod_n_list n)) ->
    x <> 0.
Proof.
    induction n. intros. simpl in H. lia.
    intros. inversion H. inversion H1. inversion H3.
    clear H. clear H1. clear H3. simpl in H5. 
    destruct H5 as [Ha|Hb].
    unfold times_a_map in Ha. unfold times_a in Ha.
    assert(x <> 0).
    rewrite <- Ha.
    assert(Z.pos(Pos.of_succ_nat n) = Z.of_nat(S n)). lia.
    rewrite H. assert(Z.of_nat(S n) <> 0). lia.
    assert(a mod m <> 0).
    assert(1 < m). lia.
    apply Zrel_prime_neq_mod_0. assumption. assumption.
    assert(Z.of_nat(S n) mod m <> 0).
    assert(0 <= Z.of_nat(S n) < m). split. lia. assumption.
    assert(Z.of_nat(S n) mod m = Z.of_nat(S n)).
    apply Zmod_small. lia. rewrite H6. assumption.
    apply no_zero_divisors_mod_p. split. assumption.
    split. assumption. assumption. lia.
    apply IHn with (a := a)(m := m). split.
    assumption. split. lia. split. assumption. assumption. 
Qed.

Lemma in_times_a_implies_small:
    forall (n: nat)(a x m: Z),
    prime m /\ Z.of_nat(n) < m /\ rel_prime a m /\
    In x (map (times_a_map a m) (mod_n_list n)) ->
    1 <= x < m. 
Proof.
    induction n. intros. simpl in H. lia.
    intros. inversion H. clear H. inversion H1. clear H1. inversion H2. clear H2.
    simpl in H3. destruct H3 as [Ha|Hb].
    unfold times_a_map in Ha. unfold times_a in Ha.
    assert(Z.pos (Pos.of_succ_nat n) = Z.of_nat(S n)). lia.
    rewrite H2 in Ha. 
    assert(0 <= (a * Z.of_nat (S n)) mod m < m).
    apply Z_mod_lt. lia. rewrite Ha in H3.
    assert(x <> 0). rewrite <- Ha.
    assert(Z.of_nat(S n) <> 0). lia.
    assert(a mod m <> 0).
    assert(1 < m). lia.
    apply Zrel_prime_neq_mod_0. assumption. assumption.
    assert(Z.of_nat(S n) mod m <> 0).
    assert(0 <= Z.of_nat(S n) < m). split. lia. assumption.
    assert(Z.of_nat(S n) mod m = Z.of_nat(S n)).
    apply Zmod_small. lia. rewrite H7. assumption.
    apply no_zero_divisors_mod_p. split. assumption.
    split. assumption. assumption. lia.
    apply IHn with (a := a). split.
    assumption. split. lia. split. assumption. assumption. 
Qed.

Lemma in_times_a_implies_small':
    forall (n: nat)(a x: Z),
    prime(Z.of_nat(S n)) /\ rel_prime a (Z.of_nat(S n)) /\
    In x (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n)) ->
    In x (mod_n_list n).
Proof.
    intros. assert(1 <= x < Z.of_nat(S n)).
    apply in_times_a_implies_small with (m := Z.of_nat(S n))(n := n)(a := a).
    split. inversion H. assumption. split. lia. inversion H. assumption. 
    assert(1 <= x <= Z.of_nat(n)). lia.
    apply if_leq_n_in_mod_n_list. assumption.
Qed.

(* Putting everything together, we get the equivalence statement. *)

Lemma mod_n_iff_times_a:
    forall (n : nat)(a x : Z),
    prime (Z.of_nat(S n)) /\ rel_prime a (Z.of_nat(S n)) ->
    In x (mod_n_list n) <-> 
    In x (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n)).
Proof.
    intros.
    split.
    intros. inversion H.
    apply mod_n_iff_less_n in H0.
    apply if_leq_n_in_mod_n_list in H0.
    assert(In x (map (times_a_map a (Z.of_nat(S n)))
    (mod_n_list( Z.to_nat (Z.of_nat (S n) - 1))))).
    apply in_mod_implies_in_times_a with (m := Z.of_nat(S n))
    (n := n). split. assumption. split. assumption. split. lia.
    assumption. 
    assert(Z.to_nat (Z.of_nat (S n) - 1) = n). lia.
    rewrite H4 in H3. assumption.
    intros. assert(x <> 0). apply in_times_a_imp_nonzero with 
    (m:= Z.of_nat (S n))(n := n)(a := a). split. inversion H.
    assumption. split. lia. split. inversion H. assumption. assumption.
    apply in_times_a_implies_small' with (n := n)
    (a := a)(x := x). split. inversion H.  assumption. 
    split. inversion H.  assumption. assumption.
Qed.

(* We apply the number theoretic and list lemmas we proved earlier to show that
   multiplication by nonzero a in Z/pZ simply permutes the nonzero elements of 
   Z/pZ. *)

Lemma mult_by_a_permutes:
    forall (a : Z)(n : nat), 
    prime (Z.of_nat(S n)) /\ rel_prime a (Z.of_nat(S n)) -> 
    Permutation (mod_n_list n) (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n)).
Proof.
    intros.
    remember (mod_n_list n) as lmod.
    remember (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n)) as almod.
    assert (NoDup (mod_n_list n)).
    apply mod_n_list_nodup.
    assert (NoDup (map (times_a_map a (Z.of_nat(S n))) (mod_n_list n))).
    apply times_a_list_nodup.
    assert (a mod (Z.of_nat(S n)) <> 0).
    apply Zrel_prime_neq_mod_0. inversion H. 
    apply prime_ge_2 in H1 as Hge. lia. tauto.
    assert ((Z.of_nat(S n)) > Z.of_nat n). lia. tauto. 
    assert (forall x:Z, In x lmod <-> In x almod).
    intros. rewrite Heqlmod.  rewrite Heqalmod. 
    apply mod_n_iff_times_a.
    inversion H. split. assumption. 
    assert (Z.of_nat n < (Z.of_nat(S n))).
    lia. assumption. inversion H.
    apply NoDup_Permutation. rewrite <- Heqlmod in H0.
    auto. rewrite <- Heqlmod in H1. auto. 
    rewrite <- Heqlmod in Heqalmod. 
    rewrite <- Heqalmod.
    auto.
Qed.

(* We use the above lemmas to argue that the integers from 1 to n have the same 
   product if you were to scale everything by a in Z/pZ and take the product. *)

Lemma prod_a_list_eq_mod_n:
    forall (a : Z)(n : nat),
    prime (Z.of_nat (S n)) /\ rel_prime a (Z.of_nat (S n)) ->
    prod_list (mod_n_list n) = prod_list (map (times_a_map a (Z.of_nat (S n))) (mod_n_list n)).
Proof.
    intros.
    assert (Permutation (mod_n_list n) (map (times_a_map a (Z.of_nat (S n))) (mod_n_list n))).
    apply mult_by_a_permutes. auto.
    apply permuting_prod_unchanged with 
    (l := mod_n_list n)(l' := map (times_a_map a (Z.of_nat (S n))) (mod_n_list n)).
    auto.
Qed.

(* Putting everything together, we can prove our main theorem. *)

Theorem Fermat's_Little_Theorem:
    forall (a: Z) (p: nat), prime (Z.of_nat (S p)) /\ a mod (Z.of_nat (S p)) <> 0 -> 
    Zpower_nat a p mod (Z.of_nat (S p)) = 1.
Proof.
    intros.
    assert (rel_prime (Z.of_nat (S p)) a) as Hrelprime.
    assert (~((Z.of_nat (S p)) | a)). apply Zdivide_mod_conv. tauto. 
    apply prime_rel_prime; tauto.
    assert (Zpower_nat a p <> 0) as Hnz. apply exp_nonzero. inversion H.
    assert ((a = 0) -> False). intro. rewrite H2 in H1.
    assert (0 mod Z.of_nat (S p) = 0). apply Zmod_small. lia. rewrite H3 in H1. 
    contradiction. assumption.
    assert (prod_list 
    (map (times_a_map a (Z.of_nat (S p))) (mod_n_list p)) mod (Z.of_nat (S p)) = 
    ((Zpower_nat a (length (mod_n_list p))) * prod_list (mod_n_list p)) mod Z.of_nat(S p)).
    apply factor_out_power. inversion H. apply prime_ge_2 in H0 as Hge. lia.
    assert (length (mod_n_list p) = p). 
    apply length_mod_n_list. rewrite H1 in H0.
    assert (prod_list (mod_n_list p) = 
    prod_list (map (times_a_map a (Z.of_nat (S p))) (mod_n_list p))).
    apply prod_a_list_eq_mod_n with (a := a)(n := p).
    split. tauto. apply rel_prime_sym in Hrelprime. auto.
    remember (prod_list (map (times_a_map a (Z.of_nat (S p))) (mod_n_list p))) as A.
    remember (prod_list (mod_n_list p)) as B.
    remember (Zpower_nat a p) as C.
    rewrite H2 in H0. 
    assert (A * 1 = A). lia.
    assert (A * C = (C * (A * 1))). lia.
    rewrite <- H3 in H0. rewrite <- H4 in H0. 
    assert (1 mod (Z.of_nat (S p)) = 1). apply Zmod_small. 
    inversion H. apply prime_ge_2 in H5 as Hge. lia. rewrite <- H5.
    apply inverses_are_unique_mod_prime with (a := A)(c := 1)(b := C).
    apply H. rewrite <- H2. rewrite HeqB. inversion H.
    apply prod_list_mod_n_nonzero with (m := Z.of_nat (S p)). split. tauto. lia.
    lia.
Qed.
---
layout: post
title: Coq Lemmas
usemathjax: true
---

## Useful Coq Commands

### `Search`

(from Software Foundations)

> Coq's `Search` command is quite helpful with this.  Let's say you've forgotten the name of a theorem about `rev`.  The command `Search rev` will cause Coq to display a list of all theorems involving `rev`.
<br><br>
 ```Search rev.```
<br><br>
 Or say you've forgotten the name of the theorem showing that plus is commutative.  You can use a pattern to search for all theorems involving the equality of two additions.
<br><br>
 ```Search (_ + _ = _ + _).```
<br><br>
 You'll see a lot of results there, nearly all of them from the standard library.  To restrict the results, you can search inside a particular module:
<br><br>
 ```Search (_ + _ = _ + _) inside Induction.```
<br><br>
 You can also make the search more precise by using variables in the search pattern instead of wildcards:
<br><br>
 ```Search (?x + ?y = ?y + ?x).```
<br><br>
 The question mark in front of the variable is needed to indicate that it is a variable in the search pattern, rather than a variable that is expected to be in scope currently.

Search only lemmas(works for `Theorem`, `Example`, `Definition`, etc.):

```coq
Search is:Lemma (_ + _ = _ + _)
```

### `Check x`

Displays the type of term. When called in proof mode, the term is checked in the local context of the selected goal (possibly by using single numbered goal selectors).

Use `@def` to force implicit arguments of `def` be passed explicitly. For example, 

```coq
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y → x = y.
```

Note that the braces `{}` indicate that the types of the function, `A, B` should be inferred. `Check`ing without @ yields:

```coq
> Check injective.
injective
: (?A -> ?B) -> Prop
where
?A : [ |- Type]
?B : [ |- Type]
```
The first argument automatically expects some function with type `A -> B` with both being inferred.

Let's now check `@injective` with applying `A = nat` :

```coq
Check @injective nat.
@injective nat
: forall B : Type, (nat -> B) -> Prop
```
Now it expects some type `B` and a function with type `nat -> B`. 

### `Locate "x"`

Search the definition of a notation. For example,

```coq
> Locate "=?"

Notation "x =? y" := (eqb x y) : nat_scope (default interpretation)
Notation "x =? y" := (String.eqb x y) : string_scope 
```

Lemmas marked with '*' are my personal lemmas.

## Nat

### `plus_n_0`
```coq
forall n:nat, n = n + 0.
```

### `plus_0_n`
```coq
forall n:nat, 0 + n = n.
```

### `plus_n_Sm`
```coq
forall n m:nat, S (n + m) = S n + S m.
```

### `plus_sn_m`
```coq
forall n m:nat, S n + m = S (n + m).
```

### `mult_n_0`
```coq
forall n:nat, 0 = n * 0.
```

### `mult_n_Sm`
```coq
forall n m:nat, n * m + n = n * S m.
```

### `succ_eql_add1`*
```coq
Theorem succ_eql_add1 : forall n : nat,
  1 + n = S n.
Proof.
  reflexivity.
Qed.
```

### `add_comm`*
```coq
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
    - induction m as [| m' IHm'].
        * simpl. reflexivity.
        *  simpl. rewrite <- IHm'. simpl. reflexivity.
    - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.
```

### `add_assoc`*
```coq
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.
```

### `mult_comm`*
```coq
Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
    - simpl. rewrite -> mul_0_r. reflexivity.
    - simpl.
      rewrite -> IHn'.
      rewrite <- mult_n_Sm.
      rewrite -> add_comm.
      reflexivity.
Qed.
```

### `mult_assoc`*
```coq
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  rewrite -> mult_comm.
  induction p as [| p' IHp'].
    - rewrite -> mul_0_r. rewrite -> mult_0_l.
      rewrite -> mult_comm. rewrite -> mult_0_l. reflexivity.
    - rewrite <- mult_n_Sm. rewrite <- mult_n_Sm. rewrite -> mult_plus_distr_r.
      rewrite -> IHp'.
      assert (m * n = n * m). {
        rewrite -> mult_comm. reflexivity.
      }
      rewrite -> H.
      reflexivity.
Qed.
```

### `leb_n_Sn`*
```coq
Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.
Qed.
```

### `le_trans`*
```coq
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros H.
  intros H1.
  transitivity n.
    - apply H.
    - apply H1.
Qed.
```

### `O_le_n`*
```coq
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
    - apply le_n.
    - apply le_S. apply IHn.
Qed.
```

### `n_le_m__Sn_le_Sm`*
```coq
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m.
  intros H.
  induction H.
    - apply le_n.
    - apply le_S. apply IHle.
Qed.
```

### `Sn_le_Sm__n_le_m`*
```coq
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.
  intros H.
  inversion H.
    - apply le_n.
    - rewrite <- H1. apply le_S. apply le_n.
Qed.
```

### `lt_ge_cases`*
```coq
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  induction n.
    - destruct m eqn:Eqm.
      + right. apply le_n.
      + left. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
    - unfold lt in IHn. destruct IHn. 
      + unfold lt. destruct m.
        * right. apply O_le_n.
        * apply Sn_le_Sm__n_le_m in H. inversion H.
          ** right. rewrite <- H0. apply le_n.
          ** left. apply n_le_m__Sn_le_Sm. apply n_le_m__Sn_le_Sm. apply H0.
      + inversion H.
        * right. apply le_S. apply le_n.
        * right. rewrite H1. rewrite <- H1. apply le_S. apply le_S. apply H0.
Qed.
```

### `le_plus_l`*
```coq
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a.
  induction a.
    - simpl. intros b. apply O_le_n.
    - intros b. simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.
```

### `plus_le`*
```coq
Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m.
  intros H.
  inversion H.
    - split.
      + apply le_plus_l.
      + rewrite add_comm. apply le_plus_l.
    - split.
      + induction n2.
        * rewrite add_comm in H. simpl in H. rewrite <- H1 in H. apply H.
        * rewrite add_comm in H. simpl in H. rewrite add_comm in H. apply le_S in H.
          apply Sn_le_Sm__n_le_m in H. apply IHn2 in H. apply H.
          (* Now prove second antecedent of IHn1*)
          rewrite add_comm in H0. simpl in H0. rewrite add_comm in H0. apply le_S in H0.
          apply Sn_le_Sm__n_le_m in H0. apply H0.
      + induction n1.
        * simpl in H. rewrite <- H1 in H. apply H.
        * simpl in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply IHn1 in H.
          apply H.
          (* Now prove second antecedent of IHn1*)
          simpl in H0. apply le_S in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.
```

### `add_le_cases`*
```coq
Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
  intros n m p q.
  intros H.
  generalize dependent m.
  generalize dependent p.
  generalize dependent q.
  induction n as [| n' IHn'].
    - intros q p m. simpl. intros H. left. apply O_le_n.
    - intros q p m. intros H. destruct p.
      + apply plus_le in H. destruct H. simpl in H0.
        right. apply H0.
      + simpl in H. apply Sn_le_Sm__n_le_m in H. apply IHn' in H. destruct H.
        * left. apply n_le_m__Sn_le_Sm. apply H.
        * right. apply H.
Qed.
```

### `plus_le_compat_l`*
```coq
Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n.
  induction n.
    - intros m p. intros H. rewrite add_comm. simpl. apply le_plus_l.
    - intros m p. intros H. inversion H.
      + apply le_n.
      + rewrite add_comm. rewrite add_comm with (m := S m0). simpl.
        apply n_le_m__Sn_le_Sm. rewrite add_comm. rewrite add_comm with (n := m0).
        apply IHn. apply le_S in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.
```

### `plus_le_compat_r`*
```coq
Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n.
  induction n.
    - intros m p. intros H. simpl. rewrite add_comm. apply le_plus_l.
    - intros m p. intros H. destruct m.
      + inversion H.
      + apply Sn_le_Sm__n_le_m in H. apply (IHn _ p) in H.
        simpl. apply n_le_m__Sn_le_Sm. apply H.
Qed.
```

### `le_plus_trans`*
```coq
Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n.
  induction n.
    - intros m p. intros H.
      apply O_le_n.
    - intros m p H. destruct m.
      + inversion H.
      + apply Sn_le_Sm__n_le_m in H. apply (IHn _ p) in H.
        simpl. apply n_le_m__Sn_le_Sm. apply H.
Qed.
```

### `n_lt_m__n_le_m`*
```coq
Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n.
  induction n.
    - intros m H.
      apply O_le_n.
    - intros m H.
      unfold lt in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H.
      apply H.
Qed.
```

### `plus_lt`*
```coq
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2.
  induction n1.
    - intros m.
      simpl. intros H. destruct m.
        + unfold lt in *. inversion H.
        + split.
          * unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
          * apply H.
    - intros m H. destruct m.
      + inversion H.
      + simpl in H. unfold lt in *. apply Sn_le_Sm__n_le_m in H. apply IHn1 in H.
        destruct H. split.
          * apply n_le_m__Sn_le_Sm. apply H.
          * apply le_S in H0. apply H0.
Qed.
```

### `le_any`*
```coq
Lemma le_any : forall (n m p : nat),
  n <= m -> n <= m + p.
Proof.
  intros n m p.
  generalize dependent n.
  generalize dependent m. 
  induction p.
    - intros . rewrite <- plus_n_O. apply H.
    - intros . rewrite <- plus_n_Sm. rewrite <- plus_Sn_m. apply IHp. 
      apply le_S in H. apply H.
Qed.
```

## Lists

### `app_nil_nil`*
```coq
Lemma app_nil_nil: forall T (l m : list T),
  l ++ m = [] -> l = [] /\ m = [].
Proof.
  intros T. intros l.
  induction l.
    - intros . simpl in *. split. reflexivity. apply H.
    - intros . simpl in *. inversion H.
Qed.
```

## Bool
### `eqb_subst`
```coq
forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
```

### `eqb_reflx`
```coq
forall b:bool, eqb b b = true.
```

### `eqb_prop`
```coq
forall a b:bool, eqb a b = true -> a = b.
```

### `eqb_true_iff`
```coq
forall a b:bool, eqb a b = true <-> a = b.
```

### `eqb_false_iff`
```coq
forall a b:bool, eqb a b = false <-> a <> b.
```

### `negb_orb`
De Morgan
```coq
forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
```

### `negb_andb`
De Morgan
```coq
forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
```

### `orb_comm`
```coq
forall b1 b2:bool, b1 || b2 = b2 || b1.
```

### `orb_assoc`
```coq
forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
```

### `andb_comm`
```coq
forall b1 b2:bool, b1 && b2 = b2 && b1.
```

### `andb_assoc`
```coq
forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
```

### `f_equal`
```coq
forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
```
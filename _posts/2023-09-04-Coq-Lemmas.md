---
layout: post
title: Coq Lemmas
usemathjax: true
---

## Using Coq's `Search`

(from Software Foundations)

> Coq's [Search] command is quite helpful with this.  Let's say you've forgotten the name of a theorem about [rev].  The command [Search rev] will cause Coq to display a list of all theorems involving [rev].

> ```Search rev.```

> Or say you've forgotten the name of the theorem showing that plus is commutative.  You can use a pattern to search for all theorems involving the equality of two additions.

> ```Search (_ + _ = _ + _).```

> You'll see a lot of results there, nearly all of them from the standard library.  To restrict the results, you can search inside a particular module:

> ```Search (_ + _ = _ + _) inside Induction.```

> You can also make the search more precise by using variables in the search pattern instead of wildcards:

> ```Search (?x + ?y = ?y + ?x).```

> The question mark in front of the variable is needed to indicate that it is a variable in the search pattern, rather than a variable that is expected to be in scope currently.

Search only lemmas(works for `Theorem`, `Example`, `Definition`, etc.):

```Search is:Lemma (_ + _ = _ + _)```

## Nat
Lemmas marked with '*' are not in `Coq.Init.Peano`.
### `plus_n_0`
```
forall n:nat, n = n + 0.
```

### `plus_0_n`
```
forall n:nat, 0 + n = n.
```

### `plus_n_Sm`
```
forall n m:nat, S (n + m) = n + S m.
```

### `plus_sn_m`
```
forall n m:nat, S n + m = S (n + m).
```

### `mult_n_0`
```
forall n:nat, 0 = n * 0.
```

### `mult_n_Sm`
```
forall n m:nat, n * m + n = n * S m.
```

### `succ_eql_add1`*
```
Theorem succ_eql_add1 : forall n : nat,
  1 + n = S n.
Proof.
  reflexivity.
Qed.
```

### `add_comm`*
```
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
```
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
```
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
```
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
```
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

## Bool
Lemmas marked with * are not in `Coq.Bool.Bool`
### `eqb_subst`
```
forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
```

### `eqb_reflx`
```
forall b:bool, eqb b b = true.
```

### `eqb_prop`
```
forall a b:bool, eqb a b = true -> a = b.
```

### `eqb_true_iff`
```
forall a b:bool, eqb a b = true <-> a = b.
```

### `eqb_false_iff`
```
forall a b:bool, eqb a b = false <-> a <> b.
```

### `negb_orb`
De Morgan
```
forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
```

### `negb_andb`
De Morgan
```
forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
```

### `orb_comm`
```
forall b1 b2:bool, b1 || b2 = b2 || b1.
```

### `orb_assoc`
```
forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
```

### `andb_comm`
```
forall b1 b2:bool, b1 && b2 = b2 && b1.
```

### `andb_assoc`
```
forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
```
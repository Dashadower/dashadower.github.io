---
layout: post
title: Coq Lemmas
usemathjax: true
---

## Nat

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

### `add_comm`
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

### `add_assoc`
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

## Bool

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
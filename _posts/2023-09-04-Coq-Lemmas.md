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

## Nat
Lemmas marked with '*' are not in `Coq.Init.Peano`.
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

## Bool
Lemmas marked with * are not in `Coq.Bool.Bool`
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
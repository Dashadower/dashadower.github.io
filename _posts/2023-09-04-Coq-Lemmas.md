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

### `plus_le_cases_middle`*
```coq
Lemma plus_le_cases_middle : forall (n m p q : nat),
  (* This is my lemma that encapsulates LEM for le *)
  n + m <= p + q -> (n <= p /\ m <= q) \/ (n <= p /\ m > q) \/ (n > p /\ m <= q).
Proof.
  intros n m p.
  generalize dependent m.
  generalize dependent n.
  induction p.
    - simpl. intros n. induction n.
      + simpl in *. intros . left. split. apply le_n. apply H.
      + intros . simpl in H. rewrite plus_n_Sm in H. apply IHn in H as H1.
        destruct H1.
          * destruct H0. right. right. split. unfold gt. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
            apply le_S in H1. apply Sn_le_Sm__n_le_m in H1. apply H1.
          * destruct H0.
            ** destruct H0. right. right. split. unfold gt. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
               apply plus_le in H. destruct H. apply le_S in H2. apply Sn_le_Sm__n_le_m in H2. apply H2.
            ** destruct H0. right. right. split. unfold gt. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
               apply plus_le in H. destruct H. apply le_S in H2. apply Sn_le_Sm__n_le_m in H2. apply H2.
    - intros n. induction n.
      + intros. simpl in *. rewrite plus_n_Sm in H. apply (IHp 0 _ _) in H. destruct H.
        * destruct H. destruct q.
          ** inversion H0. right. left. split. apply le_S. apply O_le_n. unfold gt. unfold lt. apply le_n.
             left. split. apply O_le_n. apply H2.
          ** inversion H0. right. left. split. apply O_le_n. unfold gt. unfold lt. apply le_n. left. split. apply O_le_n. apply H2.
        * destruct H.
          ** destruct H. right. left. split. apply O_le_n. unfold gt in *. unfold lt in *. apply le_S in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
          ** destruct H. inversion H0. right. left. split. apply O_le_n. unfold gt. unfold lt. apply le_n.
             left. split. apply O_le_n. apply H2.
      + intros. simpl in H. apply Sn_le_Sm__n_le_m in H. apply IHp in H. destruct H.
        * destruct H. left. split. apply n_le_m__Sn_le_Sm. apply H. apply H0.
        * destruct H.
          ** destruct H. right. left. split. apply n_le_m__Sn_le_Sm. apply H. apply H0.
          ** destruct H. right. right. split. unfold gt in *. unfold lt in *. apply n_le_m__Sn_le_Sm. apply H. apply H0.
Qed.
```

### `add_le_trans`*
```coq
Lemma add_le_trans : forall (n m p q : nat),
  n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q.
  generalize dependent p.
  induction q.
    - intros. inversion H0. rewrite <- plus_n_O. rewrite <- plus_n_O. apply H. 
    - intros. destruct p.
      + rewrite <- plus_n_O. apply le_any. apply H.
      + rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply n_le_m__Sn_le_Sm. apply IHq.
        * apply H.
        * apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.
```


### `le_Sn_le_stt`*
```coq
Lemma le_Sn_le_stt : forall (n m : nat),
  S n <= m -> n <= m.
Proof.
  intros.
  generalize dependent n.
  induction m.
    - intros. inversion H.
    - intros. apply Sn_le_Sm__n_le_m in H. apply le_S in H. apply H.
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

### `subseq_len_le_nat`*
```coq
Lemma subseq_len_le_nat : forall (ls l : list nat),
  subseq ls l -> length ls <= length l.
Proof.
  intros.
  induction H.
    - apply le_n.
    - simpl. apply le_S. apply IHsubseq.
    - simpl. apply n_le_m__Sn_le_Sm. apply IHsubseq.
Qed.
```

### `filter_le_l`*
```coq
Lemma filter_le_l : forall (X : Type) (n : nat) (l : list X) (test : X -> bool),
  n <= length (filter test l) -> n <= length l.
Proof.
  intros X.
  intros n l test.
  generalize dependent n.
  induction l.
    - simpl. intros. apply H.
    - intros. simpl. destruct n.
      + apply O_le_n.
      + simpl in H. destruct (test x) eqn:Eqtx.
        * simpl in H. apply n_le_m__Sn_le_Sm. apply Sn_le_Sm__n_le_m in H. apply IHl.
          apply H.
        * apply n_le_m__Sn_le_Sm. apply IHl. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.
```

### `subseq_head_eq`*
```coq
Lemma subseq_head_eq : forall (l1 l2 : list nat) (n : nat),
  subseq (n :: l1) (n :: l2) -> subseq l1 l2.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent n.
  induction l2.
    - intros. inversion H. inversion H2. inversion H1. apply subseq_nil. 
    - intros. inversion H.
      + inversion H2.
        * apply subseq_head_r. apply (subseq_head_r _ _ n) in H6. apply IHl2 in H6. apply H6.
        * apply subseq_head_r. apply H5.
      + apply H1.
Qed.
```

### `l_eq_nil`*
```coq
Lemma l_eq_nil : forall (X : Type) (l : list X) (x : X),
  l ++ [x] = [] -> False.
Proof.
  intros.
  induction l.
    - inversion H.
    - simpl in *. inversion H.
Qed.
```

### `tail_app_eq`*
```coq
Lemma tail_app_eq : forall (X : Type) (l m : list X) (x : X),
  l ++ [x] = m ++ [x] -> l = m.
Proof.
  intros X l.
  induction l.
    - simpl. intros. destruct m. reflexivity. simpl in *. inversion H. symmetry in H2.
      apply l_eq_nil in H2. destruct H2.
    - simpl. intros. destruct m.
        + inversion H. apply l_eq_nil in H2. destruct H2.
        + simpl in H. inversion H. apply IHl in H2. rewrite H2. reflexivity.
Qed.
```

## Bool

### `leb_iff`*
```coq
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
    - intros H. apply leb_complete in H. apply H.
    - intros H. apply leb_correct in H. apply H.
Qed.
```

### `leb_true_trans`*
```coq
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply (le_trans n m o) in H1.
   - apply leb_correct. apply H1.
   - apply H2.
Qed.
```

### `leb_complete`*
```coq
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n.
    - intros m H. apply O_le_n.
    - intros m. intros H.  destruct m.
      + simpl in H. discriminate H.
      + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.
```

### `leb_false_complete`*
```coq
Lemma leb_false_complete : forall (n m : nat),
  (n <=? m) = false -> n > m.
Proof.
  intros n.
  induction n.
    - intros. inversion H.
    - intros. destruct m.
      + unfold gt. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
      + unfold gt in *. unfold lt in *. apply n_le_m__Sn_le_Sm. apply IHn. simpl in H.
        apply H.
Qed.
```

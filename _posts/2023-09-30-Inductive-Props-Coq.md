---
layout: post
title: Inductive Propositions in Coq
usemathjax: true
---

Inductive propositions confused me so much I decided to make a note for it.

## Inductively Defined Types

Standard inductive types creates a base case and a mapping from an object to its "successor". For example the Peano natural numbers:

```
Inductive nat: Type :=
    | O
    | S : nat -> nat.
```
It defines two constructions for `nat`: either `O` or a mapping `S` that takes a `nat` and creates some other `nat`.

## Construction of Types

A definition of a type declares what objects are possible to exist for a given type. Looking at the nat example above, it defines that the set of natural numbers contain `O` and the successor function applied to it (`S O`), again (`S (S 0)`), and so on.

$$
\begin{array}{c}
  n: \mathsf{nat} \\
  \hline
  S \ n: \mathsf{nat}
\end{array}
$$

To show that an object is a member of a type, you must be able to construct the object using the definitions of the type.

## Propositions as Inductive Types

Consider we define even natural numbers:

1. 0 is an even number.
2. If `n` is even, then `S (S n)` is even.

We start at the base case 0, for which we sequentially apply #2 to 
be able to construct the set of all even natural numbers.

To prove that some number `n'` is even, we must show that `n'` is constructible from the above two cases. Informally that means showing the following implication holds:

$$
\forall n: \mathsf{nat}, \ \mathsf{ev} \ n \rightarrow n = 0 \ \vee \mathsf{ev} \ n' \ \wedge \exists n'. 
  \ n = \ S \ (S\  n')
$$

An inductive proposition defines a way to construct *propositions* inductively: either standalone propositions or a mapping that creates another proposition given a proposition. The even example can be expressed in Coq as the following:

```
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

1. `ev_0` defines the base case that 0 is even.
2. `ev_SS` says that given a natural number `n`, and *evidence* `H` that `n` is even, `S (S n)` is even. Evidence here means a way to construct an even number `n`. We can interpret it as:
    $$
    \forall n: \mathsf{nat}, \ \mathsf{ev} \ n \rightarrow \mathsf{ev} \ S \ (S \ n)
    $$
    which happens to be the case right of the logical or in the implication above.

We can verify the conversion by running `Print ev.`, which yields the following output:
```
Inductive ev : nat -> Prop := 
    ev_0 : ev 0 
    | ev_SS : forall n : nat, ev n -> ev (S (S n)).
```

Coq converts the type `nat -> Prop`, where `nat = n, Prop =  ev n -> ev (S (S n)) (-> here is implication)`, into a proposition through curry-howard correspondence. Converting the proposition back to types work the same way:

1. $\forall n: \mathsf{nat}$ becomes a function argument that admints some `nat` as `n`.
2. For the implication $\mathsf{ev} \ n \rightarrow \mathsf{ev} \ S \ (S \ n)$,
    1. The antecedent $\mathsf{ev} \ n$ is created from a function `nat -> Prop` which takes `n` from #1 and returns `ev n`.
    2. The implication is true if a function with type `Prop -> Prop`, which accepts `ev n` from 2-1, returns a type corresponding to the consequent $\mathsf{ev} \ S \ (S \ n)$, `ev S (S n)`.

Note that this implies `ev_SS` having type `nat -> Prop -> Prop`, which is exactly what we defined!

The key takeaway is that for a function that returns `Prop`, there's no distinction between adding props as arguments and adding it to the prop itself with an implication.

## Forward and Backward Reasoning

The concepts of forward/backward reasoning apply identically, depending on whether the inductively defined proposition is in the context or the goal.

If it's in the context, this implies that its construction is possible. This also implies we can apply steps of the induction freely and create *successive* propositions. For the above even example:

$$
\begin{array}{c}
  n: \mathsf{nat} \quad \mathsf{ev} \ n \\
  \hline
  \mathsf{ev} \ S \ (S \ n)
\end{array}
$$

----

If it's in the goal, the problem switches to constructing evidence of the proposition. That means applying an approporiate inductive proposition "backwards", creating a *predecessive* proposition and showing it's true:
$$
\begin{array}{c}
  n: \mathsf{nat} \quad \mathsf{ev} \ S \ (S \ n) \quad \forall n': \mathsf{nat}. \ \mathsf{ev} \ n' \rightarrow \mathsf{ev} \ S \ (S\  n') \\
  \hline
  \mathsf{ev} \ n
\end{array}
$$

## `apply`

If you want to rewrite an inductive proposition to a goal/hypothesis, you must use `apply P (in H)` instead of `rewrite`.

If applying to a goal, it becomes backward reasoning, which transforms the goal into a predecessor proposition.

If applying to a hypothesis in the context, it becomes forward reasoning, which constructs the successive proposition.

## Strategies for Inductive Props

1. `inversion E` - Straightforward. Reason about the evidence cases of the proposition.

2. `induction E` - Induction on evidence. Useful since the induction hypothesis includes the variables involved in the evidence. It normally helps to keep the induction hypothesis as general as possible.
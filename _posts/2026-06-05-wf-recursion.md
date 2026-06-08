---
layout: post
title: Well-founded recursion
usemathjax: true
---

Traditional induction on nat is defined as the following:

\[
/frac{ P \ 0 \quad \forall n. P \ n \rightarrow P \ n + 1 }{ \forall n. P n }
\]

Strong induction assumes \(P\) holds for all nats smaller than \(n\):

\[
/frac{ \forall n. (\forall m. (m < n \rightarrow P \ m)) \rightarrow P n }{ \forall n. P n }
\]

Note that the lessthan operator and the definition of nats are doing the heavy lifting here:
We're relying on the lessthan operator being well-founded, its proof being possible through the inductive structure of nats.

Suppose that there's no direct notion of well-foundness over a type(that is, we're not doing direct recursion on an inductively defined that from which its decreasing subterm can be derived syntactically) and the obligation is up to us define a relation \(R\).

First obligation is to prove that \(R\) is well-founded.

Then we can perform well-founded induction:

\[
\frac{ \forall x. (\forall y. R \ y \ x \rightarrow P \ y) \rightarrow P \ x }{ \forall x. P \ x}
\]

The well-founded relation \(R\) gives us the ability to derive subterm(s) \(y\) from \(x\), which are decreasing and finitely reducible.

In coq you can do this by using `Program Fixpoint` if a measure function that maps to nat is definable. 
Or you can define \(R\),prove \(well_founded R\), pass \(H : Acc R _\) as an arg and declare `struct H` to say the relation itself is the decreasing argument.

```
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
```
Note that `Acc` directly relates from x to "smaller" elements y defined by R. And Acc itself being an indprop encodes the notion of "finite unrolling"

Notes are compressed results of discussions with 임기정 and reading cpdt.generalrec
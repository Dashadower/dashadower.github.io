---
layout: post
title: Dependent Induction in Coq
usemathjax: true
---


## Imp.v

I stepped into a tough problem while solving a Software Foundations exercise. The Imp chapter was gradually building up a simple imperative language, upon which an exercise required me to extend the language with break-able while loops.

The syntax of the language given in the book is simple: 

```coq
Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
```

The language is equipped with standard arithmetic and boolean expressions, with support for `nat`-typed variables.

The operational semantics of the commands are equipped with a `result` type, which indicates whether after running a command, whether the outermost loop should break or not:

```coq
Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).
```

Upon which the semantics are defined:

```coq
Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st x a n,
      aeval st a = n -> st =[CAsgn x a ]=> (x !->n; st) / SContinue
  | E_SeqBreak : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak -> st =[ CSeq c1 c2 ]=> st' / SBreak
  | E_Seq : forall c1 c2 st st' st'' res,
      st =[ c1 ]=> st' / SContinue -> st' =[ c2 ]=> st'' / res -> st =[ CSeq c1 c2 ]=> st'' / res
  | E_IfTrue : forall st st' b c1 c2 res,
      beval st b = true -> st =[ c1 ]=> st' / res -> st =[ CIf b c1 c2 ]=> st' / res
  | E_IfFalse : forall st st' b c1 c2 res,
      beval st b = false -> st =[ c2 ]=> st' / res -> st =[ CIf b c1 c2 ]=> st' / res
  | E_WhileFalse : forall b st c,
      beval st b = false -> st =[ CWhile b c ]=> st / SContinue
  | E_WhileTrueBreak : forall b st st' c,
      beval st b = true -> st =[ c ]=> st' / SBreak ->
      st =[CWhile b c]=> st' / SContinue
  | E_WhileTrue : forall b st st' st'' c,
      beval st b = true -> st =[ c ]=> st' / SContinue -> st' =[CWhile b c]=> st'' / SContinue ->
      st =[CWhile b c]=> st'' / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').
```

---

For example, consider the case `E_WhileTrue`. It says that given the boolean expression `b` is true under state `st`, the loop body `c` excuted at state st yields state `st'` that doesn't signal a break, and from that state `st'` running the loop yields another state `st''` that doesn't signal a break, we can say running a while loop at state `st` yields state `st''`.

It unrolls one iteration of the while loop(`st =[ c ]=> st' / SContinue`) which says that command `c` shouldn't signal a break. The next implication, which seemingly seems like the while loop itself repeated, is where the actually proof of a break occuring should happen. This is because a break signaled to the "unfolded" inner while loop isn't exposed. 

Think like we're peeling a onion layer by layer. The topmost layer is the single iteration, while the remaining unpeeled lump of layers is the remaining while loop ran from state `st`. Very much like a recursive call, we can certify that given the topmost layer(iteration) doesn't signal a break, there must exist some other layer within the lump that signals a break.

### Problem

But the following lemma became an issue:

```coq
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
```

This seemed straightforward by induction on `c`:

```coq
Proof.
  intros.
  induction c.
```

which expectedly exposes 6 subgoals, corresponding to each type of command.

Immediately the first subgoal looks fishy:

```coq
b : bexp
st, st' : state
H : st =[ while b do skip end ]=> st' / SContinue
H0 : beval st' b = true
-------------------------------------------------------
exists st'' : state, st'' =[ skip ]=> st' / SBreak
```

First, the goal is directly unprovable by definition. Under the defined semantics `skip` cannot signal a break.
Fortunately, hypothesis `H` also doesnt make sense; `st = st'` since it's an infinite loop. I immediately call `inversion H`, which creates 3 subgoals for each while-related clause of `ceval`.

1. The first subgoal implies `beval st' b = false`, which creates a contradiction.
2. Second subgoal implies `skip` signals a break, which also creates a contradictin.
3. The third goal, corresponding to `E_WhileTrue` returns the exact same situation before calling inversion:

```coq
b : bexp
st, st' : state
H : st =[ while b do skip end ]=> st' / SContinue
H0 : beval st' b = true
st'0 : state
H3 : beval st b = true
H4 : st =[ skip ]=> st'0 / SContinue
H6 : st'0 =[ while b do skip end ]=> st' / SContinue
-----------------------------------------------------------
exists st'' : state, st'' =[ skip ]=> st' / SBreak
```
(note that `st` equals `st'0` by `H4`).

Unfortunately inversion doesn't help in this case. We'll try `induction H` instead:

<table>
<tr>
<td> Coq Commands </td> <td> Proof State </td>
</tr>
<tr>
<td> 
<pre lang="coq">
induction H.
</pre>
</td>
<td>
<pre lang="coq">
b : bexp
st : state
H0 : beval st b = true
-----------------------------------------------------------
exists st'' : state, st'' =[ skip ]=> st / SBreak
</pre>
</td>
</tr>
</table>

Above is the first case, where `c` should be `skip`. However, the original hypothesis `H`, which was 
```coq
st =[ while b do skip end ]=> st' / SContinue
```

is gone. There's nothing more to do :(

### Why it happens

Calling `induction H` is performing induction on `ceval`. `ceval` itself is an inductively defined proposition. The issue is that on induction on indprops, **induction does not care about the given indices of the proposition on which induction was called upon**.

`ceval` has type `Inductive ceval : com -> state -> result -> state -> Prop`

Since `ceval` itself is a type declaration, the `com, state, result, state` we "input" aren't actually called "parameters/arguments" in Coq, but instead *indices*. Parameters are more reserved towards parameters in parametric polymorphism. The "indices" in ceval (com, state, result, state) construct what inhabits the constructions for type `ceval`.

Calling `induction H` in that case is telling Coq "here's this inhabitant of type `ceval`. Perform case analysis on all the possible constructions of `ceval`, creating an induction hypothesis for inductive construction cases".

Therefore, Coq just discards whatever indices that happened to occupy that specific form of `ceval` (`H` in our example), because it's meaningless to keep it since Coq is performing case analysis anyway). Coq is just saying "assume the construction of `ceval` is possible with some given indices `st : state, st' : state, res: result`, instead of whatever used to inhabit the place of those variables in your hypothesis.


But in our case, we need to keep the concrete indices given. There are a couple of ways to do so:


### Solution 1: manually `remember` your indices and call induction

This is the simplest way. We realized that calling induction only made the type of the hypothesis matter. Therefore, we use remember to store the concrete values of the indices in the context. In our `ceval` example, I can do something like so:

<table>
<tr>
<td> Coq Commands </td> <td> Proof State </td>
</tr>
<tr>
<td> 
<pre lang="coq">
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
</pre>
</td>
<td>
<pre lang="coq">
b : bexp
c : com
st, st' : state
H : st =[ while b do c end ]=> st' / SContinue
H0 : beval st' b = true
-----------------------------------------------------
exists st'' : state, st'' =[ c ]=> st' / SBreak
</pre>
</td>
</tr>

<tr>
<td>
<pre lang="coq">
Proof.
  intros.
  remember (<{while b do c end}>) as com eqn:Eqcom.
  remember (SContinue) as res eqn:Eqres.
</pre>
</td>
<td>
<pre lang="coq">
b : bexp
c : com
st, st' : state
com : com
Eqcom : com = <{ while b do c end }>
res : result
Eqres : res = SContinue
H : st =[ com ]=> st' / res
H0 : beval st' b = true
------------------------------------------------------
exists st'' : state, st'' =[ c ]=> st' / SBreak
</pre>
</td>
</tr>

<tr>
<td>
<pre lang="coq">
Proof.
  intros.
  remember (<{while b do c end}>) as com eqn:Eqcom.
  remember (SContinue) as res eqn:Eqres.
  induction c.
</pre>
</td>
<td>
<pre lang="coq">
b : bexp
st, st' : state
com : com
Eqcom : com = <{ while b do skip end }>
res : result
Eqres : res = SContinue
H : st =[ com ]=> st' / res
H0 : beval st' b = true
------------------------------------------------------(1 / 6)
exists st'' : state, st'' =[ skip ]=> st' / SBreak
</pre>
</td>
</tr>

<tr>
<td>
<pre lang="coq">
Proof.
  intros.
  remember (<{while b do c end}>) as com eqn:Eqcom.
  remember (SContinue) as res eqn:Eqres.
  induction c.
    - induction H.
</pre>
</td>
<td>
<pre lang="coq">
Goal 1
b : bexp
Eqcom : <{ skip }> = <{ while b do skip end }>
Eqres : SContinue = SContinue
st : state
H0 : beval st b = true
------------------------------------------------------(1 / 10)
exists st'' : state, st'' =[ skip ]=> st / SBreak
</pre>
</td>
</tr>
</table>

We can see that by keeping the equality on "occupied indices" of the original hypothesis, we have much more to work with.

Another observation is that most goals become trivial by contradiction on `Eqcom`. Often, this is the case.
It's handy to immediately try to invert the contradiction and substitute:

```coq
remember (<{your_arbitrary_command}>) as com eqn:Eqcom.
induction my_target_relation; inversion Eqcom; subst.
```

### Solution 2: `dependent induction H`

The problem with the first solution is that since we're only applying induction, we can take advantage of inversion to eliminate trivial goals.
Well, it turns out that there is a tactic that does exactly what we wanted to achieve which performs inversion while preserving occupied indices: `dependent induction`.

You need to add an import statement:

```coq
Require Import Program.Equality.
```

It does everything in Solution #1, plus with inversion:


<table>
<tr>
<td> Coq Commands </td> <td> Proof State </td>
</tr>
<tr>
<td> 
<pre lang="coq">
Require Import Program.Equality.

Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
    induction c.
    - dependent induction H.
</pre>
</td>
<td>
<pre lang="coq">
Goal 1
b : bexp
st : state
H : beval st b = false
H0 : beval st b = true
------------------------------------------------------(1 / 3)
exists st'' : state, st'' =[ skip ]=> st / SBreak
</pre>

<pre lang="coq">
Goal 2
b : bexp
st, st' : state
H : beval st b = true
H0 : st =[ skip ]=> st' / SBreak
IHceval : forall b : bexp, <{ skip }> = <{ while b do skip end }> -> SBreak = SContinue -> beval st' b = true -> exists st'' : state, st'' =[ skip ]=> st' / SBreak
H1 : beval st' b = true
------------------------------------------------------(2 / 3)
exists st'' : state, st'' =[ skip ]=> st' / SBreak
</pre>

<pre lang="coq">
Goal 3
b : bexp
st, st', st'' : state
H : beval st b = true
H0 : st =[ skip ]=> st' / SContinue
H1 : st' =[ while b do skip end ]=> st'' / SContinue
IHceval1 : forall b : bexp, <{ skip }> = <{ while b do skip end }> -> SContinue = SContinue -> beval st' b = true -> exists st'' : state, st'' =[ skip ]=> st' / SBreak
IHceval2 : forall b0 : bexp, <{ while b do skip end }> = <{ while b0 do skip end }> -> SContinue = SContinue -> beval st'' b0 = true -> exists st''0 : state, st''0 =[ skip ]=> st'' / SBreak
H2 : beval st'' b = true
------------------------------------------------------(3 / 3)
exists st''0 : state, st''0 =[ skip ]=> st'' / SBreak
</pre>
</td>
</tr>
</table>




### references
- https://coq.inria.fr/doc/v8.9/refman/proof-engine/detailed-tactic-examples.html
- https://jamesrwilcox.com/dep-destruct.html
- https://stackoverflow.com/questions/66916376/loop-while-proving-a-theorem
- https://stackoverflow.com/questions/4519692/keeping-information-when-using-induction
- https://stackoverflow.com/questions/55965468/what-to-do-when-the-induction-removes-too-much-information-to-make-the-goal-solv
- https://stackoverflow.com/questions/20554493/coq-induction-over-functions-without-losing-information

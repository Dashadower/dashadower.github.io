---
layout: post
title: Coq - Vernacular Search Commands
usemathjax: true
---

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
---
layout: post
title: Coq Tactics
usemathjax: true
---

- `intros`: move hypotheses/variables from goal to context

    To introduce a conjunctive hypothesis `A /\ B` into `H1: A; H2: B`, use `intros [H1 H2]`.

    To introduce a disjunctive hypothesis `A \/ B` into `H1: A; H2: B`, use `intros [H1 | H2]`.

    Patterns can be nested: `[[Ha|Hb] H]` can be used to split `(A \/ B) /\ C`.

- `reflexivity`: finish the proof (when the goal looks like `e = e`) (반사성)

- `apply L`: prove goal using a hypothesis, lemma, or constructor `L`. `L` must be immediately match-able within the goal.

- `apply L in H`: apply a hypothesis, lemma, or constructor `L` to
a hypothesis `H` in the context (forward reasoning)

- `apply L with [a := b]`: explicitly specify values for variables
that cannot be determined by pattern matching. Attempts application of `L` with occurences of `a` in `L` replaced with `b`. (variable renaming/ quantifier matching)

- `simpl`: simplify computations in the goal

- `simpl in H`: ... or within a hypothesis `H`

- `rewrite L`: use an equality hypothesis (or lemma) `L` to rewrite
the goal. use

- `rewrite <- L`: Rewrite from right to left of the lemma.

- `rewrite L in H`: ... or within a hypothesis `H`

- `symmetry`: changes a goal of the form `t=u` into `u=t`

- `symmetry in H`: changes a hypothesis of the form `t=u` into
`u=t`

- `transitivity y`: prove a goal `x=z` by proving two new subgoals,
`x=y` and `y=z` (추이성)

- `unfold x`: replace a defined constant `x` by its right-hand side in
the goal. Frequently `x` is a function. (함수 전개)

- `unfold x in H`: ... or within a hypothesis `H`

- `destruct x as ...`: case analysis on values of inductively
defined type `x`. 

    e.g) `p = X * Y; destruct p as (x, y)`

- `destruct x eqn:E`: specify the name of an equation(`E`) to be
added to the context, recording the result of the case
analysis

    Another way to use destruct is to "split" a hypothesis with a logical AND into two hypotheses. e.g.)

    ```
    n, m : nat
    H : n = 0 /\ m = 0
    ```

    Using `destruct H as [Hn Hm]` yields:
    ```
    > destruct H as [Hn Hm].
    Hn : n = 0
    Hm : m = 0
    ```

    Destructing a cunjunctive hypothesis is common that if you have a hypothesis `H` with a conjunctive form, you can compresses `intros H; destruct H as [Hn Hm]` into `intros [Hn Hm]` (when it's the hypothesis's turn to be introduced). Brackets can  be nested for multiple conjunctive statements.

    If you dont need a portion, simply use `_` to throw it away:

    ```
    destruct H as [Hn _].  (* Onky keeps Hn *)
    ```

    The same works for disjunctive hypotheses.

- `induction x as ...`: induction on values of inductively
defined types

- `injection x as ...`: reason by injectivity on equalities
between values of inductively defined types. (일대일 관계인 constructor 의 성질 추론)

     e.g 
     ```H: (n, m) = (x, y); injection H as H1 H2.``` 
     yields 
     ```H1: n = m, H2: x = y```

- `discriminate x`: reason by disjointness of constructors on
equalities between values of inductively defined types within hypothesis `x`(or goal if omitted). (proof by different contructors always being not equal)

- `assert (H: e)` (or `assert (e) as H`): introduce a "local
lemma" `e` and call it `H` (보조정리 도입)

- `generalize dependent x`: move the variable `x` (and anything
else that depends on it) from the context back to an explicit
hypothesis in the goal formula. (reverses `intros` and converts to universal quantification)

- `f_equal`: change a goal of the form `f x = f y` into `x = y`

- `split`: Split the clauses of conjunction(logical AND) `A /\ B`, into subgoals `A` and `B`.

- `left/right`: Prove disjunction(logical OR) `A \/ B` with either left clause `A` or right clause `B`.
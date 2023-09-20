---
layout: post
title: Coq Tactics
usemathjax: true
---

- `intros`: move hypotheses/variables from goal to context

- `reflexivity`: finish the proof (when the goal looks like `e = e`) (반사성)

- `apply`: prove goal using a hypothesis, lemma, or constructor

- `apply... in H`: apply a hypothesis, lemma, or constructor to
a hypothesis `H` in the context (forward reasoning)

- `apply... with [a := b]`: explicitly specify values for variables
that cannot be determined by pattern matching. Replaces `a`` in lemma with `b` and attempts application. (variable renaming/ quantifier matching)

- `simpl`: simplify computations in the goal

- `simpl in H`: ... or within a hypothesis `H`

- `rewrite`: use an equality hypothesis (or lemma) to rewrite
the goal

- `rewrite ... in H`: ... or within a hypothesis `H`

- `symmetry`: changes a goal of the form `t=u` into `u=t`

- `symmetry in H`: changes a hypothesis of the form `t=u` into
`u=t`

- `transitivity y`: prove a goal `x=z` by proving two new subgoals,
`x=y` and `y=z` (추이성)

- `unfold`: replace a defined constant by its right-hand side in
the goal (함수 전개)

- `unfold... in H`: ... or within a hypothesis `H`

- `destruct... as...`: case analysis on values of inductively
defined types e.g) `p = X * Y; destruct p as (x, y)`

- `destruct... eqn:...`: specify the name of an equation to be
added to the context, recording the result of the case
analysis

- `induction... as...`: induction on values of inductively
defined types

- `injection... as...`: reason by injectivity on equalities
between values of inductively defined types. (일대일 관계인 constructor 의 성질 추론 e.g `S n = S m -> n = m` )

- `discriminate`: reason by disjointness of constructors on
equalities between values of inductively defined types. (proof by different contructors always being not equal)

- `assert (H: e)` (or `assert (e) as H`): introduce a "local
lemma" `e` and call it `H` (보조정리 도입)

- `generalize dependent x`: move the variable `x` (and anything
else that depends on it) from the context back to an explicit
hypothesis in the goal formula. (reverses `intros` and converts to universally quantification)

- `f_equal`: change a goal of the form `f x = f y` into `x = y` *
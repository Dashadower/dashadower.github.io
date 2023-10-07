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

- `apply L`: prove goal using a hypothesis, lemma, or constructor `L`. `L` must be immediately match-able within the goal. (backward reasoning)

    If we assume the goal is true,
    ```
    goal     L -> goal
    ------------------
           L
    ```

    In other words, if we know `L -> goal` and we are trying to prove `goal`, it suffices to prove `L`.

- `apply L in H`: apply a hypothesis, lemma, or constructor `L` to
a hypothesis `H` in the context (forward reasoning)

    ```
    H      H -> H'
    -------------
        H'
    ```

    In other words, if we have hypothesis `H` and an implication `H -> H'`, `H'` is true in the context.

- `apply L with (a := b)`: explicitly specify values for variables
that cannot be determined by pattern matching. Attempts application of `L` with occurences of `a` in `L` replaced with `b`. (variable renaming/ quantifier matching)

- `simpl`: simplify computations in the goal

- `simpl in H`: ... or within a hypothesis `H`

- `simpl in *`: ... or on all contexts and goals. This notation is also possible with other tactics that admit `in`.

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
analysis. `x` can be an inductively defined type or an equation that yields an inductively defined type.

    ```
    destruct n eqn:Eqn.    (* n is type nat *)
        - (* case 1: n = 0 *)
        - (* case 2: n = S n' for some nat n' *)
    ```

- `destruct H as [Hn Hm]` (On hypotheses with logical conjunction/disjunction):

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
    ---------------
    ```

    Destructing a cunjunctive hypothesis is common that if you have a hypothesis `H` with a conjunctive form, you can compresses `intros H; destruct H as [Hn Hm]` into `intros [Hn Hm]` (when it's the hypothesis's turn to be introduced). Brackets can  be nested for multiple conjunctive statements.

    If you dont need a portion, simply use `_` to throw it away:

    ```
    destruct H as [Hn _].  (* Onky keeps Hn *)
    ```

    The same works for disjunctive hypotheses. However, it creates two subgoals, one with left being true and another with right being true.

- `destruct H as [x' H']` (On hypotheses with existential quantifiers):

    If there's a hypothesis `H` such that it containt an existential quantifier, e.g)

    ```
    H : exists x : nat, S n = S n' + x
    ```

    , using `destruct H as [x' H']` introduces a variable `x'` which satisfies the quantifier and hypothesis `H': S n = S n' + x'`
    which is true for `x'`.

- `destruct H` (On hypotheses that are `False`):

    Ex falso quodlibet. If a hypothesis is a `False`, complete the proof.

- `induction x as ...`: induction on values of inductively
defined types

- `injection x as ... (in H)`: reason by injectivity on equalities
between values of inductively defined types. (일대일 관계인 constructor 의 성질 추론)

     e.g 
     ```H: (n, m) = (x, y); injection H as H1 H2.``` 
     yields 
     ```H1: n = m, H2: x = y```

- `discriminate H`: reason by disjointness of constructors on
equalities between values of inductively defined types within hypothesis `H`(or goal if omitted). (proof by different contructors always being not equal)

- `assert (H: e)` (or `assert (e) as H`): introduce a "local
lemma" `e` and call it `H` (보조정리 도입)

- `generalize dependent x`: move the variable `x` (and anything
else that depends on it) from the context back to an explicit
hypothesis in the goal formula. (reverses `intros` and converts to universal quantification)

- `f_equal`: change a goal of the form `f x = f y` into `x = y`

- `split`: Split the clauses of conjunction(logical AND) `A /\ B`, into subgoals `A` and `B`.

- `left/right`: Prove disjunction(logical OR) `A \/ B` with either left clause `A` or right clause `B`.

- `exists x`: Given an existential quantifier, substitute in `x` in place of the quantified variable and make it the goal.

    Existential quantifiers are proved by giving a concrete "example" value for the quantified variable such that goal holds. `exists x` sets `x` as the value in which the goal must be shown to hold.

- `replace (x) with (y)` : replaces expr `x` with expr `y`.     Immediately creates goal `x = y`.

- `inversion E as [...]` : Inversion on evidence. Given an evidence proposition E as a hypothesis, select one of the inductively defined propsition of the evidence that matches the hypothesis.

    Example) Suppose we have `ev n` in the context where `ev` is an inductive proposition of a nat being even:

    ```
    Inductive ev : nat -> Prop :=
        | ev_0                       : ev 0
        | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
    ```

    `ev n` implies `n` can be either 0 or `S S n'` for an even number `n'`. `inversion E as [| n' E' Heq]` then identifies for `n` to be even, `n = 0 \/ ev (S S n')` must hold. The evidence of `ev (S (S n'))` is:

    ```
    ev_SS n' E'
    ```

    for some (even) nat `n'` and evidence `E'` of `n'` being even which is assumed to be true. `Heq` describes the relationship between `n` and `n'`, which is `n = S (S n')`.

    If I try to explain it informally,
    > We have `ev n` in the context. For `n` to be an even number, it must be either 0 or if `n = S (S n')` for some number `n'`, `n'` must also be even.

    You can observe that `inversion` performs destruct in an opposite direction: it checks the cases in which an inductive property is defined and performs case analysis, identifying the precondition which is required for the hypothesis to hold.

    Here's an excerpt from Software Foundations as a summary:

    > Here's how [inversion] works in general.
    >  - Suppose the name `H` refers to an assumption `P` in the
        current context, where `P` has been defined by an `Inductive` declaration.
    >  - Then, for each of the constructors of `P`, `inversion H`
        generates a subgoal in which `H` has been replaced by the
        specific conditions under which this constructor could have
        been used to prove `P`.
     > - Some of these subgoals will be self-contradictory; 
        `inversion` throws these away.
     > - The ones that are left represent the cases that must be 
        proved to establish the original goal.  For those, `inversion` adds to the proof context all equations that must hold of the arguments given to `P` -- e.g., `n' = n` in the proof of `evSS_ev`).

- `remember e as x`: Replace all occurrences of the expression `e` with the variable `x`, and adds `x = e` to the context.
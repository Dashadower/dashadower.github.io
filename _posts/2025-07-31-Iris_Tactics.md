---
layout: post
title: Iris Tactics
usemathjax: true
---

## Non-automatic

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

- `rewrite L at n`: Rewrite only the `n`th occurence term that matches `L`. Rewrite finds the first matching subterm in depth-first search order. Only subterms identical to that first matched subterm are rewritten.

- `symmetry`: changes a goal of the form `t=u` into `u=t`

- `symmetry in H`: changes a hypothesis of the form `t=u` into
`u=t`

- `transitivity y`: prove a goal `x=z` by proving two new subgoals,
`x=y` and `y=z` (추이성)

- `unfold x`: replace a defined constant `x` by its right-hand side in
the goal. Frequently `x` is a function. (함수 전개)

- `unfold x, y`: ... or unfold multiple definitions

- `unfold x in H`: ... or within a hypothesis `H`

- `destruct x as ...`: case analysis on values of inductively
defined type `x`. 

    e.g) `p = X * Y; destruct p as (x, y)`

- `destruct x eqn:E`: specify the name of an equation(`E`) to be
added to the context, recording the result of the case
analysis. `x` can be an inductively defined type or an equation that yields an inductively defined type.

    ```coq
    destruct n eqn:Eqn.    (* n is type nat *)
        - (* case 1: n = 0 *)
        - (* case 2: n = S n' for some nat n' *)
    ```

- `destruct H as [Hn Hm]` (On hypotheses with logical conjunction/disjunction):

    Another way to use destruct is to "split" a hypothesis with a logical AND into two hypotheses. e.g.)

    ```coq
    n, m : nat
    H : n = 0 /\ m = 0
    ```

    Using `destruct H as [Hn Hm]` yields:
    ```coq
    > destruct H as [Hn Hm].
    Hn : n = 0
    Hm : m = 0
    ---------------
    ```

    Destructing a conjunctive hypothesis is common that if you have a hypothesis `H` with a conjunctive form, you can compresses `intros H; destruct H as [Hn Hm]` into `intros [Hn Hm]` (when it's the hypothesis's turn to be introduced). Brackets can  be nested for multiple conjunctive statements.

    If you dont need a portion, simply use `_` to throw it away:

    ```coq
    destruct H as [Hn _].  (* Onky keeps Hn *)
    ```

    The same works for disjunctive hypotheses. However, it creates two subgoals, one with left being true and another with right being true.

- `destruct H as [x' H']` (On hypotheses with existential quantifiers):

    If there's a hypothesis `H` such that it containt an existential quantifier, e.g)

    ```coq
    H : exists x : nat, S n = S n' + x
    ```

    , using `destruct H as [x' H']` introduces a variable `x'` which satisfies the quantifier and hypothesis `H': S n = S n' + x'`
    which is true for `x'`.

    If you have multiple variables within the existential quantifier, e.g)

    ```coq
    H0 : exists s1 s3 s4 : list T, s2 = s1 ++ s3 ++ s4
    --------------
    ```
    
    You can run
    ```coq
    destruct H0 as (s1 & s3 & s5 & H0).
    ```

    To introduce all the quantified variables and the hypothesis within a single command.


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

- `assert (H1 := H)` : duplicate hypothesis `H` into `H1`

- `generalize dependent x`: move the variable `x` (and anything
else that depends on it) from the context back to an explicit
hypothesis in the goal formula. (reverses `intros` and converts to universal quantification)

- `revert x` : weaker version of `generalize dependent`

- `f_equal`: change a goal of the form `f x = f y` into `x = y`

- `split`: Split the clauses of conjunction(logical AND) `A /\ B`, into subgoals `A` and `B`.

- `left/right`: Prove disjunction(logical OR) `A \/ B` with either left clause `A` or right clause `B`.

- `exists x`: Given an existential quantifier, substitute in `x` in place of the quantified variable and make it the goal.

    Existential quantifiers are proved by giving a concrete "example" value for the quantified variable such that goal holds. `exists x` sets `x` as the value in which the goal must be shown to hold.

- `replace (x) with (y)` : replaces expr `x` with expr `y`.     Immediately creates goal `x = y`.

- `inversion E as [...]` : Inversion on evidence. Given an evidence proposition E as a hypothesis, select one of the inductively defined propsition of the evidence that matches the hypothesis.

    Example) Suppose we have `ev n` in the context where `ev` is an inductive proposition of a nat being even:

    ```coq
    Inductive ev : nat -> Prop :=
        | ev_0                       : ev 0
        | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
    ```

    `ev n` implies `n` can be either 0 or `S S n'` for an even number `n'`. `inversion E as [| n' E' Heq]` then identifies for `n` to be even, `n = 0 \/ ev (S S n')` must hold. The evidence of `ev (S (S n'))` is:

    ```coq
    ev_SS n' E'
    ```

    for some (even) nat `n'` and evidence `E'` of `n'` being even which is assumed to be true. `Heq` describes the relationship between `n` and `n'`, which is `n = S (S n')`.

    If I try to explain it informally,
    > We have `ev n` in the context. For `n` to be an even number, it must be either 0 or if `n = S (S n')` for some number `n'`, `n'` must also be even.

    You can observe that `inversion` performs destruct in an opposite direction: it checks the cases in which an inductive property is defined and performs case analysis, identifying the precondition which is required for the hypothesis to hold.

    (For detailed info check the blog post on inductive props)

- `remember e as x`: Replace all occurrences of the expression `e` with the variable `x`, and adds `x = e` to the context.
- `remember e as x eqn:Eqx`: same as above, but name the equality as `Eqx`

- `clear H` : Delete hypothesis `H` from the context

-  `subst x` :  Given a variable `x`, find an assumption `x = e` or `e = x` in the context, replace `x` with `e` throughout the context and current goal, and clear the assumption

-  `subst` : Substitute away all assumptions of the form `x = e` or `e = x` (where `x` is a variable).

-  `rename... into...` : Change the name of a hypothesis in the proof context. For example, if the context includes a variable named `x`, then `rename x into y` will change all occurrences of `x` to `y`

-  `assumption` : Try to find a hypothesis `H` in the context that exactly matches the goal; if one is found, solve the goal

-  `contradiction` : Try to find a hypothesis H in the context that is logically equivalent to False. If one is found, solve the goal

-  `constructor` : Try to find a constructor `c` (from some Inductive definition in the current environment) that can be applied to solve the current goal. If one is found, behave like `apply c`

- `all: ` : run tactic on all remaining goals. Useful when running chained tactics with `;`. example: `all: unfold not; intros. inversion H`

- `specialize H` : replaces a given hypothesis with that hypothesis applied to some other term.

  ```
  Example specialize {A B: Type} (H: A -> B) (a: A): B.
  Proof.
    specialize (H a).
    exact H.
  Qed.
  ```

  `specialize (H a)` will apply H to a (apply as in function application)
  and replaces `H` with it.

- `pose proof P`: introduce a previously proved theorem `P` as a hypothesis. You can even use this to instantiate implications/theorems in your current goal context!

  For example, suppose I have 

  ```
  H : forall n m : nat, n < m -> n < m + 1
  ```

  Then, I can do `pose proof (H 0 1)` to instantiate `H` with `n = 0, m = 1)`

  This is the same as `(specialize H 0 1)`, except specialize replaces the original `H` with the instantiated version.

- `pose proof P as X`: ...or as hypothesis name `X`.

### Display, does not alter proof state

- `move h before h'` : Reorder hypothesis `h` so it comes right above `h'`
-  `move h after h'` : ...or right below it
- `move h at top` : ...or to the top
- `move h at bottom` : ...or to the bottom

### Implicit Argument Passing

Suppose we want to initialize the following trivial lemma:

```coq
assert (H1: [] = []) by reflexivity.
```

The command will fail with a strange error message:

```coq
Cannot infer the implicit parameter A of nil whose
type is "Type" in environment
```

This is because if we print the list type, it accepts an _implicit_ argument `A` designating the type of the elements of the list:

```coq
Inductive list (A : Type) : Type :=
  nil : list A | cons : A -> list A -> list A.
```

In this case, we need to explicitly pass `A` using `@`:

```coq
assert (H1: @nil nat = @nil nat) by reflexivity.
```

which will yield our expected result.

[https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html#lab123]()

## Automation

### `auto`

(The following is quoted from Software Foundations)

The auto tactic solves goals that are solvable by any combination of `intros` and `apply` (of hypotheses from the local context, by default).

Using `auto` is always "safe" in the sense that it will never fail and will never change the proof state: either it completely solves the current goal, or it does nothing.

By default, auto recursively attempts to apply `apply` up to a given depth. You can specify the max search depth by using `auto n`, where `n` is a number.

When searching for potential proofs of the current goal, auto considers the hypotheses in the current context together with a *hint database* of other lemmas and constructors. Some common lemmas about equality and logical operators are installed in this hint database by default.

We can add theorems/constructors to the global hint database by writing

```coq
Hint Resolve T : core.
```

where `T` is a top-level theorem or a constructor of an inductively defined proposition (i.e., anything whose type is an implication). As a shorthand, we can write

```coq
Hint Constructors c : core.
```

to tell Coq to do a `Hint Resolve` for all of the constructors from the inductive definition of `c`.
It is also sometimes necessary to add

```coq
Hint Unfold d : core.
```

where `d` is a defined symbol, so that auto knows to expand uses of `d`, thus enabling further possibilities for applying lemmas that it knows about.

- `debug auto.` : Vernacular command which prints the search trace of auto.
- `info_auto.` : Vernacular command which shows what sequence of tactics succesfully proved the goal.


### Ltac

Ltac lets you create custom "macro" tactics to eliminate common tactic sequences into a single command.

```coq
H1: beval st b = false
H2: beval st b = true
```

Having the two hypothesis would result in calling `rewrite H1 in H2; discriminate H2` to prove. Writing this in Ltac would result in:

```coq
Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.
```

which lessens the amount of commands you have to type.

### Pattern matching

Ltac also supports pattern matching on goals and hypotheses:

```coq
Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.
```

This would find two hypotheses that have the form `E = true`, `E = false`, and automatically call `rwd` tactic we defined. 

The syntax is similar to defining variables in `Check` or `Locate`: We use a question mark to specify what we're looking for.

Ltac can also handle quantifiers:

```coq
Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.
```

Ltac will try to find a proposition defined for some variable x which implies some equality, and then will also find a hypothesis in which it can apply the implication, and proceed to rewrite the implied equality.

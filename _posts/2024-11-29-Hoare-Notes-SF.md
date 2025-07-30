---
layout: post
title: Hoare Logic Notes for Solving SF
usemathjax: true
---

## Consequence Rule

```
  0   1   2   3   4   5   6   7   8   9   10  11  12
|---|---|---|---|---|---|---|---|---|---|---|---|---|
[--------------------0, 10------------------]      (Precondition P1)
              |--> x := x + 1 --> 
    [--------------------1, 11------------------]  (Weakened, less precise postcondition Q1)


        [------------2, 8-----------]              (Strengthened, more precise Precondition P2)
              |--> x := x + 1 -->
            [------------3, 9-----------]          (Postcondition Q2)
__
P2 -> P1  (strengthening precondition)
      __
Q2 -> Q1  (weakening postcondition)
```

$$
\frac{P2 \implies P1 \quad Q2 \implies Q1 \quad \{ P1 \} C \{ Q2 \} }{ \{ P2 \} C \{ Q1 \} }
$$

In the context of implications on program states, I prefer to say "more/less precise" instead of "stronger/weaker" for intuition.

Since all states that satisfy $P2$ also satisfy $P1$ but not the other way around, $P2$ is more precise than $P1$. Therefore, strengthening the precondition is equal to making the precondition more precise.

Since $Q1$ is less precise than $Q2$, weakening the postcondition is equal to making the postcondition less precise.

To summarize, we're free to make the antecedent(precondition) more precise and the consequent(postcondition) less precise without loss of soundness.

------------------------------------------------------------

## Loop Invariants

Use the following simple trick to find loop invariants for while hoare logic:

{% raw %}
```
        (1)    {{ P }}  ->>
        (2)    {{ Inv }}
                 while B do
        (3)              {{ Inv ∧ B }}  ->>
        (4)              {{ Inv [X ⊢> e2] [Y ⊢> e1] }}
                   Y := e1;
        (5)              {{ Inv [X ⊢> e2] }}
                   X := e2
        (6)              {{ Inv }}
                 end
        (7)    {{ Inv ∧ ¬B }}  ->>
        (8)    {{ Q }}
```
(code and explanation taken from PLF and modified to be generic)
{% endraw %}

By examining this skeleton, we can see that any valid loop invariant `Inv` will have to respect three conditions:

1. it must be weak enough to be implied by the loop's precondition `P`, i.e., (1) must imply (2);

2. it must be strong enough to imply the program's postcondition `Q`, i.e., (7) must imply (8);

3. it must be preserved by a single iteration of the loop, assuming that the loop guard `B` also evaluates to true, i.e., (3) must imply (4).

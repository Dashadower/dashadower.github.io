---
layout: post
title: Hoare Logic Notes for Solving SF
usemathjax: true
---

```
  0   1   2   3   4   5   6   7   8   9   10  11  12
|---|---|---|---|---|---|---|---|---|---|---|---|---|
[--------------------0, 10------------------]      (Precondition P1)
              |--> x := x + 1 --> 
    [--------------------1, 11------------------]  (Postcondition Q1)


        [------------2, 8-----------]              (Stronger Precondition P2)
              |--> x := x + 1 -->
            [------------3, 9-----------]          (Stronger Postcondition Q2)
__
P2 -> P1  (strengthening precondition)
      __
Q2 -> Q1  (weakening postcondition)
```

$$
\frac{P2 \implies P1 \quad Q2 \implies Q1 \quad \{ P1 \} C \{ Q2 \} }{ \{ P2 \} C \{ Q1 \} }
$$

------------------------------------------------------------

This leads to the following skeleton:
```
        (1)    {{ X = m ∧ Y = n }}  ->>                   (a)
        (2)    {{ Inv }}
                 while X ≠ 0 do
        (3)              {{ Inv ∧ X ≠ 0 }}  ->>          (c)
        (4)              {{ Inv [X ⊢> X-1] [Y ⊢> Y-1] }}
                   Y := Y - 1;
        (5)              {{ Inv [X ⊢> X-1] }}
                   X := X - 1
        (6)              {{ Inv }}
                 end
        (7)    {{ Inv ∧ ¬(X ≠ 0) }}  ->>                (b)
        (8)    {{ Y = n - m }}
```

By examining this skeleton, we can see that any valid Inv will have to respect three conditions:

(a) it must be weak enough to be implied by the loop's precondition, i.e., (1) must imply (2);

(b) it must be strong enough to imply the program's postcondition, i.e., (7) must imply (8);

(c) it must be preserved by a single iteration of the loop, assuming that the loop guard also evaluates to true, i.e., (3) must imply (4).

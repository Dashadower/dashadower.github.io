---
layout: post
title: Standard Separation Logic
usemathjax: true
---

Separation Logic is an extension of Hoare Logic to reason about local regions of a program state.

The main idea is to partition the program state into disjoint portions. This makes it possible to reason on just parts of the program state in which we specified conditions, which is necessary for reasoning about pointer manipulation.


## Magic Wand

Definition

$$
\newcommand\wand{\mathrel{-\mkern-6mu*}}
H_1 \ \wand \ H_2 := \forall h', h \bot h' \rightarrow H_1 \ h' \rightarrow H_2 \ (h \cup h')
$$

where $$h, h'$$ are disjoint heaps and $$H_1, H_2$$ are heap predicates $$\mathsf{heap} \rightarrow \mathsf{Prop}$$.

This means that for any heap $$h$$, if we append a disjoint heap $$h'$$ that satifies $$H_1$$, then $$H_2$$ holds. We can see this operator acts as an "implication" between heap predicates.

### Properties

The wand has the following properties:

- The "antecedent" is cancelled out if it is already given:
  $$
  H_1 * (H_1 \wand H_2) \implies H_2
  $$
- It is transitive *with respect to a given heap*:
  $$
  \frac{(H_1 \wand H_2) * (\quad H_2 \wand H_3)}{H_1 \wand H_3}
  $$
- The empty heap predicate has no effect:
  $$
  \_ \wand \H = \H
  $$
- Like the consequence rule, we can strengthen the "antecedent" and weaken the "consequent":
  $$
  \frac{H'_1 \implies H_1 \quad H_2 \implies H'_2 \quad H_1 \wand H_2}{H'_1 \wand H'_2}
  $$
- It can be curried:
  $$
  (H_1 * H_2) \wand H_3 = H_1 \wand (H_2 \wand H_3)
  $$

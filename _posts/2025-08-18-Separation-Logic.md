---
layout: post
title: Standard Separation Logic
usemathjax: true
---
# Separation Logic

Separation Logic is an extension of Hoare Logic to reason about local regions of a program state.

The main idea is to partition the program state into disjoint portions. This makes it possible to reason on just parts of the program state in which we specified conditions, which is necessary for reasoning about pointer manipulation.


## Magic Wand

testing mathjax 
$$
\newcommand\sepimp{\mathrel{-\mkern-6mu*}}
P \ \sepimp \ Q
$$



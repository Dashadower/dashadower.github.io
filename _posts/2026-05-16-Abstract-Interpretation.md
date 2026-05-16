---
layout: post
title: A 2 Minute Introduction to Sound Abstract Interpretation
usemathjax: true
---

A trace of a program execution is the sequence of transitions of the program state:

![trace](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_trace.png)

Errorneous states are just states that satisfy some property $P$:

![error](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_error.png)

Testing may verify some traces if an error occurs:

![testing](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_testing.png)

But checking all possible programs are impossible:

![infinite traces](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_infinite_traces.png)

Abstract interpretation approximates the concrete states with a less precise approximation:

![abstraction](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_abstraction.png)

Since it's an over-approximation, it may falsely identify safe states as errorneous:

![false positive](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_false_positive.png)

And additionally take into account states which would not actually be computed:

![overapproximation](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_overapproximation.png)

But it is a sound approximation, meaning it never not takes a concrete state into account:

![sound](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_sound.png)

And all concrete errorneous states must be correctly abstracted into an errorneous abstract state:

![sound_errors](https://raw.githubusercontent.com/Dashadower/dashadower.github.io/master/images/ai_sound_errors.png)
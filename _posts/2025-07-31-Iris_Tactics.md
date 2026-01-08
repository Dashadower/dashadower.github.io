---
layout: post
title: Iris Tactics
usemathjax: true
---

## basics
(referenced from logsem iris tutorial)

Iris propositions include many of the usual logical connectives such
as conjunction `P ∧ Q`. As such, Iris uses a notation scope to
overload the usual logical notation in Coq. This scope is delimited by
`I` and bound to `iProp Σ`. Hence, you may need to wrap your
propositions in `(_)%I` to use the notations.

Iris uses ssreflect internally. This means the following changes are made to gallina tactics:

- No commas between arguments, meaning you have to write
`rewrite H1 H2` instead of `rewrite H1, H2`.
- `rewrite -H` instead of `rewrite <-H`. But the original also seems to work.
- Occurrences are written in front of the argument (`rewrite {1 2 3}H` instead of `rewrite H at 1 2 3`)
- Rewrite can unfold definitions as `rewrite /def` which does thesame as `unfold def`

## tactics

- `iIntros.`: Same as `intros`. From my experience, it was simplier to intros specifically as much as possible.
    - `iIntros "H".`: `intros H`
    - `iIntros "[H1 H2]"` : Used to intros `P * Q` separately into spatial context.
    - `iIntros "H1 & H2 & H3".`: Used to intros multiple hypothesis at once. `(H1 & .. & H2 & H3) = [H1 .. [H2 H3] ..]`. 
    - `iIntros "[HP HQ]".`: Used to intros `P ∨ Q`.
    - `iIntros %x.`: Used to intros `∀ x`.
    - `iIntros %x & Hx.`: Used to intros `∃ x, Φ x`.
    - `iIntros %H.`: Intros `⌜...⌝` directly into coq context.
    
- `iFrame.`: Discharge immediate goals from a separating conjunction.
- `iApply "H".`: Same as `apply`.
    - `iApply ("H" with "[H1] [H2]").`: If applying `H` yields two subgoals, automatically pass `H1` to the first and `H2` to the second.
    - `iApply ("H" $! x y z).`: Same as `apply (H x y z)`. `x, y, z` is from the pure context.

- `iSplitL "H".`: Break apart a separating conjunction and pass the `H` hypothesis to the lhs goal.
- `iSplitR "H".`: Same as `iSplitL`, but pass `H` to the rhs goal.
- `iLeft. iRight.`: Same as `left. right.`
- `iExists x.`. Same as `exists x.` `x` is from the pure context.
- `iPureIntro.`: Intros pure hypothesis `⌜...⌝` directly into coq context.


## generic input characters

- `\ent, \vdash` : `⊢`
- `\sep` : `∗`
- `\and` : `∧`
- `\or` : `∨`
- `\ex` : `∃`
- `\all` : `∀`
- `\lc` : `⌜`  `\rc` : `⌝`
- `\fun, \lambda` : `λ`

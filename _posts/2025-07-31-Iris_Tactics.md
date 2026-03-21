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
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md

- `iIntros.`: Same as `intros`. From my experience, it was simplier to intros specifically as much as possible. Start by iIntros-ing in bulk, and dissect as much as possible.
    - `iIntros "H".`: `intros H`
    - `iIntros "H1 H2."` : Intros multiple hypothesis in chained magic wands.
    - `iIntros "[H1 H2]"` : Used to intros `P * Q` separately into spatial context.
    - `iIntros "H1 & H2 & H3".`: Used to intros multiple hypothesis at once. `(H1 & .. & H2 & H3) = [H1 .. [H2 H3] ..]`. 
    - `iIntros "[HP HQ]".`: Used to intros `P ∨ Q`.
    - `iIntros "%x".`: Used to intros `∀ x`.
    - `iIntros "(%x & Hx)".`: Used to intros `∃ x, Φ x`.
    - `iIntros "(%x & (%y & Hxy))".`: Used to intros `∃ x y, Φ x y`.
    - `iIntros "%H".`: Intros `⌜...⌝` directly into coq context.
    - `iIntros "#H".`: Intros a persistent hypothesis into the persistent context as `H` 
    - `iIntros "... !>"`: Call `iModIntro` before introsing, removing later modalities
    - `iIntros ">H"`: Call `iMod` in `H` before introsing, removing modalities from `H`
    
- `iFrame.`: Discharge immediate goals from a separating conjunction.
    - `iFrame "#"`: Use persistent hypotheses
- `iApply "H".`: Same as `apply`.
    - `iApply ("H" with "[H1] [H2]").`: If applying `H` yields two subgoals, automatically pass `H1` to the first and `H2` to the second.
    - `iApply ("H" $! x y z).`: Same as `apply (H x y z)`. `x, y, z` is from the pure context.

- `iSplitL "H".`: Break apart a separating conjunction and pass the `H` hypothesis to the lhs goal.
- `iSplitR "H".`: Same as `iSplitL`, but pass `H` to the rhs goal.
- `iSplit.`: Break apart a bidirectional entailment(`⊣⊢`) just like iff
- `iLeft. iRight.`: Same as `left. right.`
- `iExists x.`. Same as `exists x.` `x` is from the pure context.
- `iDestruct "H" as "[Hx _]".`: Same as `destruct H as (Hx _)`. Useful for destructing conjunctions in a hypothesis
- `iPoseProof "H" as "[Hx _]".`: Same as `iDestruct` but leaves `H`
    - `iPoseProof (some_lemma with "arg1 arg2") as "H".` : introduce some_lemma with args as hypothesis
- `iPureIntro.`: Intros pure hypothesis `⌜...⌝` directly into coq context.
- `iModIntro.`: Remove update modality(`|==>`) or later modality in the goal.
- `iMod "H" as "H1"`: Remove a modality from hypothesis `H`
- `iNext.`: Strip all later modalities(`▷`) from the goal and context. This requires a modality in the goal
- `iCombine "Hl1 Hl2" as "Hl"`: Combine multiplicative (`⋅`) ownership into full ownership. e.g) combining fractioinal and authorative RA.
    - `iCombine "Hl1 Hl2" as "Hl" gives "%Hvalid"`: and provide a validity hypothesis `Hvalid`
- `iAssert (...)%I with "[H1 H2]" as "H4"`: assert `...` using `H1, H2` and name it as `H4`. `...` must be `iProp`. 
    - `iAssert (⌜...⌝)%I as "%H4"` for pure hypotheses.
- `iLöb as "IH" forall (x y).`: Perform lob induction wrt to `x` and `y`.
- `iInv "Hinv" as "H"`: OPen an invariant `Hinv` as `H`
- `iMod (inv_alloc Inv with "[...]") as "#Hinv"`: open an invariant

## Heaplang tactics
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md

- `wp_op.`: symbolically execute exprs
- `wp_pures`: execute pure expressions until possible
- `wp_alloc l as "Hl".`: reason about allocating a location as `l`
- `wp_bind l`: Focus the specification on `l`.
- `wp_apply ("H" with "[H1]")`: same as `iApply ("H" with "[H1]")`
- `wp_apply (wp_fork with [H1])`: For Fork, split between each thread, and pass `H1` to the first thread
- `wp_apply (wp_par t1_post t2_post with "[Hl1] [Hl2]").`: split the threads of a paralle composition (`|||`) with each postconditions


## generic input characters

- `\ent, \vdash` : `⊢`
- `\sep` : `∗`
- `\and` : `∧`
- `\or` : `∨`
- `\ex` : `∃`
- `\all` : `∀`
- `\lc` : `⌜`  `\rc` : `⌝`
- `\fun, \lambda, \lam` : `λ`
- `\"o` : `ö`
- `\mult` : `⋅`
- `\valid` : `✓`
- `\incl` : `≼`
- `\auth` : `●`
\ `\frag` : `◯`

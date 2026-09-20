# JSP-000299 — Lean formalization (complete answer for every prescribed target `1 ≤ k ≤ n`: the maximum is `n − ⌈k/2⌉`)

This repository contains a complete, machine-checked Lean 4 formalization of
the answer to the problem
[JSP-000299](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000299)
from the TheJustinSunPrize/awards problem bank:

> *"How large can a subset of a finite integer range be if none of its subset
> sums equals a prescribed target?"*
> (Number theory; posed no later than 1980; Open.)

## What is proved

For every prescribed target `k` with `1 ≤ k ≤ n`, the largest size of a set
`A ⊆ {1, …, n}` with no subset summing to `k` is exactly `n − ⌈k/2⌉`:

* `jsp000299_gen_lower` — **construction (lower bound):** the set
  `A = {⌈k/2⌉, …, n} \ {k}` has exactly `n − ⌈k/2⌉` elements and no subset of
  `A` sums to `k`.  Any two distinct elements of `A` already sum to more than
  `k`, and the only element equal to `k` was removed.
* `jsp000299_gen_upper` — **upper bound:** every `A ⊆ {1, …, n}` such that no
  subset of `A` sums to `k` satisfies `A.card ≤ n − ⌈k/2⌉`.  Since `{k}` would
  sum to `k`, we have `k ∉ A`; the map sending `x < k` to `min x (k − x)`
  (landing in `{1, …, ⌊k/2⌋}`) and `x > k` to `x − ⌈k/2⌉` is injective on `A`.
* `jsp000299_gen` — combines the two: the maximum is exactly `n − ⌈k/2⌉`.
* `jsp000299_gen_far` — targets beyond the range: if `n·(n+1)/2 < k` then no
  subset of `{1, …, n}` sums to `k` at all, so the maximum is `n`.
* `jsp000299_lower`, `jsp000299_upper`, `jsp000299` — the original
  top-of-range instance (`k = n`, maximum `⌊n/2⌋`), retained for continuity
  with the first submission; it is the specialization `k = n` of the general
  answer.

## Scope (honest statement)

This formalization completely answers the catalogued question for **every
prescribed target inside the range** (`1 ≤ k ≤ n`) and in the vacuous regime
`n·(n+1)/2 < k`.  The remaining regime `n < k ≤ n·(n+1)/2` is genuinely open:
there the maximum equals `n` minus the minimum size of a set of elements
meeting every `k`-summing subset of `{1, …, n}` (a hitting-set problem with no
known closed form); no claim is made on it.  The edge `k = 0` is excluded —
the empty subset of any `A` sums to `0`, so no set satisfies the condition at
all.  This record makes **no award claim**.

## Method

Everything is elementary finite combinatorics over `ℕ`, formalized with
`Finset.Icc`, `Finset.sum`, `Finset.image`, and one explicit injection per
bound (`a ↦ min a (k − a)` below the target; a shifted identity above it).
Small numerical side conditions are discharged by `omega`.  No `sorry`,
`admit`, `native_decide`, or added unproved assumptions are used.

## Build and verification

Toolchain (pinned): `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.

```sh
lake build                  # or:
lake env lean JSP000299.lean   # zero output = success
```

The file ends with `#print axioms` for all seven theorems.  Result of the
axiom audit:

```
'jsp000299_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_gen_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_gen_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_gen_far' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are within the allowed set `{propext, Classical.choice, Quot.sound}`.

## Attribution

Formalization author: **Yaohua-Leo** (AI-assisted via ZCode (GLM)).
Mathematical content is elementary and no external mathematical credit is
claimed for the observation itself; the catalogued problem belongs to the
TheJustinSunPrize/awards problem bank.

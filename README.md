# JSP-000299 — Lean formalization observation (target = top of range: the maximum is ⌊n/2⌋)

This repository contains a complete, machine-checked Lean 4 formalization of a
complete answer for the **target equal to the top of the range** instance of the
open problem
[JSP-000299](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000299)
from the TheJustinSunPrize/awards problem bank:

> *"How large can a subset of a finite integer range be if none of its subset
> sums equals a prescribed target?"*
> (Number theory; posed no later than 1980; Open.)

## What is proved

Fix `n ≥ 2` and take the prescribed target to be `n`, the top of the integer
range `{1, 2, …, n}`.  Then the largest size of a set `A ⊆ {1, …, n}` with no
subset summing to `n` is exactly `⌊n/2⌋`:

* `jsp000299_lower` — **construction (lower bound):** the interval
  `A = {⌈n/2⌉, …, n - 1}` has exactly `n / 2 = ⌊n/2⌋` elements and no subset
  of `A` sums to `n`.  Every element of `A` is `< n`, and any two distinct
  elements of `A` already sum to more than `n`, so the empty, one-element, and
  multi-element cases are all covered.
* `jsp000299_upper` — **upper bound:** every `A ⊆ {1, …, n}` such that no
  subset of `A` sums to `n` satisfies `A.card ≤ n / 2`.  Since `{n}` would sum
  to `n`, we have `n ∉ A`; the map `a ↦ min a (n - a)` sends `A` into
  `{1, …, ⌊n/2⌋}` and is injective on `A` — a collision between distinct
  `a, b ∈ A` forces `a + b = n`, and then `{a, b} ⊆ A` would sum to `n`.
  Hence `A` injects into a set of size `n/2`.
* `jsp000299` — combines the two: the maximum is exactly `n / 2`.

The informal argument (construction by the top half of the range; pairing
upper bound `a ↦ min a (n-a)`) was checked by brute force for all
`n = 2, …, 14` before formalization.

## Scope (honest statement)

This formalization covers **only the case where the prescribed target equals
the top of the range**.  The full problem — a complete characterization for an
arbitrary prescribed target `t` — is **not** addressed here; the catalogued
problem JSP-000299 remains **Open**.  This record makes **no award claim**.

## Method

Everything is elementary finite combinatorics over `ℕ`, formalized with
`Finset.Icc`, `Finset.sum`, `Finset.image`, and the injection
`a ↦ min a (n - a)`.  Small numerical side conditions (`⌈n/2⌉` arithmetic,
"two distinct elements of the top half sum to more than `n`") are discharged
by `omega`.  No `sorry`, `admit`, `native_decide`, or added unproved
assumptions are used.

## Build and verification

Toolchain (pinned): `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.

```sh
lake build                  # or:
lake env lean JSP000299.lean   # zero output = success
```

The file ends with `#print axioms` for all three theorems.  Result of the
axiom audit:

```
'jsp000299_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'jsp000299' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are within the allowed set `{propext, Classical.choice, Quot.sound}`.

## Attribution

Formalization author: **Yaohua-Leo** (AI-assisted via ZCode (GLM)).
Mathematical content is elementary and no external mathematical credit is
claimed for the observation itself; the catalogued problem belongs to the
TheJustinSunPrize/awards problem bank.

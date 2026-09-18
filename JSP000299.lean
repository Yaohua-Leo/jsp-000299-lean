/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000299 — Observation record: complete answer for the target equal to the
top of the range.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0201-0300.md,
#JSP-000299):
  "How large can a subset of a finite integer range be if none of its subset
   sums equals a prescribed target?"

Scope of this file
------------------
We fix the prescribed target to be `n`, the top of the integer range
`{1, 2, …, n}` (with `n ≥ 2`), and prove the exact answer:

* a largest subset `A ⊆ {1, …, n}` such that no subset of `A` sums to `n`
  has exactly `⌊n/2⌋` elements:
  - `jsp000299_lower` constructs such a set of size `n/2`, namely the
    interval `⌈n/2⌉, …, n-1`;
  - `jsp000299_upper` shows every such set has at most `n/2` elements, via
    the injection `a ↦ min a (n - a)` of `A` into `{1, …, ⌊n/2⌋}` (if two
    distinct `a, b ∈ A` collided, they would satisfy `a + b = n`, so the
    two-element set `{a, b}` would sum to `n`);
  - `jsp000299` combines the two bounds: the maximum is exactly `⌊n/2⌋`.

It does NOT settle the catalogued open problem for a general prescribed
target `t` (which remains Open), and makes no award claim.

Method
------
Everything is elementary finite combinatorics over `ℕ`, formalized with
`Finset.Icc`, `Finset.sum`, and `Finset.image`.  The lower bound splits on
whether `T` contains two distinct elements: two distinct elements of the
interval already sum to more than `n`, while a single element is at most
`n - 1`.  The upper bound uses that `n ∉ A` (else `{n}` sums to `n`), so
`1 ≤ a ≤ n - 1` for `a ∈ A`; the map `a ↦ min a (n - a)` then lands in
`{1, …, ⌊n/2⌋}` and is injective on `A` (a collision forces `a + b = n`).
No `sorry`, `admit`, `native_decide`, or added unproved assumptions are used.

Mathematical area: Number theory (subset sums).
Problem posed: no later than 1980 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-! ## The lower bound: a set of size `⌊n/2⌋` avoiding the target `n` -/

/-- **JSP-000299, lower bound.**  For `n ≥ 2` there is a subset `A` of
`{1, …, n}` with exactly `n / 2` elements, none of whose subset sums equals
`n`: take `A = {⌈n/2⌉, …, n - 1}`.  Indeed every element is less than `n`,
and any two distinct elements of `A` already sum to more than `n`. -/
theorem jsp000299_lower (n : ℕ) (hn : 2 ≤ n) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 n ∧ A.card = n / 2 ∧ ∀ T ⊆ A, T.sum id ≠ n := by
  refine ⟨Finset.Icc ((n + 1) / 2) (n - 1), ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · rw [Nat.card_Icc]
    omega
  · intro T hT
    by_cases htwo : ∃ a ∈ T, ∃ b ∈ T, a ≠ b
    · -- two distinct elements already sum to more than `n`
      obtain ⟨a, haT, b, hbT, hab⟩ := htwo
      have hsub : ({a, b} : Finset ℕ) ⊆ T := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haT
        · exact hbT
      have hsum : ({a, b} : Finset ℕ).sum id = a + b := by
        rw [Finset.sum_insert (Finset.notMem_singleton.mpr hab), Finset.sum_singleton]
        simp
      have hsumle : a + b ≤ T.sum id := by
        rw [← hsum]
        exact Finset.sum_le_sum_of_subset hsub
      have h1 := hT haT
      have h2 := hT hbT
      simp only [Finset.mem_Icc] at h1 h2
      omega
    · -- `T` is empty or a singleton, so its sum is `< n`
      push Not at htwo
      rcases Finset.eq_empty_or_nonempty T with hE | ⟨a, haT⟩
      · rw [hE]
        simp only [Finset.sum_empty]
        omega
      · have hTeq : T = {a} := by
          ext z
          simp only [Finset.mem_singleton]
          constructor
          · exact fun hz => htwo z hz a haT
          · intro hz
            rw [hz]
            exact haT
        rw [hTeq]
        simp only [Finset.sum_singleton, id_eq]
        have h := hT haT
        simp only [Finset.mem_Icc] at h
        omega

/-! ## The upper bound: every set avoiding the target `n` has ≤ `⌊n/2⌋` elements -/

/-- **JSP-000299, upper bound.**  For `n ≥ 2`, a subset `A` of `{1, …, n}`
none of whose subset sums equals `n` has at most `n / 2` elements.

Since `{n} ⊆ A` would sum to `n`, we have `n ∉ A`, so every `a ∈ A`
satisfies `1 ≤ a ≤ n - 1`.  The map `a ↦ min a (n - a)` sends `A` into
`{1, …, n/2}` and is injective on `A`: if distinct `a, b ∈ A` satisfied
`min a (n - a) = min b (n - b)`, case analysis (using `a, b ≤ n`) forces
`a + b = n`, and then `{a, b}` — a subset of `A` — would sum to `n`.
Hence `A` injects into a set of size `n / 2`. -/
theorem jsp000299_upper (n : ℕ) (hn : 2 ≤ n) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hA2 : ∀ T ⊆ A, T.sum id ≠ n) : A.card ≤ n / 2 := by
  classical
  -- `n ∉ A`, otherwise the singleton `{n}` sums to `n`
  have hnn : n ∉ A := fun hmem =>
    hA2 {n} (Finset.singleton_subset_iff.mpr hmem) (by simp)
  have hbound : ∀ x ∈ A, 1 ≤ x ∧ x ≤ n ∧ x ≠ n := by
    intro x hx
    have h := hA hx
    simp only [Finset.mem_Icc] at h
    exact ⟨h.1, h.2, fun hxn => hnn (hxn ▸ hx)⟩
  set phi : ℕ → ℕ := fun x => min x (n - x) with hphi
  -- `phi` maps `A` into `{1, …, n/2}`
  have hrange : ∀ x ∈ A, 1 ≤ phi x ∧ phi x ≤ n / 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hbound x hx
    constructor
    · simp only [hphi]
      omega
    · simp only [hphi]
      omega
  -- `phi` is injective on `A`: a collision forces the two elements to sum to `n`
  have hinj : Set.InjOn phi (↑A : Set ℕ) := by
    intro x hx y hy heq
    simp only [hphi] at heq
    obtain ⟨h1, h2, h3⟩ := hbound x hx
    obtain ⟨h4, h5, h6⟩ := hbound y hy
    by_contra hne
    have hsumkey : x + y = n := by
      rcases Nat.le_total x (n - x) with e1 | e1 <;>
        rcases Nat.le_total y (n - y) with e2 | e2
      · rw [min_eq_left e1, min_eq_left e2] at heq; omega
      · rw [min_eq_left e1, min_eq_right e2] at heq; omega
      · rw [min_eq_right e1, min_eq_left e2] at heq; omega
      · rw [min_eq_right e1, min_eq_right e2] at heq; omega
    have hsub : ({x, y} : Finset ℕ) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hsum : ({x, y} : Finset ℕ).sum id = x + y := by
      rw [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      simp
    exact hA2 _ hsub (by rw [hsum]; omega)
  -- conclude by injection into a set of size `n/2`
  have himg : A.image phi ⊆ Finset.Icc 1 (n / 2) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨r1, r2⟩ := hrange y hy
    simp only [Finset.mem_Icc]
    omega
  calc A.card = (A.image phi).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (n / 2)).card := Finset.card_le_card himg
    _ = n / 2 := by rw [Nat.card_Icc]; omega

/-! ## The combined statement: the maximum is exactly `⌊n/2⌋` -/

/-- **JSP-000299 (target `n` = top of the range).**  For `n ≥ 2`, the
maximum size of a subset `A` of `{1, …, n}` such that no subset of `A` sums
to `n` is exactly `⌊n/2⌋ = n / 2`. -/
theorem jsp000299 (n : ℕ) (hn : 2 ≤ n) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = n / 2 ∧ ∀ T ⊆ A, T.sum id ≠ n) ∧
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (∀ T ⊆ A, T.sum id ≠ n) → A.card ≤ n / 2 :=
  ⟨jsp000299_lower n hn, fun A hA hA2 => jsp000299_upper n hn A hA hA2⟩

#print axioms jsp000299_lower
#print axioms jsp000299_upper
#print axioms jsp000299

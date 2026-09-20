/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000299 — Complete answer for a prescribed target inside the range.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0201-0300.md,
#JSP-000299):
  "How large can a subset of a finite integer range be if none of its subset
   sums equals a prescribed target?"

Scope of this file
------------------
We answer the catalogued question exactly whenever the prescribed target `k`
lies inside the range, `1 ≤ k ≤ n`:

* the largest subset `A ⊆ {1, …, n}` such that no subset of `A` sums to `k`
  has exactly `n - ⌈k/2⌉` elements:
  - `jsp000299_gen_lower` constructs such a set of size `n - ⌈k/2⌉`, namely
    `A = {⌈k/2⌉, …, n} \ {k}`: any two distinct elements of `A` already sum
    to more than `k`, and the only element equal to `k` was removed;
  - `jsp000299_gen_upper` shows every such set has at most `n - ⌈k/2⌉`
    elements: `k ∉ A`, and the map sending `x < k` to `min x (k - x)` (which
    lands in `{1, …, ⌊k/2⌋}`) and `x > k` to `x - ⌈k/2⌉` is injective on `A`
    (a collision of two values below `k` forces `x + y = k`);
  - `jsp000299_gen` combines the two bounds.
* At `k = n` this specializes to the top-of-range answer `⌊n/2⌋`, proved
  elementarily by `jsp000299_lower`, `jsp000299_upper` and `jsp000299`,
  which are retained below for continuity with the original submission.
* Beyond the range, `jsp000299_gen_far` settles the vacuous regime
  `n * (n + 1) / 2 < k`: every subset of `{1, …, n}` avoids such a `k`, so
  the maximum is `n`.  The remaining regime `n < k ≤ n * (n + 1) / 2` is
  genuinely open — there the maximum equals `n` minus the minimum size of a
  set of elements meeting every `k`-summing subset of `{1, …, n}`, a
  hitting-set problem for which no closed form is known; this file makes no
  claim on it.

Edges: `k = 0` is excluded from the statements — the empty subset of any
`A` sums to `0`, so no subset satisfies the condition at all.

Method
------
Elementary finite combinatorics over `ℕ` with `Finset.Icc`, `Finset.sum`,
`Finset.image` and one explicit injection per bound.  No `sorry`, `admit`,
`native_decide`, or added unproved assumptions are used.

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
      push_neg at htwo
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

/-! ## Generalization: arbitrary prescribed target `1 ≤ k ≤ n` -/

/-- **JSP-000299, generalized lower bound.**  For `1 ≤ k ≤ n` there is a
subset `A` of `{1, …, n}` with exactly `n - ⌈k/2⌉` elements, none of whose
subset sums equals `k`: take `A = {⌈k/2⌉, …, n} \ {k}`.  Any two distinct
elements of `A` sum to more than `k`, and the only element equal to `k` was
removed. -/
theorem jsp000299_gen_lower (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n ∧ A.card = n - (k + 1) / 2 ∧ ∀ T ⊆ A, T.sum id ≠ k := by
  refine ⟨Finset.Icc ((k + 1) / 2) n \ {k}, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at ha
    simp only [Finset.mem_Icc]
    omega
  · have hkIn : k ∈ Finset.Icc ((k + 1) / 2) n := by
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hkIn), Nat.card_Icc,
      Finset.card_singleton]
    omega
  · intro T hT
    by_cases htwo : ∃ a ∈ T, ∃ b ∈ T, a ≠ b
    · -- two distinct elements of `A` already sum to more than `k`
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
      have ha := hT haT
      have hb := hT hbT
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at ha hb
      have hbig : (k + 1) / 2 + (k + 1) / 2 < a + b := by omega
      omega
    · -- `T` is empty or a singleton, so its sum misses `k`
      push_neg at htwo
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
        have ha := hT haT
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at ha
        omega

/-- **JSP-000299, generalized upper bound.**  For `1 ≤ k ≤ n`, a subset `A`
of `{1, …, n}` none of whose subset sums equals `k` has at most
`n - ⌈k/2⌉` elements.

Since `{k} ⊆ A` would sum to `k`, we have `k ∉ A`.  Map `x ∈ A` with
`x < k` to `min x (k - x)`, which lands in `{1, …, ⌊k/2⌋}`; map `x > k` to
`x - ⌈k/2⌉`, which lands in `{⌊k/2⌋ + 1, …, n - ⌈k/2⌉}`.  The combined map
is injective on `A`: a collision of two values below `k` forces `x + y = k`,
and above `k` the map is a shift of the identity.  Hence `A` injects into
`{1, …, n - ⌈k/2⌉}`. -/
theorem jsp000299_gen_upper (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hA2 : ∀ T ⊆ A, T.sum id ≠ k) :
    A.card ≤ n - (k + 1) / 2 := by
  classical
  have hnn : k ∉ A := fun hmem =>
    hA2 {k} (Finset.singleton_subset_iff.mpr hmem) (by simp)
  have hbound : ∀ x ∈ A, 1 ≤ x ∧ x ≤ n ∧ x ≠ k := by
    intro x hx
    have h := hA hx
    simp only [Finset.mem_Icc] at h
    exact ⟨h.1, h.2, fun hxk => hnn (hxk ▸ hx)⟩
  set psi : ℕ → ℕ := fun x => if x < k then min x (k - x) else x - (k + 1) / 2 with hpsi
  -- `psi` maps `A` into `{1, …, n - ⌈k/2⌉}`
  have hrange : ∀ x ∈ A, 1 ≤ psi x ∧ psi x ≤ n - (k + 1) / 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hbound x hx
    by_cases hxk : x < k
    · have hxv : psi x = min x (k - x) := by rw [hpsi]; simp [hxk]
      constructor
      · rw [hxv]
        rcases Nat.le_total x (k - x) with e | e
        · rw [min_eq_left e]; omega
        · rw [min_eq_right e]; omega
      · rw [hxv]
        have hminle : min x (k - x) ≤ k / 2 := by
          rcases Nat.le_total x (k - x) with e | e
          · rw [min_eq_left e]; omega
          · rw [min_eq_right e]; omega
        omega
    · have hxv : psi x = x - (k + 1) / 2 := by rw [hpsi]; simp [hxk]
      constructor
      · rw [hxv]; omega
      · rw [hxv]; omega
  -- `psi` is injective on `A`
  have hinj : Set.InjOn psi (↑A : Set ℕ) := by
    intro x hx y hy heq
    obtain ⟨h1, h2, h3⟩ := hbound x hx
    obtain ⟨h4, h5, h6⟩ := hbound y hy
    by_contra hne
    by_cases hxk : x < k
    · by_cases hyk : y < k
      · -- both below `k`: a collision forces `x + y = k`
        have hxv : psi x = min x (k - x) := by rw [hpsi]; simp [hxk]
        have hyv : psi y = min y (k - y) := by rw [hpsi]; simp [hyk]
        rw [hxv, hyv] at heq
        have hsumkey : x + y = k := by
          rcases Nat.le_total x (k - x) with e1 | e1 <;>
            rcases Nat.le_total y (k - y) with e2 | e2
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
      · -- `x` below, `y` above: the two value ranges are disjoint
        have hxv : psi x = min x (k - x) := by rw [hpsi]; simp [hxk]
        have hyv : psi y = y - (k + 1) / 2 := by rw [hpsi]; simp [hyk]
        rw [hxv, hyv] at heq
        have hminle : min x (k - x) ≤ k / 2 := by
          rcases Nat.le_total x (k - x) with e | e
          · rw [min_eq_left e]; omega
          · rw [min_eq_right e]; omega
        omega
    · by_cases hyk : y < k
      · -- `y` below, `x` above: symmetric
        have hxv : psi x = x - (k + 1) / 2 := by rw [hpsi]; simp [hxk]
        have hyv : psi y = min y (k - y) := by rw [hpsi]; simp [hyk]
        rw [hxv, hyv] at heq
        have hminle : min y (k - y) ≤ k / 2 := by
          rcases Nat.le_total y (k - y) with e | e
          · rw [min_eq_left e]; omega
          · rw [min_eq_right e]; omega
        omega
      · -- both above `k`: a shift of the identity
        rw [hpsi] at heq
        simp [hxk, hyk] at heq
        omega
  -- conclude by injection into a set of size `n - ⌈k/2⌉`
  have himg : A.image psi ⊆ Finset.Icc 1 (n - (k + 1) / 2) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨r1, r2⟩ := hrange y hy
    simp only [Finset.mem_Icc]
    omega
  calc A.card = (A.image psi).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (n - (k + 1) / 2)).card := Finset.card_le_card himg
    _ = n - (k + 1) / 2 := by rw [Nat.card_Icc]; omega

/-- **JSP-000299, general prescribed target.**  For `1 ≤ k ≤ n`, the
maximum size of a subset `A` of `{1, …, n}` such that no subset of `A` sums
to `k` is exactly `n - ⌈k/2⌉`. -/
theorem jsp000299_gen (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n ∧ A.card = n - (k + 1) / 2 ∧ ∀ T ⊆ A, T.sum id ≠ k) ∧
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (∀ T ⊆ A, T.sum id ≠ k) →
      A.card ≤ n - (k + 1) / 2 :=
  ⟨jsp000299_gen_lower n k hk hkn, fun A hA hA2 => jsp000299_gen_upper n k hk hkn A hA hA2⟩

/-! ## Beyond the range: the vacuous regime `n * (n + 1) / 2 < k` -/

/-- **JSP-000299, targets beyond the total sum.**  If `n * (n + 1) / 2 < k`
then no subset of `{1, …, n}` can sum to `k` at all, so the maximum is `n`. -/
theorem jsp000299_gen_far (n k : ℕ) (hfar : n * (n + 1) / 2 < k) :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = n ∧ ∀ T ⊆ A, T.sum id ≠ k) ∧
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (∀ T ⊆ A, T.sum id ≠ k) → A.card ≤ n := by
  classical
  have hsumIcc : ∀ m : ℕ, (Finset.Icc 1 m).sum id = m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hinsert : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hmem : (m + 1 : ℕ) ∉ Finset.Icc 1 m := by
        simp only [Finset.mem_Icc]
        omega
      rw [hinsert, Finset.sum_insert hmem, ih]
      have hprod : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
      rw [hprod, Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 2)]
      simp [id_eq, Nat.add_comm]
  have hsumIccN : (Finset.Icc 1 n).sum id = n * (n + 1) / 2 := hsumIcc n
  refine ⟨?_, ?_⟩
  · refine ⟨Finset.Icc 1 n, ?_, ?_, ?_⟩
    · exact fun a ha => ha
    · rw [Nat.card_Icc]
      omega
    · intro T hT
      have hsumle : T.sum id ≤ (Finset.Icc 1 n).sum id := Finset.sum_le_sum_of_subset hT
      rw [hsumIccN] at hsumle
      have hlt : T.sum id < k := lt_of_le_of_lt hsumle hfar
      exact Nat.ne_of_lt hlt
  · intro A hA hA2
    have hle := Finset.card_le_card hA
    rw [Nat.card_Icc] at hle
    omega

#print axioms jsp000299_lower
#print axioms jsp000299_upper
#print axioms jsp000299
#print axioms jsp000299_gen_lower
#print axioms jsp000299_gen_upper
#print axioms jsp000299_gen
#print axioms jsp000299_gen_far

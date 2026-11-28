import Mathlib

/-!
# A243700: The lexicographically earliest sequence of distinct terms with a(1) = 1 such that a(n) divides the sum of the first a(n) terms.

Source: https://oeis.org/A243700
Credit: @Solfanbtc

The entry carries two conjectures about the shape of the graph of `a`:

1. (Bill McEachen, May 21 2024) For `n > 1000`, `a(n)` falls within 1% of one of the six values
   `n, 1.576385 n, 1.788185 n, 2.576385 n, 2.788185 n, 3.576285 n`, using floor at the low bound
   and ceiling at the high bound, inclusive: for one of these six constants `c`,
   `⌊0.99 c n⌋ ≤ a(n) ≤ ⌈1.01 c n⌉`. The constants are taken exactly as printed (including
   `3.576285`).
2. (Hugo Pfoertner, Dec 19 2024) The asymptotic slopes of the 6 lines in the graph of `a` are
   `1, √3/3 + 1, √3/6 + 3/2, √3/3 + 2, √3/6 + 5/2, √3/3 + 3`. This is read as: the set of
   cluster points (limit points as `n → ∞`) of `a(n)/n` is exactly this set of six numbers.

Both are stated together below, as a conjunction.

Conventions:
* Indices are those of the entry (offset 1); a sequence is a function `ℕ → ℕ` with the unused
  value at `0` fixed to `0`. `Valid f` says: `f 1 = 1`, the terms `f n` (`n ≥ 1`) are positive
  and distinct, and every `f n` (`n ≥ 1`) divides `f 1 + ... + f (f n)`.
* `IsLexEarliest a` says `a` is valid and lexicographically below every other valid sequence:
  at the first index where they differ, `a` is smaller. (The set of valid sequences is closed
  in the product topology, as each condition involves finitely many terms, so it has a
  lexicographically least element as soon as it is nonempty.) `main` is stated for every such
  `a` (there is at most one).
* Checked in python on the b-file (n ≤ 100000): the terms are distinct and satisfy the
  divisibility condition; conjecture 1 holds for every `1000 < n ≤ 100000` (it fails at small
  `n`, e.g. `n = 11`, hence the bound `n > 1000`); for `n ≥ 50000` each `a(n)/n` lies within
  0.004 of one of the six slopes, each slope being attained.
-/

namespace OMA.S_oeis_a243700

open Filter

/-- The defining conditions of A243700 (indices from 1, value 0 at index 0). -/
def Valid (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ (∀ n, 1 ≤ n → 0 < f n) ∧ Function.Injective f ∧
    ∀ n, 1 ≤ n → f n ∣ ∑ i ∈ Finset.Icc 1 (f n), f i

/-- `a` is the lexicographically earliest valid sequence. -/
def IsLexEarliest (a : ℕ → ℕ) : Prop :=
  Valid a ∧ ∀ b, Valid b → b ≠ a → ∃ k, (∀ j < k, a j = b j) ∧ a k < b k

/-- McEachen's six constants. -/
def bandConstants : Set ℝ := {1, 1.576385, 1.788185, 2.576385, 2.788185, 3.576285}

/-- Pfoertner's six slopes. -/
noncomputable def slopes : Set ℝ :=
  {1, Real.sqrt 3 / 3 + 1, Real.sqrt 3 / 6 + 3 / 2, Real.sqrt 3 / 3 + 2,
    Real.sqrt 3 / 6 + 5 / 2, Real.sqrt 3 / 3 + 3}

/-- The two conjectures of A243700: the 1% bands for `n > 1000`, and the six asymptotic slopes
as the cluster points of `a(n)/n`. -/
theorem main : ∀ a : ℕ → ℕ, IsLexEarliest a →
    (∀ n : ℕ, 1000 < n → ∃ c ∈ bandConstants,
      ⌊0.99 * c * n⌋ ≤ (a n : ℤ) ∧ (a n : ℤ) ≤ ⌈1.01 * c * n⌉) ∧
    {x : ℝ | MapClusterPt x atTop (fun n : ℕ => (a n : ℝ) / n)} = slopes := by
  sorry

end OMA.S_oeis_a243700

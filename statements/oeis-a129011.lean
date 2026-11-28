import Mathlib

/-!
# A129011: a(n) = floor(n^(4/3)).

Source: https://oeis.org/A129011
Credit: @Solfanbtc

Conjecture (R. F. Churchhouse, 1971, as recorded by Peter Bala in A129011): every positive
integer `N` is the sum of two elements of this sequence. (Churchhouse verified it up to
`N = 10000` and proved that every sufficiently large `N` is `⌊n^s⌋ + ⌊m^s⌋` for any
`s ∈ (1, 4/3)`; the case `s = 4/3` is the conjecture.)

Formalization.
* `a(n) = ⌊n^(4/3)⌋` (real power), `n ≥ 0` (offset 0, so `a(0) = 0` is an element and, e.g.,
  `1 = a(1) + a(0)`).
* "Sum of two elements": `N = a(n) + a(m)` for some `n, m ≥ 0` (not necessarily distinct).

Checked with python3 (exact integer cube roots, `a(n) = ⌊(n^4)^(1/3)⌋`): the definition gives
all listed %S/%T/%U terms, and every `1 ≤ N ≤ 200000` is such a sum.
-/

namespace OMA.S_oeis_a129011

/-- A129011: `a(n) = ⌊n^(4/3)⌋`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (4 / 3 : ℝ)⌋₊

/-- Churchhouse's conjecture: every positive integer is `a(n) + a(m)`. -/
theorem main : ∀ N : ℕ, 1 ≤ N → ∃ n m : ℕ, N = a n + a m := by
  sorry

end OMA.S_oeis_a129011

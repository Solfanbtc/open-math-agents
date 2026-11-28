import Mathlib

/-!
# A111497: successive differences of ⌊10^n / Li(10^n) - 1⌋ are 2 or 3

Source: https://oeis.org/A111497
Name: "Difference between successive terms of floor(10^n/Li(10^n) - 1)", offset 1, with
`Li(x) = ∫_2^x dt / log t` (formula section of the entry). Writing
`f(n) = ⌊10^n / Li(10^n) - 1⌋`, the terms are differences `f(n+1) - f(n)`.
Conjecture of the entry: "2 and 3 are the only numbers in this sequence."

We state: for every `n ≥ 1`, `f(n+1) - f(n) ∈ {2, 3}`.

Notes.
* The entry's PARI program steps `x` by 2, so the listed data are the differences
  `f(x+1) - f(x)` for odd `x = 1, 3, 5, ...` only (python3 with 120-digit arithmetic reproduces
  all 100 listed terms this way, not with consecutive `n`). We follow the name, "successive
  terms", i.e. every `n ≥ 1`; this includes the odd `x` of the data.
* The PARI program uses `li(x) = ∫_0^x` (principal value) rather than `Li = li - li(2)`. Both give
  the same 100 listed terms, and both give differences in `{2, 3}` for all `1 ≤ n ≤ 202`. We use
  `Li` as defined in the entry.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a111497

/-- The offset logarithmic integral `Li(x) = ∫_2^x dt / log t`. -/
noncomputable def Li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- `f(n) = ⌊10^n / Li(10^n) - 1⌋`. -/
noncomputable def f (n : ℕ) : ℤ := ⌊(10 : ℝ) ^ n / Li ((10 : ℝ) ^ n) - 1⌋

theorem main : ∀ n : ℕ, 1 ≤ n → f (n + 1) - f n = 2 ∨ f (n + 1) - f n = 3 := by
  sorry

end OMA.S_oeis_a111497

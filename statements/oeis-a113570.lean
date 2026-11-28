import Mathlib

/-!
# A113570: fixed points of the harmonic-number divisibility function are prime powers

Source: https://oeis.org/A113570 (with https://oeis.org/A110545 and https://oeis.org/A025475)
`f(k)` (A110545) is the smallest positive integer `j` such that `k` divides either the numerator
or the denominator of the reduced harmonic number `H(j) = ∑_{i=1}^{j} 1/i`. A113570 lists the `k`
with `f(k) = k`: 1, 2, 4, 8, 9, 16, 27, 32, 64, 81, 125, 128, ...
Conjecture of the entry: "only prime powers are present (A025475) in addition to 1 and 2. Thus
this sequence would be a proper subset of A000961."

A025475 is 1 and the prime powers `p^e` with `e ≥ 2`. We state: every `k ≥ 1` with `f(k) = k` is
1, 2, or `p^e` for a prime `p` and `e ≥ 2`.

Conventions. `H j` is a rational number, automatically reduced (`Rat.num`, `Rat.den`). `f` is
defined with `sInf`; if no such `j` existed, `f(k)` would be `0 ≠ k`, so such `k` are not terms
(the source's search would not terminate on them).
Checked: an `#eval` (bounded search) reproduces `A110545(1..30)` and gives exactly 1, 2, 4, 8, 9,
16, 27, 32, 64, 81, 125, 128 as the fixed points `k < 131`, matching the data.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a113570

/-- The harmonic number `H(j) = ∑_{i=1}^{j} 1/i`. -/
def H (j : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 j, (1 : ℚ) / i

/-- A110545: the least positive `j` such that `k` divides the numerator or the denominator of
`H(j)`. -/
noncomputable def f (k : ℕ) : ℕ := sInf {j : ℕ | 0 < j ∧ ((k : ℤ) ∣ (H j).num ∨ k ∣ (H j).den)}

theorem main : ∀ k : ℕ, 1 ≤ k → f k = k →
    k = 1 ∨ k = 2 ∨ ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ k = p ^ e := by
  sorry

end OMA.S_oeis_a113570

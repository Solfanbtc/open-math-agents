import Mathlib

/-!
# A060298: Number of powers x^y (x,y > 1) with n digits.

Source: https://oeis.org/A060298
Credit: @Solfanbtc

`a(n)` counts the pairs `(x, y)` with `x, y ≥ 2` such that `x^y` has exactly `n` decimal digits,
i.e. `10^(n-1) ≤ x^y < 10^n`. Representations are counted with multiplicity (e.g. `16 = 2^4 = 4^2`
counts twice): this is what the data says (a(2) = 12, while there are only 8 distinct perfect
powers with 2 digits), and it matches the formula
`a(n) = Σ_{y=2..⌊n log_2 10⌋} (⌈10^(n/y)⌉ - ⌈10^((n-1)/y)⌉)`. Since `x^y < 10^n` forces
`x < 10^n` and `y < 4n`, the finite box below contains every such pair. Checked with python3:
the definition gives 3, 12, 34, 94, 263 for n = 1..5, as listed.

Conjectures (Robert G. Wilson v, 2012):
`lim a(2n)/10^n = 1 - 1/√10` and `lim a(2n-1)/10^n = 1/√10 - 1/10`.
The entry notes (Robert Israel, 2020) that these follow from the formula above, so they are
known results; `main` states them as in the entry.
-/

namespace OMA.S_oeis_a060298

/-- A060298(n): the number of pairs `(x, y)`, `x, y ≥ 2`, with `x^y` having `n` digits. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 2 (10 ^ n) ×ˢ Finset.Icc 2 (4 * n)).filter
    (fun p => 10 ^ (n - 1) ≤ p.1 ^ p.2 ∧ p.1 ^ p.2 < 10 ^ n)).card

open Filter Topology in
/-- Both limits conjectured by Wilson. -/
theorem main :
    Tendsto (fun n : ℕ => (a (2 * n) : ℝ) / 10 ^ n) atTop (𝓝 (1 - 1 / Real.sqrt 10)) ∧
    Tendsto (fun n : ℕ => (a (2 * n - 1) : ℝ) / 10 ^ n) atTop
      (𝓝 (1 / Real.sqrt 10 - 1 / 10)) := by
  sorry

end OMA.S_oeis_a060298

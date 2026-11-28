import Mathlib

/-!
# A011373: the number of 1's in the binary expansion of F(n) is asymptotic to (log_2 φ / 2) n

Source: https://oeis.org/A011373
Credit: @Solfanbtc

A011373 (offset 0): `a(n)` is the number of 1's in the binary expansion of the Fibonacci number
`F(n)` (A000120(A000045(n))). Data 0, 1, 1, 1, 2, 2, 1, 3, …

Conjecture (A. Eldar, May 13 2022): `Limit_{n->oo} a(n)/n = log_2(phi)/2 = 0.3471209568...`,
where `phi = (1 + sqrt 5)/2`. (Heuristically `F(n)` has about `n log_2 φ` binary digits, half of
them 1's. The entry also notes `a(n) → ∞` by a result of C. L. Stewart, which is much weaker.)

Checked with python3: `a(n)/n` is 0.3240, 0.3448, 0.3494 at `n = 1000, 5000, 20000`.
-/

namespace OMA.S_oeis_a011373

/-- A011373: the number of 1's in the binary expansion of `F(n)`. -/
def a (n : ℕ) : ℕ := (Nat.digits 2 (Nat.fib n)).count 1

open Filter Topology in
/-- Eldar's conjecture: `a(n)/n → log_2(φ)/2`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop
    (𝓝 (Real.logb 2 ((1 + Real.sqrt 5) / 2) / 2)) := by
  sorry

end OMA.S_oeis_a011373

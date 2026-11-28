import Mathlib

/-!
# A088913: a(n) = (Lucas(2n) + Lucas(2n+1)*phi)/kappa(phi/Fibonacci(4n)) where kappa(x) is the sum of successive remainders in computing the Euclidean algorithm for (1,x).

Source: https://oeis.org/A088913
Credit: @Solfanbtc

The Euclidean algorithm on `(1, x)`, `x > 0`: from a pair `(u, v)` with `v ≠ 0` the next pair is
`(v, u - ⌊u / v⌋ v)`; the successive remainders are the second components
`r_1 = 1 - ⌊1/x⌋ x`, `r_2`, ... (for irrational `x` the algorithm never stops; the pair
`(u, 0)` is kept fixed so that a terminating run contributes only zeros). `kappa(x)` is the sum
`r_1 + r_2 + ...` of all remainders (as in Peter Bala's worked example for `phi/3`, whose
remainders are `(3 - phi)/3`, `(2 phi - 3)/3`, ...). `phi` is the golden ratio,
`Lucas(0) = 2`, `Lucas(1) = 1`. We checked numerically (400 digits) that
`(Lucas(2n) + Lucas(2n+1) phi) / kappa(phi / F(4n))` equals all 16 terms of %S, %T, %U and
`Lucas(6n) - Lucas(2n)` for `n = 1..16`.

Conjecture (Peter Bala, 2026): `a(n) = Lucas(6n) - Lucas(2n)` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a088913

/-- Lucas numbers. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- One step of the Euclidean algorithm on a pair of reals. -/
noncomputable def step (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.2 = 0 then p else (p.2, p.1 - ⌊p.1 / p.2⌋ * p.2)

/-- `kappa(x)`: the sum of the successive remainders of the Euclidean algorithm on `(1, x)`. -/
noncomputable def kappa (x : ℝ) : ℝ := ∑' k : ℕ, (step^[k + 1] (1, x)).2

/-- `a(n)` as defined in the entry. -/
noncomputable def a (n : ℕ) : ℝ :=
  ((lucas (2 * n) : ℝ) + lucas (2 * n + 1) * Real.goldenRatio) /
    kappa (Real.goldenRatio / Nat.fib (4 * n))

/-- Bala's conjecture: `a(n) = Lucas(6n) - Lucas(2n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (lucas (6 * n) : ℝ) - lucas (2 * n) := by
  sorry

end OMA.S_oeis_a088913

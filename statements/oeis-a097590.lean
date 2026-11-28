import Mathlib

/-!
# A097590: a(n) = Sum_{i=2..n} A055211(i).

Source: https://oeis.org/A097590
Credit: @Solfanbtc

A055211(i) (`i ≥ 2`, lesser Fortunate numbers) is the least `m > 1` such that `p_i# - m` is prime,
where `p_i#` is the product of the first `i` primes. A097590 (offset 2) is
`a(n) = ∑_{i=2}^{n} A055211(i)`: 3, 10, 21, 34, 51, 80, ... A007504(n) is the sum of the first `n`
primes.

Conjecture (in the entry, %F): `F(n) = a(n) / A007504(n) → π/2` as `n → ∞`. (The same limit is
claimed in A055211 by P. Cami, 2017, while A. Rocchelli, 2022, conjectures the limit `3/2` there,
so the two conjectures are incompatible.) python3 reproduces the data and gives
`F(40) ≈ 1.555`, `F(80) ≈ 1.572`, `F(120) ≈ 1.603`, `F(160) ≈ 1.579`.

Conventions: `p_i# = primorial (p_i)` with `p_i = Nat.nth Nat.Prime (i - 1)` (Mathlib's
`primorial m` is the product of the primes `≤ m`); the condition `m < p_i#` only keeps the natural
subtraction honest. The sequence index `n` starts at 2; the limit does not depend on the values at
smaller `n`.
-/

namespace OMA.S_oeis_a097590

open Filter Topology Real

/-- The `i`-th primorial `p_i#`. -/
noncomputable def P (i : ℕ) : ℕ := primorial (Nat.nth Nat.Prime (i - 1))

/-- The lesser Fortunate number A055211(i). -/
noncomputable def lesserFortunate (i : ℕ) : ℕ := sInf {m | 1 < m ∧ m < P i ∧ (P i - m).Prime}

/-- A097590(n) = ∑_{i=2}^{n} A055211(i). -/
noncomputable def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 2 n, lesserFortunate i

/-- Conjecture: `a(n) / A007504(n) → π / 2`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℝ))
      atTop (𝓝 (π / 2)) := by
  sorry

end OMA.S_oeis_a097590

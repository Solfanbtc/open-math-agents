import Mathlib

/-!
# A112302: quadratic recurrence constant `√(1 √(2 √(3 √(4 ⋯))))`

Source: https://oeis.org/A112302
Credit: @Solfanbtc

The constant `σ = √(1 · √(2 · √(3 · ⋯))) = ∏_{n ≥ 1} n^(1/2^n) = 1.66168794963359412129…`
(OEIS formulas, Sondow; equivalently `exp(∑_{n ≥ 2} log(n)/2^n)`, Bhatt). Below
`σ = exp(∑_{n ≥ 1} log(n)/2^n)`.

Conjecture (Johannes W. Meijer, Jun 27 2016, OEIS comment): with `Φ(z, p, q)` the Lerch
transcendent, define `LP(0) = 1` and `LP(n) = (1/n) ∑_{k=0}^{n-1} Φ(1/2, n-k, 1) LP(k)`; then
`lim_{n→∞} LP(n) = σ`. Here only `Φ(1/2, s, 1) = ∑_{k ≥ 0} (1/2)^k / (k+1)^s` with integer
`s = n - k ≥ 1` occurs (a convergent series of positive terms). Numerically
`LP(40) = 1.6616879496334…`, `LP(79) = 1.661687949633594`.
-/

namespace OMA.S_oeis_a112302

/-- The Lerch transcendent `Φ(1/2, s, 1) = ∑_{k ≥ 0} (1/2)^k / (k+1)^s`, for `s : ℕ`. -/
noncomputable def lerchHalf (s : ℕ) : ℝ := ∑' k : ℕ, (1 / 2 : ℝ) ^ k / ((k : ℝ) + 1) ^ s

/-- Meijer's `LP(n)`. -/
noncomputable def LP : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / ((n : ℝ) + 1)) *
      ∑ k : Fin (n + 1), lerchHalf (n + 1 - k) * LP k
decreasing_by exact k.isLt

/-- The quadratic recurrence constant `σ = ∏_{n ≥ 1} n^(1/2^n) = exp(∑_{n ≥ 1} log(n)/2^n)`. -/
noncomputable def σ : ℝ := Real.exp (∑' n : ℕ, Real.log ((n : ℝ) + 1) / 2 ^ (n + 1))

/-- Meijer's conjecture: `LP(n) → σ`. -/
theorem main : Filter.Tendsto LP Filter.atTop (nhds σ) := by
  sorry

end OMA.S_oeis_a112302

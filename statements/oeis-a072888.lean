import Mathlib

/-!
# A072888: Sum of the coefficients of the Schur function expansion of the square of the Vandermonde determinant in n variables.

Source: https://oeis.org/A072888
Credit: @Solfanbtc

Mathlib has no Schur functions, so we use the bialternant formula. Let
`Δ = ∏_{i<j} (x_i - x_j) = det(x_i^(n-1-j)) = a_δ` with `δ = (n-1, …, 1, 0)`, and
`s_λ = a_{λ+δ} / a_δ`, where `a_α = Σ_σ sgn(σ) x^(σ·α)`. If `Δ² = Σ_λ c_λ s_λ`, then
`Δ³ = Σ_λ c_λ a_{λ+δ}`. The alternants `a_{λ+δ}` have disjoint supports, and `x^(λ+δ)` occurs in
`a_{λ+δ}` with coefficient `1`, so `c_λ` is the coefficient of `x^(λ+δ)` in `Δ³`. The exponent
vectors `λ + δ` are exactly the strictly decreasing ones. Hence

  `a(n) = Σ_λ c_λ = Σ_{α strictly decreasing} [x^α] Δ³`.

(Checked in Python for `n = 2, …, 6`: `-2, -14, 70, 910, -7280`, the first terms of the data;
e.g. `n = 3`: `Δ² = s_{42} - 3 s_{411} - 3 s_{33} + 6 s_{321} - 15 s_{222}`, sum `-14`.)

Conjecture (Brian G. Wybourne, in the entry), for `n ≥ 2` (the offset):
`a(n) = ∏_{x=0}^{⌊n/2⌋} (1 - 3x) · ∏_{x=0}^{⌊(n-1)/2⌋} (6x + 1)`.
-/

namespace OMA.S_oeis_a072888

open MvPolynomial

/-- The Vandermonde determinant `∏_{i<j} (x_i - x_j)` in `n` variables. -/
noncomputable def vandermonde (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then (X i - X j) else 1

open Classical in
/-- A072888: the sum of the Schur coefficients of `Δ²`, i.e. of the coefficients of `Δ³` at
strictly decreasing exponent vectors. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ α ∈ ((vandermonde n) ^ 3).support.filter (fun α : Fin n →₀ ℕ => StrictAnti (fun i => α i)),
    coeff α ((vandermonde n) ^ 3)

theorem main : ∀ n : ℕ, 2 ≤ n →
    a n = (∏ x ∈ Finset.range (n / 2 + 1), (1 - 3 * (x : ℤ))) *
      ∏ x ∈ Finset.range ((n - 1) / 2 + 1), (6 * (x : ℤ) + 1) := by
  sorry

end OMA.S_oeis_a072888

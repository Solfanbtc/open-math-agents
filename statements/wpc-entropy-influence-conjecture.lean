import Mathlib

/-!
# Friedgut–Kalai entropy–influence conjecture

Source: https://en.wikipedia.org/wiki/Entropy_influence_conjecture
Credit: @Solfanbtc

From the source: for a function `f : {-1, 1} ^ n → {-1, 1}` with Fourier expansion
`f x = ∑_{S ⊆ [n]} f̂ S * x_S`, where `x_S = ∏_{i ∈ S} x i`, the entropy–influence conjecture
states that there exists an absolute constant `C` such that `H f ≤ C * I f`, where the total
influence is `I f = ∑_S |S| * f̂ S ^ 2` and the entropy of the spectrum is
`H f = - ∑_S f̂ S ^ 2 * log (f̂ S ^ 2)` (with `x log x` taken to be `0` when `x = 0`).
The conjecture is due to Ehud Friedgut and Gil Kalai (1996).

Encoding: `{-1, 1}` is the group of units `ℤˣ` of `ℤ`, so the cube is `Fin n → ℤˣ`. The
Fourier coefficients are given by the usual inversion formula
`f̂ S = 2 ^ (-n) * ∑_x f x * x_S`, which is the unique choice making the expansion of the source
hold, since the characters `x ↦ x_S` are orthonormal for the uniform average. The logarithm is
the natural one (`Real.log`): a change of base only rescales `H` and is absorbed by `C`; and
`Real.log 0 = 0`, so the term of a vanishing coefficient is `0`, as in the source.
-/

namespace OMA.S_wpc_entropy_influence_conjecture

/-- The character `x_S = ∏_{i ∈ S} x i`, as a real number `±1`. -/
def character {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℤˣ) : ℝ :=
  (((∏ i ∈ S, x i : ℤˣ) : ℤ) : ℝ)

/-- The Fourier coefficient `f̂ S = 2 ^ (-n) * ∑_x f x * x_S`. -/
noncomputable def fourierCoeff {n : ℕ} (f : (Fin n → ℤˣ) → ℤˣ) (S : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → ℤˣ, (((f x : ℤ) : ℝ)) * character S x

/-- The total influence `I f = ∑_S |S| * f̂ S ^ 2`. -/
noncomputable def totalInfluence {n : ℕ} (f : (Fin n → ℤˣ) → ℤˣ) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f S ^ 2

/-- The entropy of the spectrum `H f = - ∑_S f̂ S ^ 2 * log (f̂ S ^ 2)`. -/
noncomputable def spectralEntropy {n : ℕ} (f : (Fin n → ℤˣ) → ℤˣ) : ℝ :=
  - ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * Real.log (fourierCoeff f S ^ 2)

/-- **Entropy–influence conjecture** (Friedgut–Kalai): there is an absolute constant `C` such
that every Boolean function `f : {-1, 1} ^ n → {-1, 1}`, for every `n`, satisfies
`H f ≤ C * I f`. -/
theorem main : ∃ C : ℝ, ∀ (n : ℕ) (f : (Fin n → ℤˣ) → ℤˣ),
    spectralEntropy f ≤ C * totalInfluence f := by
  sorry

end OMA.S_wpc_entropy_influence_conjecture

import Mathlib

/-!
# A074760: Decimal expansion of lambda(1) in Li's criterion

Source: https://oeis.org/A074760
Credit: @Solfanbtc

The constant is `λ₁ = -B = (1/2) ∑_ρ 1/(ρ(1-ρ))` over the nontrivial zeros `ρ` of the Riemann
zeta function, the first Li coefficient; by the OEIS formula (classical),
`λ₁ = γ/2 + 1 - log(4π)/2 = 0.0230957089661210338…`, with `γ` the Euler–Mascheroni constant.
We use this closed form as the definition.

Open problem (OEIS comment, Charles R Greathouse IV, Nov 12 2021, after Gun, Murty & Rath,
2018): "it is not even known whether this constant is rational or not", though Gun, Murty and
Rath show it is transcendental under Schanuel's conjecture. The question is stated, as is
customary, in its expected form: `λ₁` is irrational.
-/

namespace OMA.S_oeis_a074760

/-- `λ₁ = γ/2 + 1 - log(4π)/2`, the first Li coefficient. -/
noncomputable def lambda1 : ℝ :=
  Real.eulerMascheroniConstant / 2 + 1 - Real.log (4 * Real.pi) / 2

/-- Is `λ₁` irrational? (Open; transcendental under Schanuel's conjecture.) -/
theorem main : Irrational lambda1 := by
  sorry

end OMA.S_oeis_a074760

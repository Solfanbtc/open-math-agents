import Mathlib

/-!
# A085108: Decimal expansion of Σ 1/(p 2^p) over the Artin primes for 2.

Source: https://oeis.org/A085108
Credit: @Solfanbtc

The constant is `α = Σ 1/(p * 2^p)` over the primes `p` for which `2` is a primitive root
(`orderOf (2 : ZMod p) = p - 1`; `p = 2` is excluded, since there `2 = 0`). Its decimal
expansion is A085108: `α = 0.04797054634644652348828730998094732…` (checked with python3 from
the primes below 400, with exact rationals, matching the listed digits).

Conjecture (David H. Bailey and Richard E. Crandall): `α` is 2-normal, i.e. normal in base 2.
The definition of normality in base `b` copies upstream
`FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean` (`digitSeq`, `IsNormalInBase`):
every string of `k` base-`b` digits occurs in the fractional expansion with asymptotic
frequency `1/b^k`.
-/

namespace OMA.S_oeis_a085108

open Filter Topology

/-- The `n`-th digit (0-indexed) after the radix point in the base-`b` expansion of `x`. -/
noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

/-- `x` is normal in base `b`: every string `w` of `k` digits `< b` occurs with asymptotic
frequency `1 / b ^ k`. -/
def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun i => ∀ j : Fin k, digitSeq b x (i + j) = w j)).card : ℝ) / n)
      atTop (𝓝 (1 / (b : ℝ) ^ k))

/-- The primes with primitive root `2`. -/
def ArtinPrime (p : ℕ) : Prop := p.Prime ∧ orderOf (2 : ZMod p) = p - 1

/-- The constant `Σ_{p Artin prime} 1/(p 2^p)`. -/
noncomputable def α : ℝ := ∑' p : {p : ℕ // ArtinPrime p}, 1 / ((p : ℝ) * 2 ^ (p : ℕ))

/-- The Bailey–Crandall conjecture: `α` is normal in base 2. -/
theorem main : IsNormalInBase 2 α := by
  sorry

end OMA.S_oeis_a085108

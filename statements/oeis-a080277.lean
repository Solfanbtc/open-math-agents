import Mathlib

/-!
# A080277: Partial sums of A038712

Source: https://oeis.org/A080277
Credit: @Solfanbtc

A038712 (offset 1): `A038712(k) = 2^(v₂(k)+1) - 1`, where `v₂(k)` is the exponent of the highest
power of `2` dividing `k`: `1, 3, 1, 7, 1, 3, 1, 15, …`. A080277 (offset 1):
`a(n) = ∑_{k=1}^{n} A038712(k)`: `1, 4, 5, 12, 13, 16, 17, 32, …`.

Conjecture (Klaus Brockhaus, Mar 23 2003, OEIS formula): `a(n)` is asymptotic to
`n log(n)/log(2)`.

Status: SOLVED. The entry points to Bannister et al. (2013), who prove
`n log₂ n - 2n < a(n) ≤ n log₂ n + n` (OEIS formula, David Eppstein), which gives the asymptotic.
Stated faithfully as `a ~ n log n / log 2` (`Asymptotics.IsEquivalent` at `atTop`).
-/

namespace OMA.S_oeis_a080277

/-- A038712: `2^(v₂(k)+1) - 1`. -/
def A038712 (k : ℕ) : ℕ := 2 ^ (padicValNat 2 k + 1) - 1

/-- A080277: partial sums of A038712. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A038712 k

/-- Brockhaus' conjecture (proved by Bannister et al.): `a(n) ~ n log n / log 2`. -/
theorem main : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => (n : ℝ) * Real.log n / Real.log 2) := by
  sorry

end OMA.S_oeis_a080277

import Mathlib

/-!
# A138312: Decimal expansion of Mertens's constant B_3 minus Euler's constant.

Source: https://oeis.org/A138312 (see also https://oeis.org/A083343, https://oeis.org/A138313)
Credit: @Solfanbtc

The constant is `B_3 - γ = 0.7553666108...`, which the entry also gives as
`∑_{p prime} log p / (p (p - 1))`; we use this series as its definition (it converges absolutely).

Conjecture (entry comment): the constant equals
`κ = lim_{n→∞} (∑_{k=1..n} μ(k)^2 / φ(k) - H_n)`,
`μ` the Möbius function, `φ` Euler's totient, `H_n` the `n`-th harmonic number. We state that the
limit exists and equals the constant.

Status: this follows from known results: Ward (1927) proved
`∑_{k ≤ n} μ(k)^2/φ(k) - log n → B_3` (formula in A083343), `H_n - log n → γ`, and
`B_3 = γ + ∑_p log p/(p(p-1))` by Mertens's theorem. We state it faithfully nevertheless.

Sanity check (python): the difference is 0.75574, 0.75537, 0.75536, 0.75538 at
`n = 10^4, 10^5, 10^6, 2·10^6`, and the prime series (truncated at `2·10^6`) is 0.755366.
-/

namespace OMA.S_oeis_a138312

open Filter

/-- The constant `B_3 - γ = ∑_{p prime} log p / (p (p - 1))`. -/
noncomputable def c : ℝ := ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))

/-- `∑_{k=1..n} μ(k)^2 / φ(k) - H_n`. -/
noncomputable def kappaSeq (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, ((ArithmeticFunction.moebius k : ℝ) ^ 2 / (Nat.totient k : ℝ)))
    - (harmonic n : ℝ)

/-- The conjecture: `κ = lim (∑_{k ≤ n} μ(k)^2/φ(k) - H_n)` exists and equals `B_3 - γ`. -/
theorem main : Tendsto kappaSeq atTop (nhds c) := by
  sorry

end OMA.S_oeis_a138312

import Mathlib

/-!
# A110464: Oddly colossally abundant numbers.

Source: https://oeis.org/A110464
Credit: @Solfanbtc

Conjecture (OEIS A110464, %C line): the ratio of consecutive oddly colossally abundant numbers
is always a prime number (those primes are listed in A110465).

Definition (from the same comment): the usual colossally abundant numbers (A004490) are the
`m > 1` for which some `ε > 0` gives `σ(m)/m^(1+ε) ≥ σ(k)/k^(1+ε)` for all `k > 1`; oddly
colossally abundant numbers are defined similarly, except that only odd primes are allowed in
the factorization, i.e. `m` and the competitors `k` range over odd numbers `> 1`.

Formalization.
* `IsOddlyCA m`: `m` odd, `m > 1`, and some real `ε > 0` gives
  `σ(k)/k^(1+ε) ≤ σ(m)/m^(1+ε)` for every odd `k > 1` (real powers). This mirrors upstream
  `ColossallyAbundantNumber.IsColossallyAbundant` (FormalConjectures/Wikipedia), restricted to
  odd numbers; that file's ratio conjecture concerns the usual (even) CANs and does not cover
  this odd analogue.
* The terms in increasing order are `Nat.nth IsOddlyCA j`. The set is infinite; were it finite,
  `Nat.nth` would return `0` from some index on and the claim at the last term would read
  `0 = p * m` with `m ≥ 3`, which is false, so no junk value makes the statement easier.

Checked with python3: maximizing `σ(k)/k^(1+ε)` over odd `k` (prime by prime) for `ε` from `1`
down to `0.003` yields exactly the listed %S/%T/%U terms `3, 15, 45, 315, ..., 6181604729214089175`
as the first 18 maximizers, and the first 27 maximizers have prime consecutive ratios.
-/

namespace OMA.S_oeis_a110464

open scoped ArithmeticFunction.sigma

/-- Oddly colossally abundant numbers. -/
def IsOddlyCA (m : ℕ) : Prop :=
  Odd m ∧ 1 < m ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ k : ℕ, Odd k → 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 m : ℝ) / (m : ℝ) ^ (1 + ε)

/-- The ratio of consecutive oddly colossally abundant numbers is a prime. -/
theorem main : ∀ j : ℕ, ∃ p : ℕ, p.Prime ∧ Nat.nth IsOddlyCA (j + 1) = p * Nat.nth IsOddlyCA j := by
  sorry

end OMA.S_oeis_a110464

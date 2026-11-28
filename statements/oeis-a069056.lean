import Mathlib

/-!
# A069056: Numbers k such that Sum_{d|k} d^2*mu(d) divides k^2.

Source: https://oeis.org/A069056 (cf. A063453, A046970)
Credit: @Solfanbtc

The entry (Benoit Cloitre) conjectures the analogue for higher exponents:
if `c > 2` and `n > 1`, then `Sum_{d|n} d^c * mu(d)` never divides `n^c`
(in particular A063453(n) = `Sum_{d|n} mu(d) d^3` never divides `n^3` for `n > 1`).

The sum is an integer (it equals `∏_{p | n} (1 - p^c)`, which is negative for some `n`), so
divisibility is stated in `ℤ`. Checked numerically for `3 ≤ c ≤ 8`, `2 ≤ n ≤ 20000`.
-/

namespace OMA.S_oeis_a069056

open ArithmeticFunction

/-- `Sum_{d|n} d^c * mu(d)`, an integer. -/
def moebiusPowerSum (c n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) ^ c * moebius d

/-- Conjecture (OEIS A069056): for `c > 2` and `n > 1`, `Sum_{d|n} d^c mu(d)` does not
divide `n^c`. -/
theorem main : ∀ c n : ℕ, 2 < c → 1 < n → ¬ moebiusPowerSum c n ∣ (n : ℤ) ^ c := by
  sorry

end OMA.S_oeis_a069056

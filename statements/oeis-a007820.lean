import Mathlib

/-!
# A007820: Stirling numbers of second kind S(2n,n).

Source: https://oeis.org/A007820
Credit: @Solfanbtc

Conjecture (Peter Bala, Mar 30 2025, OEIS A007820): a(2n+1) is divisible by (2n+1)^2, where
a(m) = S(2m, m) is the Stirling number of the second kind (offset 0, so n ranges over all
natural numbers). Mathlib's `Nat.stirlingSecond n k` is S(n, k).
Checked numerically for 0 <= n < 100.
-/

namespace OMA.S_oeis_a007820

theorem main : ∀ n : ℕ,
    (2 * n + 1) ^ 2 ∣ Nat.stirlingSecond (2 * (2 * n + 1)) (2 * n + 1) := by
  sorry

end OMA.S_oeis_a007820

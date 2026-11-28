import Mathlib

/-!
# A071561: Numbers with no middle divisors (cf. A071090).

Source: https://oeis.org/A071561
Credit: @Solfanbtc

Conjecture (OEIS A071561): lim_{n→∞} a(n)/n = 4/3.
(The entry adds, Amiram Eldar, Jul 27 2024: numerical calculations suggest that this limit is
smaller than 4/3; see A071540. The statement below is the conjecture as recorded.)

Definitions: a middle divisor of k is a divisor d with sqrt(k/2) <= d < sqrt(2k) (comment of
Michael B. Porter), i.e. k <= 2 d^2 and d^2 < 2k; a(n) is the n-th positive integer without
middle divisors (offset 1: 3, 5, 7, 10, 11, 13, ...), `Nat.nth` at n - 1.
Checked numerically: the listed terms are reproduced; a(n)/n = 1.3382 for the last term below 10^6.
-/

namespace OMA.S_oeis_a071561

open Filter

/-- `k` has no middle divisor. -/
def NoMiddleDivisor (k : ℕ) : Prop := 0 < k ∧ ∀ d : ℕ, d ∣ k → ¬ (k ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * k)

/-- a(n), the n-th number without middle divisors (n ≥ 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth NoMiddleDivisor (n - 1)

theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds (4 / 3)) := by
  sorry

end OMA.S_oeis_a071561

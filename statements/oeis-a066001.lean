import Mathlib

/-!
# A066001: Sum of digits of 5^n.

Source: https://oeis.org/A066001
Credit: @Solfanbtc

Conjecture (M. F. Hasler, OEIS A066001, comment, May 18 2017): a(n) ~ 4.5*log_10(5)*n.
(The same comment notes the periodicity of a(n) mod 9 and a(n) ≡ (-1)^n (mod 3), which are
elementary facts, not conjectures, and are not stated.)

Conventions:
* a(n) is the base-10 digit sum of 5^n (offset 0), `(Nat.digits 10 (5 ^ n)).sum`.
* "a(n) ~ 4.5 log_10(5) n" is a(n) / (4.5 · log_10(5) · n) → 1 as n → ∞, in ℝ, with
  log_10(5) = `Real.logb 10 5`. (The constant is the expected value 4.5 of a decimal digit
  times the number ≈ n log_10(5) of digits of 5^n.)
* Per the entry, a(10^3)/log_10(5) ≈ 4538 and a(10^4)/log_10(5) ≈ 44518, i.e. ratios 1.008 and
  0.989 against 4.5 n.
-/

namespace OMA.S_oeis_a066001

open Filter Topology

/-- A066001: the digit sum of `5^n`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 (5 ^ n)).sum

/-- Hasler's conjecture: `a(n) ~ 4.5 log₁₀(5) n`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (4.5 * Real.logb 10 5 * n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a066001

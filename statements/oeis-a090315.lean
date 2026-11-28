import Mathlib

/-!
# A090315: Least k such that k and digit reversal of k both have n divisors, or 0 if no such number exists.

Source: https://oeis.org/A090315
Credit: @Solfanbtc

For `n ≥ 1` (offset 1), `a(n)` is the least positive `k` such that `k` and its decimal digit
reversal both have exactly `n` divisors, or `0` if no such `k` exists (e.g. `a(8) = 24`,
`τ(24) = τ(42) = 8`). Conjecture (Amarnath Murthy, OEIS %C): there are infinitely many nonzero
terms as well as infinitely many zeros. A term is nonzero exactly when such a `k` exists, so
the statement is: both the set of `n ≥ 1` for which some `k` exists and the set of `n ≥ 1` for
which none exists are infinite. (No zero has been proved: D. Wasserman notes that all zeros
in the data are unproved.)

Digit reversal (A004086) drops leading zeros, e.g. `rev 10 = 1`.
-/

namespace OMA.S_oeis_a090315

/-- Decimal digit reversal of `k`. -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- Some positive `k` and its reversal both have exactly `n` divisors (`a(n) ≠ 0`). -/
def HasTerm (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k.divisors.card = n ∧ (rev k).divisors.card = n

theorem main : {n : ℕ | 1 ≤ n ∧ HasTerm n}.Infinite ∧ {n : ℕ | 1 ≤ n ∧ ¬ HasTerm n}.Infinite := by
  sorry

end OMA.S_oeis_a090315

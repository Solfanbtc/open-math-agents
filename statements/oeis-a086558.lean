import Mathlib

/-!
# A086558: Smallest n-digit number beginning with n and having prime signature of n, or 0 if no such number exists.

Source: https://oeis.org/A086558
Credit: @Solfanbtc

For `n ≥ 1`, an admissible number is an `x` with exactly `n` decimal digits, whose decimal
expansion begins with that of `n`, and with the same prime signature as `n` (the multiset of
exponents in the prime factorization). `a(n)` is the least admissible number, or 0 if there is
none. Examples: `a(4) = 4489 = 67^2` (`4 = 2^2`), `a(12) = 120000000004 = 2^2 · 30000000001`.

Conjecture (A. Murthy): no term is zero, i.e. for every `n ≥ 1` an admissible number exists.
`main` states this.
-/

namespace OMA.S_oeis_a086558

/-- Prime signature: the multiset of exponents in the prime factorization. -/
def signature (x : ℕ) : Multiset ℕ := x.primeFactors.val.map x.factorization

/-- `x` is an `n`-digit number beginning with `n` and having the prime signature of `n`. -/
def Admissible (n x : ℕ) : Prop :=
  (Nat.digits 10 x).length = n ∧ (Nat.digits 10 n).reverse <+: (Nat.digits 10 x).reverse ∧
    signature x = signature n

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ x : ℕ, Admissible n x := by
  sorry

end OMA.S_oeis_a086558

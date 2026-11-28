import Mathlib

/-!
# A082770: a(n) = smallest palindromic prime that begins with A082768(n) and contains more than twice the number of digits in A082768(n), or 0 if no such number exists.

Source: https://oeis.org/A082770
Credit: @Solfanbtc

A082768 lists the positive integers whose leading decimal digit is 1, 3, 7 or 9.
"Begins with m" means that the decimal expansion of `m` is an initial segment of that of
the prime (most significant digit first). `Nat.digits 10` lists digits least significant
first, so this is `(Nat.digits 10 m).reverse <+: (Nat.digits 10 p).reverse`.

Conjecture (Amarnath Murthy, 2003): no entry is zero, i.e. for every positive `m` with
leading digit 1, 3, 7 or 9, with `k` decimal digits, there is a palindromic prime that begins
with `m` and has more than `2k` digits. (The question in the entry, about the first entry
needing more than `2k + 1` digits, was answered by D. Wasserman: a(37) = 9200029 for
A082768(37) = 92; it is not part of the statement.)
-/

namespace OMA.S_oeis_a082770

/-- Murthy's conjecture: no term of A082770 is zero. -/
theorem main : ∀ m : ℕ, 0 < m →
    (Nat.digits 10 m).getLast? ∈ ({some 1, some 3, some 7, some 9} : Set (Option ℕ)) →
    ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧
      2 * (Nat.digits 10 m).length < (Nat.digits 10 p).length ∧
      (Nat.digits 10 m).reverse <+: (Nat.digits 10 p).reverse := by
  sorry

end OMA.S_oeis_a082770

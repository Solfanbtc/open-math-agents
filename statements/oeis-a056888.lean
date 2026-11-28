import Mathlib

/-!
# A056888: a(n) = number of k such that sum of digits of 9^k is 9n.

Source: https://oeis.org/A056888
Credit: @Solfanbtc

Conjecture (OEIS A056888, comment by N. J. A. Sloane, Jan 06 2011): "All terms except the
first are only conjectures": the listed values (computed numerically by Michael Kleber and
David W. Wilson, 2000) are the true counts. `main` states every listed term of %S, %T, %U
(n = 1..99). The finiteness of each count is a theorem (Senge-Straus, Stewart), and a(1) = 2
was proved by Mark Sapir; both are included for completeness.

Conventions:
* k ranges over all natural numbers (9^0 = 1 has digit sum 1, which is not of the form 9n with
  n ≥ 1). The digit sum is in base 10 (`Nat.digits 10`).
* "the number of k" is `Set.ncard` together with `Set.Finite` (`ncard` alone would be 0 for an
  infinite set, which would make the terms equal to 0 vacuous).
* Checked in Python: for 0 ≤ k < 15000 the counts reproduce all 99 listed terms, and every
  digit sum of 9^k with 3000 < k < 15000 is at least 12519 > 9·99.
-/

namespace OMA.S_oeis_a056888

/-- The listed terms a(1), ..., a(99). -/
def terms : List ℕ :=
  [2, 3, 2, 0, 4, 1, 3, 1, 1, 5, 2, 2, 3, 1, 0, 3, 6, 2, 3, 0, 0, 4, 1, 3, 1, 4, 1, 1, 0, 1, 3, 2,
    3, 5, 1, 1, 3, 3, 2, 5, 0, 3, 3, 1, 1, 3, 2, 2, 0, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4, 5, 1, 0, 1, 3,
    2, 1, 2, 4, 5, 1, 1, 2, 1, 0, 1, 2, 4, 1, 2, 5, 0, 2, 4, 3, 2, 2, 1, 2, 2, 2, 0, 2, 3, 2, 1, 5,
    1, 0, 4]

/-- The set of `k` such that the digit sum of `9^k` is `9n`. -/
def ks (n : ℕ) : Set ℕ := {k : ℕ | (Nat.digits 10 (9 ^ k)).sum = 9 * n}

/-- The listed values of A056888 are correct. -/
theorem main :
    ∀ i (hi : i < terms.length),
      (ks (i + 1)).Finite ∧ (ks (i + 1)).ncard = terms.get ⟨i, hi⟩ := by
  sorry

end OMA.S_oeis_a056888

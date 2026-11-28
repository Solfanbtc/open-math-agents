import Mathlib

/-!
# A002121: a(0) = 1, a(1) = 0, a(2) = -1; for n >= 3, a(n) = - a(n-2) + Sum_{ primes p with 3 <= p <= n} a(n-p).

Source: https://oeis.org/A002121
Credit: @Solfanbtc

The comment selected by the desk ("Arises in studying the Goldbach conjecture") makes no
claim. The entry's only conjecture is the next comment (T. D. Noe, Dec 05 2006):
the last negative term appears to be a(303).

This is stated as: a(303) < 0 and a(n) >= 0 for every n > 303.

The sequence is defined exactly as in the name, by strong recursion. Evaluated with `#eval`,
the first terms are 1, 0, -1, 1, 1, -1, 0, 2, 0, -2, 2, 4, -3, -2, 8, 1, -8, 8, 12, -11,
matching the data. Checked in Python: a(303) = -92116085548584644050 and no term
a(n) with 303 < n < 6000 is negative.
-/

namespace OMA.S_oeis_a002121

/-- A002121. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | n + 3 =>
      -a (n + 1) + ∑ p : Fin (n + 4), if h : 3 ≤ (p : ℕ) ∧ (p : ℕ).Prime then
        (have : n + 3 - p < n + 3 := by omega
         a (n + 3 - p)) else 0

/-- Conjecture: the last negative term is a(303). -/
theorem main : a 303 < 0 ∧ ∀ n : ℕ, 303 < n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a002121

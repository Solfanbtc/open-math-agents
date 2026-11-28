import Mathlib

/-!
# A101902: Numbers n that are not of the form ab+bc+cd+de+ea with 1<=a<=b<=c<=d<=e.

Source: https://oeis.org/A101902
Credit: @Solfanbtc

Conjecture (T. D. Noe, in the entry): the sequence 1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62
is complete.

Status: solved. Ivan Neretin (OEIS comment, Dec 14 2016) proved completeness: every
sufficiently large n has a representation in one of seven explicit families according to
n mod 7 (e.g. n = 7k + 1 with (a,b,c,d,e) taken from {1, 1, 1, 6, k - 1}), smaller numbers
being checked individually; the entry carries the keywords fini, full.

Formalization: for every positive integer `n`, `n` has no representation
`n = ab + bc + cd + de + ea` with `1 ≤ a ≤ b ≤ c ≤ d ≤ e` if and only if `n` is one of the 13
listed terms. (Checked with python3 for n ≤ 1500.)
-/

namespace OMA.S_oeis_a101902

/-- `n = ab + bc + cd + de + ea` for some `1 ≤ a ≤ b ≤ c ≤ d ≤ e`. -/
def Representable (n : ℕ) : Prop :=
  ∃ a b c d e : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
    n = a * b + b * c + c * d + d * e + e * a

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (¬ Representable n ↔ n ∈ ({1, 2, 3, 4, 6, 8, 12, 14, 18, 30, 38, 42, 62} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a101902

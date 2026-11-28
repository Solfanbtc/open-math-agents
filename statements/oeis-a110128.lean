import Mathlib

/-!
# A110128: Number of permutations p of 1,2,...,n satisfying |p(i+2)-p(i)| not equal to 2 for all 0<i<n-1.

Source: https://oeis.org/A110128
Credit: @Solfanbtc

Conjectural asymptotic expansion (Vaclav Kotesovec, Dec 05 2022, OEIS A110128, "based on the
recurrence by Manuel Kauers"; the entry notes that this recurrence is conjectural, guessed from
the 600-term b-file):
  a(n) ~ exp(-2) n! (1 + 4/n + 8/n^2 + 68/(3n^3) + 242/(3n^4) + 1692/(5n^5) + 72802/(45n^6)
         + 2725708/(315n^7) + 16083826/(315n^8) + 186091480/(567n^9) + 32213578294/(14175n^10) + ...).
The first terms are proved (Tauraso 2006: a(n)/n! ~ (1 + 4/n + ...)/e^2; quadratic term
Kotesovec 2011). The recurrence itself is not printed in the entry, so `main` states the expansion
with all eleven listed coefficients, in the usual sense of an asymptotic expansion:
  a(n)/n! - exp(-2) Σ_{k=0}^{10} c_k / n^k = O(1/n^11).

a(n) counts the permutations p of {0, ..., n-1} (shifted from 1..n) with |p(i+2) - p(i)| ≠ 2
whenever i + 2 < n. Checked: brute force gives 1, 1, 2, 4, 16, 44, 200, 1288, 9512 for n <= 8
(the listed terms), and with the listed terms up to n = 21 the remainder times n^11 stays bounded
(about 2.7 * 10^7 at n = 18 and n = 21).
-/

namespace OMA.S_oeis_a110128

open Filter Asymptotics

/-- Number of permutations of `Fin n` with `|p(i+2) - p(i)| ≠ 2` for all `i + 2 < n`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Equiv.Perm (Fin n) =>
    ∀ i j : Fin n, (j : ℕ) = i + 2 → ((p j : ℤ) - p i ≠ 2 ∧ (p i : ℤ) - p j ≠ 2)).card

/-- The listed coefficients c_0, ..., c_10 of the expansion. -/
def coeffs : List ℚ :=
  [1, 4, 8, 68 / 3, 242 / 3, 1692 / 5, 72802 / 45, 2725708 / 315, 16083826 / 315,
   186091480 / 567, 32213578294 / 14175]

theorem main :
    (fun n : ℕ => (a n : ℝ) / (Nat.factorial n : ℝ) -
        Real.exp (-2) * ∑ k ∈ Finset.range 11, ((coeffs.getD k 0 : ℚ) : ℝ) / (n : ℝ) ^ k)
      =O[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 11) := by
  sorry

end OMA.S_oeis_a110128

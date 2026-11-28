import Mathlib

/-!
# A066435: least k with sigma(n+k) = sigma(n) + sigma(k), or 0 if none (conjectured values).

Source: https://oeis.org/A066435
Credit: @Solfanbtc

The entry lists "Conjectured values for a(n) = least natural number k such that
sigma(n+k) = sigma(n)+sigma(k) if it exists; otherwise 0" ("It would be nice to remove the word
'Conjectured' from the description", N. J. A. Sloane). The conjectural part is that the zeros
(n = 3, 9, 15, 21, 27, 39, 57, 63 among the listed terms) really have no solution; the nonzero
values are verified minima. Stated: all 72 listed terms (n = 1..72) are correct.

Conventions.
* "Natural number k" means k ≥ 1 (with k = 0 the equation holds trivially since σ(0) = 0 in
  Mathlib, and the data show a(n) ≥ 1 whenever a solution exists).
* a(n) = v > 0 means v is the least k ≥ 1 with σ(n+k) = σ(n) + σ(k); a(n) = 0 means there is no
  such k. σ = `ArithmeticFunction.sigma 1`.
* python3: the least solutions k < 10^4 - n agree with all nonzero listed terms, and there is
  none for the n with listed value 0 (the entry reports searches up to k < 10^11).
-/

namespace OMA.S_oeis_a066435

open ArithmeticFunction

/-- The listed terms, a(n) = data.getD (n - 1) 0. -/
def data : List ℕ :=
  [2, 1, 0, 5, 4, 2, 14, 2, 0, 5, 22, 43, 26, 7, 0, 496, 34, 2, 38, 37, 0, 11, 46, 6, 50, 13, 0,
    4, 26, 10, 62, 929, 282, 17, 28, 252, 20, 19, 0, 101, 8, 14, 12, 19, 17, 23, 38, 307, 98, 25,
    54, 65, 106, 51, 14, 14, 0, 29, 118, 66, 56, 30, 0, 8128, 22, 22, 44, 85, 66, 35, 135, 18]

/-- k ≥ 1 satisfies the homomorphic condition for n. -/
def Good (n k : ℕ) : Prop := 1 ≤ k ∧ sigma 1 (n + k) = sigma 1 n + sigma 1 k

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 72 →
    (data.getD (n - 1) 0 = 0 → ∀ k : ℕ, ¬ Good n k) ∧
    (data.getD (n - 1) 0 ≠ 0 → IsLeast {k : ℕ | Good n k} (data.getD (n - 1) 0)) := by
  sorry

end OMA.S_oeis_a066435

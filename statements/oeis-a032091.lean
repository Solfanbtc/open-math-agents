import Mathlib

/-!
# A032091: Number of reversible strings with n-1 beads of 2 colors. 4 beads are black. String is not palindromic.

Source: https://oeis.org/A032091
Credit: @Solfanbtc

The formula for a(n) was Ralf Stephan's conjecture 73 (arXiv:math/0409509), solved by
E. Wilmer (Proposition 2 of her notes); the entry notes a minor typo in the original
conjecture, so the corrected formula as given in the entry is stated:
* (M. F. Hasler) 48 a(n) = (n-5)(n-3)(n-1)^2 + (6n-15)·[n even];
* (C. Barker) 48 a(n) = n^4 - 10n^3 + 32n^2 - 32n for n even, and
  48 a(n) = n^4 - 10n^3 + 32n^2 - 38n + 15 for n odd.
`main` states both, for all n ≥ 6 (the offset), over ℤ.

Conventions. A string is a word `Fin (n-1) → Bool` (true = black) with exactly 4 black
beads; it is palindromic if it equals its reverse. A reversible string is a class under
reversal; a(n) counts the classes {w, reverse w} of non-palindromic strings. Checked with
python3: this count reproduces the data 2, 6, 16, 32, 60, ... and both formulas hold for
6 ≤ n < 40.
-/

namespace OMA.S_oeis_a032091

/-- Non-palindromic strings of length `n-1` with exactly 4 black beads. -/
def nonPalindromic (n : ℕ) : Finset (Fin (n - 1) → Bool) :=
  Finset.univ.filter fun w =>
    (Finset.univ.filter fun i => w i = true).card = 4 ∧ w ∘ Fin.rev ≠ w

/-- a(n): the number of reversal classes {w, reverse w} of such strings. -/
def a (n : ℕ) : ℕ :=
  ((nonPalindromic n).image fun w => ({w, w ∘ Fin.rev} : Finset (Fin (n - 1) → Bool))).card

theorem main : ∀ n : ℕ, 6 ≤ n →
    48 * (a n : ℤ) = ((n : ℤ) - 5) * ((n : ℤ) - 3) * ((n : ℤ) - 1) ^ 2 +
        (if Even n then 6 * (n : ℤ) - 15 else 0) ∧
    (Even n → 48 * (a n : ℤ) = (n : ℤ) ^ 4 - 10 * (n : ℤ) ^ 3 + 32 * (n : ℤ) ^ 2 - 32 * n) ∧
    (Odd n → 48 * (a n : ℤ) =
      (n : ℤ) ^ 4 - 10 * (n : ℤ) ^ 3 + 32 * (n : ℤ) ^ 2 - 38 * n + 15) := by
  sorry

end OMA.S_oeis_a032091

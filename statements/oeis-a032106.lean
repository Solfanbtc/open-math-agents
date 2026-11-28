import Mathlib

/-!
# A032106: Number of reversible strings with n black beads and n-1 white beads. String is not palindromic.

Source: https://oeis.org/A032106
Credit: @Solfanbtc

The formula for a(n) was Ralf Stephan's conjecture 74 (arXiv:math/0409509), solved by
E. Wilmer (Proposition 3 of her notes). The entry gives it in the forms
* a(2n) = (C(4n, 2n) - C(2n, n)) / 4 for n ≥ 1 (Bower),
* a(2n+1) = (C(4n+1, 2n+1) - C(2n, n)) / 2 for n ≥ 1 (Hadjicostas),
* a(n) = (2 C(2n, n) - (3 - (-1)^n) C(2⌊n/2⌋, ⌊n/2⌋)) / 8 for n ≥ 2 (Hadjicostas),
and `main` states all three (cleared of denominators, in ℤ).

Conventions.
* A string is a word `Fin (2n-1) → Bool` (true = black) with exactly n black beads (so n-1
  white); it is palindromic if it equals its reverse. A reversible string is a class of
  strings under reversal; a(n) counts the classes of non-palindromic strings, i.e. the
  number of distinct sets {w, reverse w} with w non-palindromic.
* n = 1 is excluded, as in all three formulas: by this literal count a(1) = 0 (the single
  bead string is palindromic), while the entry lists a(1) = 1 by Bower's convention, which
  Wilmer rejects (see the entry). Checked with python3: the count reproduces the data
  1, 4, 16, 60, 226, ... for 2 ≤ n ≤ 12, and the three formulas hold there.
-/

namespace OMA.S_oeis_a032106

/-- Strings of length `2n-1` with exactly `n` black beads that are not palindromic. -/
def nonPalindromic (n : ℕ) : Finset (Fin (2 * n - 1) → Bool) :=
  Finset.univ.filter fun w =>
    (Finset.univ.filter fun i => w i = true).card = n ∧ w ∘ Fin.rev ≠ w

/-- a(n): the number of reversal classes {w, reverse w} of such strings. -/
def a (n : ℕ) : ℕ :=
  ((nonPalindromic n).image fun w => ({w, w ∘ Fin.rev} : Finset (Fin (2 * n - 1) → Bool))).card

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      4 * (a (2 * n) : ℤ) = ((4 * n).choose (2 * n) : ℤ) - ((2 * n).choose n : ℤ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      2 * (a (2 * n + 1) : ℤ) = ((4 * n + 1).choose (2 * n + 1) : ℤ) - ((2 * n).choose n : ℤ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      8 * (a n : ℤ) = 2 * ((2 * n).choose n : ℤ) -
        (3 - (-1) ^ n) * ((2 * (n / 2)).choose (n / 2) : ℤ)) := by
  sorry

end OMA.S_oeis_a032106

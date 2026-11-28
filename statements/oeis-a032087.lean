import Mathlib

/-!
# A032087: Number of reversible strings with n beads of 4 colors. If more than 1 bead, not palindromic.

Source: https://oeis.org/A032087
Credit: @Solfanbtc

Ralf Stephan's conjecture 72 (solved by Elizabeth Wilmer, Proposition 1): the formula
`a(2n+1) = 2^(4n+1) - 2^(2n+1)`, `a(2n) = 2^(4n-1) - 2^(2n) + 2^(2n-1)` (`n ≥ 1`), `a(1) = 4`.

Conventions. For `n ≥ 2`, `a(n)` is the number of non-palindromic strings `w : Fin n → Fin 4`
counted up to reversal, i.e. the number of distinct pairs `{w, reverse w}` with
`w ≠ reverse w`. The value `a(1) = 4` is Bower's convention that a 1-bead string is not
palindromic (Wilmer does not accept it); it is not part of `main`, which states the two
formulas for `n ≥ 1` (lengths `2n ≥ 2` and `2n+1 ≥ 3`). Checked with `#eval`: the definition
gives `6, 24, 120, 480, 2016` for lengths `2..6`, matching the data and the formulas.
-/

namespace OMA.S_oeis_a032087

/-- Reversal of a string of length `n`. -/
def rev {n : ℕ} (w : Fin n → Fin 4) : Fin n → Fin 4 := w ∘ Fin.rev

/-- Number of non-palindromic strings of length `n` over 4 colors, up to reversal. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ.filter fun w : Fin n → Fin 4 => rev w ≠ w).image
    fun w => ({w, rev w} : Finset (Fin n → Fin 4))).card

/-- Stephan's conjecture 72 (Wilmer's Proposition 1). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a (2 * n + 1) = 2 ^ (4 * n + 1) - 2 ^ (2 * n + 1) ∧
    a (2 * n) = 2 ^ (4 * n - 1) - 2 ^ (2 * n) + 2 ^ (2 * n - 1) := by
  sorry

end OMA.S_oeis_a032087

import Mathlib

/-!
# A087212: Number of ways in which n X n cells may be numbered using nonzero digits so that n n-digit squares are formed when read across or down the grids.

Source: https://oeis.org/A087212
Credit: @Solfanbtc

Conjecture (OEIS A087212): the sequence is complete, i.e. its 13 listed terms
3, 4, 10, 1, 16, 17, 13, 12, 11, 11, 9, 8, 2 (n = 1, ..., 13) are all its nonzero terms: there is
no such grid for n >= 14. `main` states the listed values and the vanishing for n >= 14.

Definition: an n X n grid of digits 1..9 (cell (i, j) holds `d i j + 1`) such that every row, read
left to right, and every column, read top to bottom, is an n-digit perfect square. (This is the
reading that reproduces the data: the four 2 X 2 grids of the example, and counts 3, 4, 10, 1 for
n = 1..4 by brute force.)
-/

namespace OMA.S_oeis_a087212

/-- The number formed by the digits `f 0, ..., f (n-1)` (most significant first), digit = `f j + 1`. -/
def readNum {n : ℕ} (f : Fin n → Fin 9) : ℕ := ∑ j : Fin n, ((f j : ℕ) + 1) * 10 ^ (n - 1 - j)

/-- All rows and columns of the grid are perfect squares. -/
def IsSquareGrid {n : ℕ} (d : Fin n → Fin n → Fin 9) : Prop :=
  (∀ i, IsSquare (readNum (d i))) ∧ ∀ j, IsSquare (readNum fun i => d i j)

open Classical in
/-- a(n): the number of such grids. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin n → Fin n → Fin 9 => IsSquareGrid d).card

/-- The listed terms a(1), ..., a(13). -/
def terms : List ℕ := [3, 4, 10, 1, 16, 17, 13, 12, 11, 11, 9, 8, 2]

theorem main : (∀ n : ℕ, 1 ≤ n → n ≤ 13 → a n = terms.getD (n - 1) 0) ∧
    ∀ n : ℕ, 14 ≤ n → a n = 0 := by
  sorry

end OMA.S_oeis_a087212

import Mathlib

/-!
# A139772: Number of linear trimer coverings of a 3n X 3n square.

Source: https://oeis.org/A139772
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of tilings of the `3n × 3n` square by straight trominoes
(`1 × 3` and `3 × 1` bars). Data: 2, 64, 37160, 378875648, 67433401509980,
209087783283413477232, 11281654633785546173131745084.

Conjecture (N. Bělohoubek, Apr 16 2026, OEIS A139772):
`a(n) ~ α · β^n · γ^(n^2)` with `0.933 < α < 0.979`, `0.4619 < β < 0.4696`,
`4.1691 < γ < 4.1739`. We state: there exist constants in these open intervals with
`a(n) ~ α β^n γ^(n^2)` as `n → ∞`.

Model. A placement is a lower-left cell `(i, j)` and an orientation (`false`: horizontal cells
`(i,j), (i+1,j), (i+2,j)`; `true`: vertical cells `(i,j), (i,j+1), (i,j+2)`). A tiling of the
`N × N` board is a set of placements inside the board covering every cell exactly once.
Checked: `#eval` of `a 1` gives 2; an independent python3 count with the same convention gives
2, 64, 37160, 378875648 for `n = 1..4`.
-/

namespace OMA.S_oeis_a139772

/-- The three cells of a straight tromino placement. -/
def cells (t : (ℕ × ℕ) × Bool) : Finset (ℕ × ℕ) :=
  if t.2 then {t.1, (t.1.1, t.1.2 + 1), (t.1.1, t.1.2 + 2)}
  else {t.1, (t.1.1 + 1, t.1.2), (t.1.1 + 2, t.1.2)}

/-- The `N × N` board. -/
def board (N : ℕ) : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N

/-- Straight tromino placements lying inside the `N × N` board. -/
def placements (N : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (board N ×ˢ (Finset.univ : Finset Bool)).filter (fun t => cells t ⊆ board N)

/-- The number of tilings of the `N × N` board by straight trominoes. -/
def tilings (N : ℕ) : ℕ :=
  ((placements N).powerset.filter (fun T =>
    ∀ c ∈ board N, (T.filter (fun t => c ∈ cells t)).card = 1)).card

/-- A139772(n): tilings of the `3n × 3n` square by straight trominoes. -/
def a (n : ℕ) : ℕ := tilings (3 * n)

/-- Bělohoubek's conjectured asymptotics for A139772. -/
theorem main : ∃ α β γ : ℝ, 0.933 < α ∧ α < 0.979 ∧ 0.4619 < β ∧ β < 0.4696 ∧
    4.1691 < γ ∧ γ < 4.1739 ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => α * β ^ n * γ ^ (n ^ 2)) := by
  sorry

end OMA.S_oeis_a139772

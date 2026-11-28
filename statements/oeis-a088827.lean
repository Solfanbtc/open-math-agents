import Mathlib

/-!
# A088827: Even numbers with odd abundance: even squares or two times squares.

Source: https://oeis.org/A088827
Credit: @Solfanbtc

`a(n)` (offset 1) is the `n`-th even number `k` whose abundance `σ(k) - 2k` is odd.

A191432 is the dispersion of `s(m) = ⌊m √2 + 1/√2⌋` (`m ≥ 1`): its row `r` (counting from 0)
is `t_r, s(t_r), s(s(t_r)), ...`, where `t_0 < t_1 < ...` are the positive integers not of the
form `s(m)` with `m ≥ 1`. Every positive integer occurs exactly once in this array.

Conjecture (John Tyler Rascoe, Jul 12 2022): if `n` sits in row `r` and column `c` of A191432
(first row and column numbered 0), then `a(n) = (2r + 1)^2 * 2^(c + 1)`. Since every
positive integer occurs in the array, this is stated as `a (D r c) = (2r+1)^2 * 2^(c+1)` for all
`r, c`, where `D r c` is the entry in row `r`, column `c`. Checked by computer for every
entry `D r c ≤ 539` with `r < 40`, `c < 12`.
-/

namespace OMA.S_oeis_a088827

/-- Even numbers with odd abundance `σ(k) - 2k`. -/
def IsTerm (k : ℕ) : Prop := Even k ∧ Odd ((ArithmeticFunction.sigma 1 k : ℤ) - 2 * k)

/-- `a n` is the `n`-th term of A088827 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- `s m = ⌊m √2 + 1/√2⌋`, the sequence whose dispersion is A191432. -/
noncomputable def s (m : ℕ) : ℕ := ⌊(m : ℝ) * Real.sqrt 2 + 1 / Real.sqrt 2⌋₊

/-- The positive integers not of the form `s m` with `m ≥ 1` (the first column of A191432). -/
def InComplement (t : ℕ) : Prop := 0 < t ∧ ∀ m : ℕ, 1 ≤ m → s m ≠ t

/-- The entry of A191432 in row `r` and column `c` (both counted from 0). -/
noncomputable def D (r c : ℕ) : ℕ := s^[c] (Nat.nth InComplement r)

/-- Rascoe's conjecture: the term of A088827 whose index sits in row `r`, column `c` of
A191432 is `(2r+1)^2 * 2^(c+1)`. -/
theorem main : ∀ r c : ℕ, a (D r c) = (2 * r + 1) ^ 2 * 2 ^ (c + 1) := by
  sorry

end OMA.S_oeis_a088827

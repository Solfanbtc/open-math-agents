import Mathlib

/-!
# A080795: Number of minimax trees on n nodes

Source: https://oeis.org/A080795
Credit: @Solfanbtc

A080795 (offset 0): `1, 1, 4, 20, 128, 1024, 9856, …`, defined here by the recurrence in the
entry, `a(0) = 1`, `a(n+1) = 2 ∑_{k=0}^{n} C(n, k) a(k) a(n-k) - 0^n` (equivalent to the e.g.f.
`A' = 2A^2 - 1`, `A(0) = 1`); it reproduces all 16 data terms.

A006154 (offset 0): number of labeled ordered partitions of an `n`-set into odd parts, e.g.f.
`1/(1 - sinh x)`; defined by the recurrence in its entry (Ralf Stephan):
`a(0) = a(1) = 1`, `a(n) = ∑_{k=1}^{⌈n/2⌉} C(n, 2k-1) a(n-2k+1)`, i.e. the sum over odd
`j = 2k - 1 ≤ n` of `C(n, j) a(n - j)`: `1, 1, 2, 7, 32, 181, …` (all 17 data terms agree).

Conjecture (Ralf Stephan, Apr 29 2004, OEIS formula): `a(2n) = 2^n · A006154(2n)` for `n > 0`.
(Python: holds for `1 ≤ n < 30`.)
-/

namespace OMA.S_oeis_a080795

/-- A080795 by its recurrence. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * (∑ k : Fin (n + 1), (Nat.choose n k : ℤ) * a k * a (n - k)) -
      (if n = 0 then 1 else 0)
decreasing_by all_goals (have := k.isLt; omega)

/-- A006154 by its recurrence: `A006154(n+1) = ∑_{odd J ≤ n+1} C(n+1, J) A006154(n+1-J)`
(with `J = j + 1`, `j` even). -/
def A006154 : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1),
      if (j : ℕ) % 2 = 0 then (Nat.choose (n + 1) (j + 1) : ℤ) * A006154 (n - j) else 0
decreasing_by omega

/-- Stephan's conjecture: `a(2n) = 2^n · A006154(2n)` for `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → a (2 * n) = 2 ^ n * A006154 (2 * n) := by
  sorry

end OMA.S_oeis_a080795

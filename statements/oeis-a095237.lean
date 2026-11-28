import Mathlib

/-!
# A095237: a(1)=1; then for n even, a(n)=(sum of previous terms times n) plus 1, for n odd, a(n)=(sum of previous terms times n) minus 1.

Source: https://oeis.org/A095237
Credit: @Solfanbtc

`S n = a(1) + ⋯ + a(n)` (with `S 0 = 0`, `S 1 = 1`). For `n ≥ 2`, `a(n) = n · S(n-1) + 1` if `n` is
even and `a(n) = n · S(n-1) - 1` if `n` is odd: 1, 3, 11, 61, 379, 2731, ... (`a(2) = 2·1 + 1`,
`a(3) = 3·4 - 1`, `a(4) = 4·15 + 1`). The truncated subtraction in `ℕ` is harmless, since
`S(n-1) ≥ 1`.

Conjecture (A. Murthy): there are infinitely many primes in this sequence. The sequence is
strictly increasing, so this means infinitely many indices `n` with `a(n)` prime. `main` states
this.
-/

namespace OMA.S_oeis_a095237

/-- One step: `a(n)` from `n` and `S(n-1)`. -/
def step (n s : ℕ) : ℕ := if Even n then n * s + 1 else n * s - 1

/-- Partial sums `S n = a(1) + ⋯ + a(n)`. -/
def S : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => S (n + 1) + step (n + 2) (S (n + 1))

/-- `a n` (offset 1). -/
def a (n : ℕ) : ℕ := if n ≤ 1 then 1 else step n (S (n - 1))

theorem main : {n : ℕ | 1 ≤ n ∧ (a n).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a095237

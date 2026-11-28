import Mathlib

/-!
# A137613: Omit the 1's from Rowland's sequence f(n) - f(n-1) = gcd(n,f(n-1)), where f(1) = 7.

Source: https://oeis.org/A137613
Credit: @Solfanbtc

Rowland's sequence: `f(1) = 7`, `f(n) = f(n-1) + gcd(n, f(n-1))` for `n ≥ 2`. A137613 (offset 1)
lists the differences `d(n) = f(n) - f(n-1)` (`n ≥ 2`) that are not 1, in order:
`5, 3, 11, 3, 23, 3, 47, 3, 5, 3, 101, ...`.

A168007 (the "jumping divisor sequence"): `b(1) = 1`; if `b(n)` is an even composite number then
`b(n+1) = b(n) - 1`, otherwise `b(n+1) = b(n) + lpf(b(n))` (`lpf = A020639`, `lpf(1) = 1`).
A168008 is its sequence of first differences: `A168008(n) = b(n+1) - b(n)`:
`1, 2, -1, 3, -1, 5, -1, 3, -1, 11, ...`.

Conjecture (Jon Maiga, May 20 2021, in the entry): `a(n) = A168008(2n + 4)` for all `n ≥ 1`.
(Rowland's own remark that all odd primes likely occur is already stated upstream as
`RowlandSequence.rowland_generates_all_odd_primes`, and is not repeated here.)

A python3 check: the definitions reproduce the data of A137613 and A168008, and the conjecture
holds for the first 150 terms.

Conventions:
* `rowland 0 = 0` is unused; `d n = rowland n - rowland (n - 1)` for `n ≥ 2`.
* `a k = d (Nat.nth (fun n => 2 ≤ n ∧ d n ≠ 1) (k - 1))` for `k ≥ 1` (infinitely many
  differences are not 1).
* `lpf` is `Nat.minFac` (`Nat.minFac 1 = 1`). "Even composite" is `Even x ∧ 1 < x ∧ ¬ x.Prime`.
* `jump 0 = 0` is unused.
-/

namespace OMA.S_oeis_a137613

/-- Rowland's sequence `f`, with `f(1) = 7`. -/
def rowland : ℕ → ℕ
  | 0 => 0
  | 1 => 7
  | n + 2 => rowland (n + 1) + Nat.gcd (n + 2) (rowland (n + 1))

/-- `d(n) = f(n) - f(n-1)`. -/
def d (n : ℕ) : ℕ := rowland n - rowland (n - 1)

/-- `a k = A137613(k)`: the `k`-th difference `d(n)` (`n ≥ 2`) that is not 1. -/
noncomputable def a (k : ℕ) : ℕ := d (Nat.nth (fun n => 2 ≤ n ∧ d n ≠ 1) (k - 1))

/-- A168007, the jumping divisor sequence, with `b(1) = 1`. -/
def jump : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let x := jump (n + 1)
      if Even x ∧ 1 < x ∧ ¬ x.Prime then x - 1 else x + Nat.minFac x

/-- A168008: first differences of A168007. -/
def c (n : ℕ) : ℤ := (jump (n + 1) : ℤ) - jump n

/-- Maiga's conjecture: `A137613(n) = A168008(2n + 4)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = c (2 * n + 4) := by
  sorry

end OMA.S_oeis_a137613

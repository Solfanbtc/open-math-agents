import Mathlib

/-!
# A077202: successive concatenations give new primes

Source: https://oeis.org/A077202
Credit: @Solfanbtc

`a(1) = 1`, and `a(n)` is the smallest (positive) number such that the decimal concatenation of the
two successive terms `a(n-1)`, `a(n)` is a prime which has not occurred earlier (as the
concatenation of an earlier pair of successive terms): `1, 1, 3, 1, 7, 1, 9, 7, 3, 7, 9, 11, …`
(a simulation with this definition reproduces all 80 data terms). Concatenation:
`x ‖ m = x · 10^(number of digits of m) + m`. Below `terms k = [a(1), …, a(k+1)]` and
`a 0 = 0` (offset 1).

Conjecture (OEIS comment): every odd prime occurs in this sequence infinitely many times.
-/

namespace OMA.S_oeis_a077202

/-- Decimal concatenation `x ‖ m`. -/
def concat (x m : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 m).length + m

/-- The primes `a(i) ‖ a(i+1)` formed by successive terms of the list `l`. -/
def pairs (l : List ℕ) : List ℕ := List.zipWith concat l l.tail

/-- The next term after the terms `l` (nonempty). -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (concat (l.getLastD 0) m).Prime ∧ concat (l.getLastD 0) m ∉ pairs l}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => terms k ++ [next (terms k)]

/-- A077202 (offset 1; `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else (terms (n - 1)).getD (n - 1) 0

/-- Every odd prime occurs infinitely often in A077202. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → {n : ℕ | 1 ≤ n ∧ a n = p}.Infinite := by
  sorry

end OMA.S_oeis_a077202

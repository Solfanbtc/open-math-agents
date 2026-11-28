import Mathlib

/-!
# A094340: a(n) = n-th partial sum of A094339 divided by A094339(n+1).

Source: https://oeis.org/A094340
Credit: @Solfanbtc

A094339 (offset 1): `b(1) = 2`, and `b(k+1)` is the least positive integer not among
`b(1), ..., b(k)` that divides `S(k) = b(1) + ⋯ + b(k)`: 2, 1, 3, 6, 4, 8, 12, 9, ...
(such a number exists: `S(k)` itself is unused, as it exceeds every earlier term once `k ≥ 2`,
and `b(2) = 1`). A094340 (offset 1) is `a(n) = S(n) / b(n+1)`, an integer by construction:
2, 1, 1, 3, 2, 2, 4, 9, ...

Conjecture (in the entry): every natural number occurs in A094340. All terms are positive, so
this means every positive integer occurs. (`#eval` of the definitions below reproduces the data.)
-/

namespace OMA.S_oeis_a094340

/-- The least positive divisor of `S` not in `l` (searching up to `S`; `0` if there is none). -/
def nextTerm (l : List ℕ) (S : ℕ) : ℕ :=
  ((List.range (S + 1)).filter (fun d => 0 < d && S % d == 0 && !l.contains d)).headD 0

/-- `init k = [b(1), ..., b(k+1)]` (A094339). -/
def init : ℕ → List ℕ
  | 0 => [2]
  | k + 1 => let l := init k; l ++ [nextTerm l l.sum]

/-- A094339(k), `k ≥ 1`. -/
def b (k : ℕ) : ℕ := (init k).getD (k - 1) 0

/-- A094340(n) = (b(1) + ⋯ + b(n)) / b(n+1). -/
def a (n : ℕ) : ℕ := (∑ i ∈ Finset.Icc 1 n, b i) / b (n + 1)

/-- Conjecture: every positive integer occurs in A094340. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a094340

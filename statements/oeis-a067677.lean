import Mathlib

/-!
# A067677: Diagonals of the prime-composite array, B(m,n) which are zeros from the Second Borve Conjecture.

Source: https://oeis.org/A067677
Credit: @Solfanbtc

Let `c(m)` be the `m`-th composite number (`c(1) = 4, c(2) = 6, ...`) and `p(n)` the `n`-th prime
(`m, n ≥ 1`). The prime-composite array is `B(m, n)` = the exponent of `p(n)` in `c(m)`. The
`m`-th diagonal consists of `B(m, 1), B(m+1, 2), B(m+2, 3), ...`, i.e. `B(m+k, k+1)`, `k ≥ 0`.
A067677 lists the `m` whose diagonal consists only of zeros: `8, 12, 26, 35, 38, ...`.

Second Borve Conjecture (in the entry): there are infinitely many zero-only diagonals.

`B(m+k, k+1) = 0` iff `p(k+1)` does not divide `c(m+k)`, so the diagonal `m` is zero-only iff
`p(k+1) ∤ c(m+k)` for every `k ≥ 0`.

A python3 check: computing each diagonal until `p(k+1) > c(m+k)` (from then on all entries are
`0`) reproduces all 47 listed terms, `m ≤ 820`.
-/

namespace OMA.S_oeis_a067677

/-- The `m`-th composite number, `m ≥ 1`. -/
noncomputable def c (m : ℕ) : ℕ := Nat.nth (fun x => 1 < x ∧ ¬ x.Prime) (m - 1)

/-- The `n`-th prime, `n ≥ 1`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `B(m, n)`: the exponent of `p(n)` in `c(m)`. -/
noncomputable def B (m n : ℕ) : ℕ := (c m).factorization (p n)

/-- The `m`-th diagonal `B(m, 1), B(m+1, 2), ...` consists of zeros only. -/
def ZeroDiagonal (m : ℕ) : Prop := ∀ k : ℕ, B (m + k) (k + 1) = 0

/-- The Second Borve Conjecture: infinitely many diagonals are zero-only. -/
theorem main : {m : ℕ | 1 ≤ m ∧ ZeroDiagonal m}.Infinite := by
  sorry

end OMA.S_oeis_a067677

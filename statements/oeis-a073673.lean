import Mathlib

/-!
# A073673: Rearrangement of natural numbers such that every partial product + 1 is a prime.

Source: https://oeis.org/A073673
Credit: @Solfanbtc

The sequence is greedy (Mathematica, PARI and Python programs of the entry): `a(1) = 1`, and
`a(n)` is the least positive integer `k` not among `a(1), …, a(n-1)` such that
`a(1) ⋯ a(n-1) · k + 1` is prime. Such a `k` always exists, by Dirichlet's theorem on primes
`≡ 1` modulo the partial product. `firstTerms n` is the list `[a(1), …, a(n)]`, and `a n` its
last entry (offset 1). Checked with python3: this definition reproduces the 70 listed terms
1, 2, 3, 5, 6, 9, 4, 7, 10, 17, ...

Conjecture (T. Ordowski, 2017): `n / log n ≪ a(n) ≪ n log n` (Vinogradov notation), i.e.
`n / log n = O(a(n))` and `a(n) = O(n log n)` as `n → ∞`.
-/

namespace OMA.S_oeis_a073673

open Filter Asymptotics Real

/-- The first `n` terms `[a(1), …, a(n)]` of the greedy sequence. -/
noncomputable def firstTerms : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := firstTerms n
    l ++ [sInf {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ (l.prod * k + 1).Prime}]

/-- `a n` is the `n`-th term of A073673 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (firstTerms n).getD (n - 1) 0

theorem main :
    ((fun n : ℕ => (n : ℝ) / log n) =O[atTop] fun n => (a n : ℝ)) ∧
      (fun n : ℕ => (a n : ℝ)) =O[atTop] fun n => (n : ℝ) * log n := by
  sorry

end OMA.S_oeis_a073673

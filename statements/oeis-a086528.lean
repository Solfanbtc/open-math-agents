import Mathlib

/-!
# A086528: Smallest prime which occurs exactly n times in the sequence A086527.

Source: https://oeis.org/A086528
Credit: @Solfanbtc

A055265 is the greedy sequence `b(1) = 1`, and `b(k)` is the smallest positive integer not
used earlier such that `b(k-1) + b(k)` is prime. (It is well defined: the terms alternate in
parity, and Dirichlet's theorem gives a next term. So the infimum below is the genuine
minimum.) `L k` is the list `[b(1), …, b(k)]`. A086527 is the sequence of the primes
`b(k) + b(k+1)`, `k ≥ 1`, and A086528(n) (`n ≥ 0`) is the smallest prime occurring exactly `n`
times in A086527. Here the number of occurrences of `p` is the (extended) cardinality of
`{k ≥ 1 | b(k) + b(k+1) = p}`, which is `⊤` if `p` occurs infinitely often.

Conjecture (entry): the sequence is infinite, i.e. for every `n ≥ 0` some prime occurs exactly
`n` times in A086527. Checked with python3 (A055265 up to 400000 terms, primes below 6000):
the definition reproduces the 17 listed terms `2, 3, 11, 53, 29, …, 5623`.
-/

namespace OMA.S_oeis_a086528

/-- `L k = [b(1), …, b(k)]` for A055265 (`L 0 = []`). -/
noncomputable def L : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | k + 2 =>
    let l := L (k + 1)
    l ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ l ∧ (l.getLastD 1 + m).Prime}]

/-- A055265(k) for `k ≥ 1`. -/
noncomputable def b (k : ℕ) : ℕ := (L k).getLastD 0

/-- The conjecture: for every `n`, some prime occurs exactly `n` times as `b(k) + b(k+1)`. -/
theorem main : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧
    {k : ℕ | 1 ≤ k ∧ b k + b (k + 1) = p}.encard = n := by
  sorry

end OMA.S_oeis_a086528

import Mathlib

/-!
# A079098: Conjectured values of greatest k such that for any consecutive primes q, q', k <= q < q', sqrt(q')-sqrt(q) < 1/n.

Source: https://oeis.org/A079098
Credit: @Solfanbtc

Reading of the name. Taken literally ("greatest k such that the inequality holds for all
consecutive primes `q ≥ k`") the set of such `k` is upward closed, so it has no greatest
element; and the data contradict that reading: for `n = 2`, `a(2) = 113` and the next prime is
`127`, with `√127 - √113 ≈ 0.639 > 1/2`. What the data list is the threshold after which the
inequality holds: for `n ≥ 2`, `a(n)` is the greatest prime `q` whose next prime `q'` has
`√q' - √q ≥ 1/n` (equality is impossible, as `√q` is irrational), so that
`√q' - √q < 1/n` for all consecutive primes `a(n) < q < q'`; for `n = 1` there is no such prime
(Andrica's conjecture) and the entry lists `a(1) = 1`. This reading reproduces all 32 terms of
%S, %T, %U (checked in Python over all primes below `6·10^7`).

The entry states the terms as conjectured values ("each of these terms, k, has been tested to at
least 100*k", Sean A. Irvine). The claim stated here: for each listed `n = 1, …, 32`,
* every pair of consecutive primes `q < q'` with `q > a(n)` has `√q' - √q < 1/n`
  (for `n = 1`, `a(1) = 1`, this is Andrica's conjecture for all primes), and
* for `n ≥ 2`, `a(n)` is a prime whose next prime `q'` has `√q' - √q ≥ 1/n`,
so that `a(n)` is exactly the term described above.
-/

namespace OMA.S_oeis_a079098

/-- The listed terms `a(1), …, a(32)`, as `a (⟨n - 1, _⟩)`. -/
def a : Fin 32 → ℕ :=
  ![1, 113, 1327, 2971, 31397, 34061, 43331, 44293, 58831, 155921, 370261, 370261,
    492113, 492113, 492113, 604073, 604073, 1357201, 1561919, 2010733, 2010733,
    2010733, 2010733, 2010733, 2010733, 2010733, 2010733, 2238823, 4652353, 4652353, 4652353,
    4652353]

theorem main : ∀ j : Fin 32,
    (∀ i : ℕ, a j < Nat.nth Nat.Prime i →
      Real.sqrt (Nat.nth Nat.Prime (i + 1)) - Real.sqrt (Nat.nth Nat.Prime i) < 1 / ((j : ℕ) + 1 : ℝ)) ∧
    (1 ≤ (j : ℕ) → ∃ i : ℕ, Nat.nth Nat.Prime i = a j ∧
      1 / ((j : ℕ) + 1 : ℝ) ≤ Real.sqrt (Nat.nth Nat.Prime (i + 1)) - Real.sqrt (Nat.nth Nat.Prime i)) := by
  sorry

end OMA.S_oeis_a079098

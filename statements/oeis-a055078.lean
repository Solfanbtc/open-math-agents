import Mathlib

/-!
# A055078: numbers needing at least 4 terms of the form (p^2-1)/24, p a prime > 4

Source: https://oeis.org/A055078 (R. K. Guy, Unsolved Problems in Number Theory, section C20)
Credit: @Solfanbtc

For a prime `p > 4` (i.e. `p ≥ 5`), `(p^2 - 1)/24` is an integer: 1, 2, 5, 7, 12, 15, 22, ...
A055078 lists the `n` that need at least 4 such terms: 33, 68, 88, 103, ...

Conjecture (Chowla): every number is the sum of no more than four terms of the form
`(p^2 - 1)/24` with `p` a prime `> 4`. Terms may repeat (the entry's terms 33, 68, ... need
exactly four, and e.g. `3 = 1 + 2`, `4 = 2 + 2`). "All numbers" is read as all positive integers
(`0` is the empty sum anyway). A representation is a list of at most four primes `p > 4`.

Sanity check (python): with repetitions allowed, the numbers `≤ 20000` needing at least four terms
start with all 52 listed terms, and every `n ≤ 20000` needs at most four.
-/

namespace OMA.S_oeis_a055078

/-- Chowla's conjecture: every positive integer is a sum of at most four numbers
`(p^2 - 1)/24` with `p` a prime `> 4`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ l : List ℕ, l.length ≤ 4 ∧ (∀ p ∈ l, p.Prime ∧ 4 < p) ∧
      n = (l.map (fun p => (p ^ 2 - 1) / 24)).sum := by
  sorry

end OMA.S_oeis_a055078

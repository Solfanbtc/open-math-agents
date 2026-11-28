import Mathlib

/-!
# A065069: Numbers n such that Fibonacci(n) is not squarefree, but for all proper divisors k of n, Fibonacci(k) is squarefree.

Source: https://oeis.org/A065069
Credit: @Solfanbtc

A term is an `n ≥ 1` with `F(n)` not squarefree and `F(k)` squarefree for every proper divisor
`k` of `n` (`n = 0` is excluded: `F(0) = 0` is not squarefree and `0` has no proper divisor
below it; the entry's PARI program also requires `n > 1`).

The entry (Charles R Greathouse IV, 2014, 2022): "Terms after a(12) are conjectures until the
factorizations of F(1271), F(1273), etc. are completed"; the listed data is computed under the
assumption that no Fibonacci number has a square primitive prime factor (T. D. Noe), i.e. that
the terms are the minimal elements under divisibility of `{p · Z(p)}` (`Z(p)` the index of the
first Fibonacci number divisible by `p`). `main` states that the listed data is correct: the
terms up to `21206` (the last listed term) are exactly the 41 listed numbers. Checked with
python3: under that assumption (and checking `p² ∤ F(Z(p))` for every prime `p ≤ 21206`) the
minimal elements of `{p · Z(p)} ∩ [1, 21206]` are exactly the listed terms.
-/

namespace OMA.S_oeis_a065069

/-- `n` is a term of A065069. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ ¬ Squarefree (Nat.fib n) ∧ ∀ k : ℕ, k ∣ n → k < n → Squarefree (Nat.fib k)

/-- The listed terms of A065069 are all its terms up to 21206. -/
theorem main : {n : ℕ | n ≤ 21206 ∧ IsTerm n} =
    {6, 25, 56, 91, 110, 153, 406, 703, 752, 820, 915, 979, 1431, 1892, 2147, 2701, 2943, 3029,
      3422, 4378, 4556, 4753, 4970, 5513, 6394, 7868, 8841, 9453, 10712, 12403, 13508, 13546,
      15051, 16256, 17030, 17267, 18023, 18721, 19503, 20827, 21206} := by
  sorry

end OMA.S_oeis_a065069

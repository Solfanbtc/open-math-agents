import Mathlib

/-!
# A090483: Indices of zero in A090482.

Source: https://oeis.org/A090483
Credit: @Solfanbtc

A090482(n) is the smallest prime `p` with `τ(p - 1) + τ(p + 1) = n` (`τ` = number of divisors),
or 0 if there is no such prime. A090483 lists the `n ≥ 1` with A090482(n) = 0, i.e. the
`n ≥ 1` that are not of the form `τ(p - 1) + τ(p + 1)` for any prime `p`: 1, 2, 4, 6, 9, 15, 19
(`p = 2` gives `τ(1) + τ(3) = 3`). The zeros at 9, 15 and 19 are proved in A090482.

Conjecture (D. Wasserman, 2005; checked up to 200): there are no more terms. `main` states
that the set of such `n ≥ 1` is exactly `{1, 2, 4, 6, 9, 15, 19}`.
-/

namespace OMA.S_oeis_a090483

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p : ℕ, p.Prime ∧ (p - 1).divisors.card + (p + 1).divisors.card = n} =
      {1, 2, 4, 6, 9, 15, 19} := by
  sorry

end OMA.S_oeis_a090483

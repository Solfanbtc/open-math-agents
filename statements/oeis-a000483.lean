import Mathlib

/-!
# A000483: Associated Stirling numbers: second-order reciprocal Stirling numbers (Fekete) a(n) = [[n, 3]]. The number of 3-orbit permutations

Source: https://oeis.org/A000483
Credit: @Solfanbtc

The entry (offset 6, data 15, 210, 2380, 26432, ...) carries two conjectured recurrences
(R. J. Mathar, Jul 18 2015):

1. `(n-2)(n-4) a(n) - (n-1)(3n^2-21n+35) a(n-1) + (n-1)(n-2)(3n^2-24n+47) a(n-2)
     - (n-5)(n-1)(n-2)(n-3)(n-4) a(n-3) = 0`;
2. `3(-n+4) a(n) + (9n^2-59n+90) a(n-1) + (-9n^3+96n^2-348n+436) a(n-2)
     + (n-3)(3n^3-45n^2+237n-430) a(n-3) + 5(n-5)(n-6)(n-3)(n-4) a(n-4) = 0`.

Both are stated together below, as a conjunction.

Conventions:
* `a n` is the number of permutations of an `n`-set with exactly 3 cycles (orbits), each of
  length at least 2, as in the entry's name. In Mathlib terms: permutations of `Fin n` with no
  fixed point whose `cycleType` (the multiset of lengths of the nontrivial cycles) has 3
  elements. This gives `a n = 0` for `n < 6` and 15, 210, 2380 for `n = 6, 7, 8`, matching the
  e.g.f. `-(x + log(1-x))^3/6` of the entry.
* The coefficients are evaluated in `ℤ` (true subtraction).
* Ranges: the source gives none. With `a n = 0` for `n < 6` (the value of the definition),
  recurrence 1 holds for every `n` from 7 to 60 (checked) but fails at `n = 6`
  (`8 * 15 ≠ 0`), and recurrence 2 holds for every `n` from 8 to 60 but fails at `n = 6, 7`.
  So they are stated for `n ≥ 7` and `n ≥ 8` respectively, the largest ranges on which they
  can hold. These include every `n` at which all the terms involved lie in the entry's range
  (`n ≥ 9`, resp. `n ≥ 10`).
-/

namespace OMA.S_oeis_a000483

/-- A000483: the number of permutations of an `n`-set with exactly 3 cycles, each of length
at least 2. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (∀ i, σ i ≠ i) ∧ σ.cycleType.card = 3)).card

/-- Mathar's two conjectured recurrences for A000483, for `n ≥ 7` and `n ≥ 8` respectively. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n →
      ((n : ℤ) - 2) * ((n : ℤ) - 4) * (a n : ℤ)
        - ((n : ℤ) - 1) * (3 * (n : ℤ) ^ 2 - 21 * n + 35) * (a (n - 1) : ℤ)
        + ((n : ℤ) - 1) * ((n : ℤ) - 2) * (3 * (n : ℤ) ^ 2 - 24 * n + 47) * (a (n - 2) : ℤ)
        - ((n : ℤ) - 5) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * ((n : ℤ) - 4)
            * (a (n - 3) : ℤ) = 0) ∧
    (∀ n : ℕ, 8 ≤ n →
      3 * (-(n : ℤ) + 4) * (a n : ℤ)
        + (9 * (n : ℤ) ^ 2 - 59 * n + 90) * (a (n - 1) : ℤ)
        + (-9 * (n : ℤ) ^ 3 + 96 * (n : ℤ) ^ 2 - 348 * n + 436) * (a (n - 2) : ℤ)
        + ((n : ℤ) - 3) * (3 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 237 * n - 430) * (a (n - 3) : ℤ)
        + 5 * ((n : ℤ) - 5) * ((n : ℤ) - 6) * ((n : ℤ) - 3) * ((n : ℤ) - 4)
            * (a (n - 4) : ℤ) = 0) := by
  sorry

end OMA.S_oeis_a000483

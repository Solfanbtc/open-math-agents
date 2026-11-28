import Mathlib

/-!
# A060432: Partial sums of A002024.

Source: https://oeis.org/A060432
Credit: @Solfanbtc

`A002024(k)` is `m` repeated `m` times (`1, 2, 2, 3, 3, 3, ...`): the least `m` with
`k ≤ m(m+1)/2`. `a(n) = ∑_{k=1}^{n} A002024(k)` for `n ≥ 1`: `1, 3, 5, 8, 11, 14, 18, ...`.

Conjecture (Aditya A Gupta and Sean A. Irvine, Apr 26 2026, in the entry; "known to be true for
`n ≤ 16`"): `a(n)` is the minimum diameter of an `(n+1)`-element set of integers for which no
nonzero `d` has more than `d` representations as a difference of elements of the set.

Minimal fix, explained: read literally for `d < 0` ("at most `d < 0` representations") the
condition fails for every set with two or more elements (each positive difference `x - y` gives
the negative difference `y - x`). The intended condition is for `d > 0`: the number of pairs
`(x, y)` of elements with `x - y = d` is at most `d` (equivalently, at most `|d|` for every
nonzero `d`, since `d` and `-d` have the same number of representations). Diameter = `max - min`.

A python3 check (brute force over all sets containing `0` and `D`): the minimum diameter equals
`a(n)` for `1 ≤ n ≤ 9`.
-/

namespace OMA.S_oeis_a060432

/-- `A002024(k)`: the least `m` with `k ≤ m (m+1)/2`. -/
noncomputable def A002024 (k : ℕ) : ℕ := sInf {m : ℕ | k ≤ m * (m + 1) / 2}

/-- `a(n) = ∑_{k=1}^{n} A002024(k)`. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A002024 k

/-- Every positive `d` has at most `d` representations `d = x - y` with `x, y ∈ S`. -/
def FewDifferences (S : Finset ℤ) : Prop :=
  ∀ d : ℤ, 0 < d → (((S ×ˢ S).filter (fun p => p.1 - p.2 = d)).card : ℤ) ≤ d

/-- The set has diameter `D`. -/
def HasDiameter (S : Finset ℤ) (D : ℕ) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x - y ≤ D) ∧ ∃ x ∈ S, ∃ y ∈ S, x - y = D

/-- The conjecture: `a(n)` is the least diameter of an `(n+1)`-element set of integers in which
every `d > 0` has at most `d` representations as a difference. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    IsLeast {D : ℕ | ∃ S : Finset ℤ, S.card = n + 1 ∧ HasDiameter S D ∧ FewDifferences S}
      (a n) := by
  sorry

end OMA.S_oeis_a060432

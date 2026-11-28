import Mathlib

/-!
# A145878: permutations by number of strong fixed points: McGinnis' recurrence and closed forms

Source: https://oeis.org/A145878
Credit: @Solfanbtc

A145878: `T(n, k)` is the number of permutations of `[n]` having `k` strong fixed points
(`0 ≤ k ≤ n`). A strong fixed point of `π` is a position `i` with `π(j) < π(i)` for all `j < i`
and `π(j) > π(i)` for all `j > i` (it is then a fixed point).

The entry (D. A. McGinnis, Oct 15 2018): "T(n,k) = Sum_{i=1..n-k+1} T(n-i,k-1)*T(i-1,0).
T(3+k,k)=3k+3, T(4+k,k)=(k+1)(k+28)/2, T(5+k,k)=(k+1)(3k+77), T(6+k,k)=(k+1)(k^2+110k+2982)/6,
T(7+k,k)=(k+1)(3k^2+235k+7352)/2 (previous conjectures). See the link by Theresa Baren, et al."
So these were conjectures, now resolved in the cited work; `main` states all six for every
`k`, the recurrence for `1 ≤ k ≤ n` (the formulas with a denominator are multiplied out).
Checked with python3 by brute force over all permutations of size `≤ 9`.
-/

namespace OMA.S_oeis_a145878

/-- `i` is a strong fixed point of `σ`. -/
def IsStrongFixed {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (∀ j, j < i → σ j < σ i) ∧ (∀ j, i < j → σ i < σ j)

/-- `T(n, k)`: the number of permutations of `[n]` with exactly `k` strong fixed points. -/
noncomputable def T (n k : ℕ) : ℕ :=
  {σ : Equiv.Perm (Fin n) | {i : Fin n | IsStrongFixed σ i}.ncard = k}.ncard

/-- McGinnis' recurrence and the closed forms for `T(j + k, k)`, `3 ≤ j ≤ 7`. -/
theorem main :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n →
      T n k = ∑ i ∈ Finset.Icc 1 (n - k + 1), T (n - i) (k - 1) * T (i - 1) 0) ∧
    (∀ k : ℕ, T (3 + k) k = 3 * k + 3) ∧
    (∀ k : ℕ, 2 * T (4 + k) k = (k + 1) * (k + 28)) ∧
    (∀ k : ℕ, T (5 + k) k = (k + 1) * (3 * k + 77)) ∧
    (∀ k : ℕ, 6 * T (6 + k) k = (k + 1) * (k ^ 2 + 110 * k + 2982)) ∧
    (∀ k : ℕ, 2 * T (7 + k) k = (k + 1) * (3 * k ^ 2 + 235 * k + 7352)) := by
  sorry

end OMA.S_oeis_a145878

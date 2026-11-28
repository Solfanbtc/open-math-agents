import Mathlib

/-!
# A082885: Primes followed by a larger-than-average prime gap.

Source: https://oeis.org/A082885
Credit: @Solfanbtc

`A082885` lists the primes `p(j)` with `p(j+1) - p(j) > log p(j)` (natural logarithm), in
increasing order: `2, 3, 5, 7, 13, 19, 23, 31, ...` (offset 1).

Conjecture (Alain Rocchelli, Dec 18 2023, in the entry):
`lim_{N → ∞} (∑_{n=1}^{N} a(n)) / (∑_{n=1}^{N} prime(n)) = e`.

A python3 check: the definition reproduces the data, and for the 483411 terms below `2·10⁷` the
ratio is about `2.83` (slowly decreasing).

Conventions:
* 0-indexed: `a k = A082885(k + 1)` and `Nat.nth Nat.Prime k = prime(k + 1)`, so the ratio for `N`
  is `(∑_{k < N} a k) / (∑_{k < N} Nat.nth Nat.Prime k)`.
* The prime following `p` is `Nat.nth Nat.Prime (j + 1)` for `p = Nat.nth Nat.Prime j`.
-/

namespace OMA.S_oeis_a082885

open Filter Topology

/-- `p` is a prime followed by a prime gap larger than `log p`. -/
def IsTerm (p : ℕ) : Prop :=
  ∃ j : ℕ, p = Nat.nth Nat.Prime j ∧
    Real.log p < ((Nat.nth Nat.Prime (j + 1) : ℕ) : ℝ) - (p : ℝ)

/-- `a k = A082885(k + 1)`. -/
noncomputable def a (k : ℕ) : ℕ := Nat.nth IsTerm k

/-- Rocchelli's conjecture: the ratio of partial sums tends to `e`. -/
theorem main :
    Tendsto (fun N : ℕ => ((∑ k ∈ Finset.range N, a k : ℕ) : ℝ) /
        ((∑ k ∈ Finset.range N, Nat.nth Nat.Prime k : ℕ) : ℝ))
      atTop (𝓝 (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a082885

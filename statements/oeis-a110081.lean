import Mathlib

/-!
# A110081: Integers k such that the digit set D = (0, 1, -k) used in base 3 expansions of the form
Sum_{ -N < j < oo} d_j 3^{-j}, all d_j in D, can represent all real numbers.

Source: https://oeis.org/A110081
Credit: @Solfanbtc

Conjecture (entry comment, from correspondence of R. K. Guy and J. Lagarias, 2005): "The sequence
is known to be infinite and irregular and is conjectured to have density zero."

Formalization.
* An expansion `Σ_{-N < j < ∞} d_j 3^{-j}` is written with `m = j + N - 1 ∈ ℕ` as
  `Σ_{m ≥ 0} d_m 3^{N-1-m}`, for some `N : ℕ` and digits `d_m ∈ {0, 1, -k}`. The digits are bounded,
  so the series converges absolutely; `HasSum` expresses that its sum is `x`.
* `k` ranges over the integers, as in the name. No `k ≤ 0` qualifies (for `k = 0` the digits are
  `0, 1` and only nonnegative reals arise; for `k < 0` all digits are `≥ 0`), so the sequence is a
  set of positive integers, and "density" is the natural density of
  `{k ≥ 1 : k represents all reals}` in the positive integers: the proportion of such `k` in
  `[1, n]` tends to `0`. (For `k = 1` this is balanced ternary, the first term.)
* Only the conjecture (density zero) is stated; that the sequence is infinite is said to be known.
-/

namespace OMA.S_oeis_a110081

open Filter Topology

/-- Every real number has a base-`3` expansion `Σ_{-N < j < ∞} d_j 3^{-j}` with all digits
`d_j ∈ {0, 1, -k}`. -/
def RepresentsAllReals (k : ℤ) : Prop :=
  ∀ x : ℝ, ∃ N : ℕ, ∃ d : ℕ → ℤ, (∀ m, d m = 0 ∨ d m = 1 ∨ d m = -k) ∧
    HasSum (fun m : ℕ => (d m : ℝ) * (3 : ℝ) ^ ((N : ℤ) - 1 - m)) x

/-- The sequence A110081 has natural density zero. -/
theorem main :
    Tendsto (fun n : ℕ =>
        (Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ RepresentsAllReals k} : ℝ) / n)
      atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a110081

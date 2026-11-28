import Mathlib

/-!
# A016627: Decimal expansion of log(4).

Source: https://oeis.org/A016627
Credit: @Solfanbtc

The entry has the formula (Mats Granvik, 2011): `log(4) = Sum_{k >= 1} A191907(4, k)/k`
(conjecture), where A191907 is the square array `T(n, k) = -(n - 1)` if `n ∣ k`, else `1`. So
`T(4, k) = -3` if `4 ∣ k` and `1` otherwise, and the claim is
`log 4 = 1 + 1/2 + 1/3 - 3/4 + 1/5 + 1/6 + 1/7 - 3/8 + ⋯`.

The series converges only conditionally (its terms are not absolutely summable), so we state the
sum in the usual sense, as the limit of the partial sums `∑_{k=1}^{N} T(4, k) / k` as `N → ∞`
(Mathlib's `HasSum` would require unconditional convergence and is false here).

Status: although labelled a conjecture in A016627, this is a classical fact: the `N`-th partial
sum is `H_N - H_{⌊N/4⌋}` (`H` the harmonic numbers), which tends to `log 4` since
`H_N - log N` converges (Euler-Mascheroni); A191907 notes the general identity
`∑_{k ≥ 1} T(n, k) / k = log n` (after Jaume Oliver Lafont, A061347, A002162). We state the
formula as written.
Check (python3): the partial sums at `N = 10⁶` equal `1.3862928…` (`log 4 = 1.3862943…`).
-/

namespace OMA.S_oeis_a016627

/-- The array A191907: `T(n, k) = -(n - 1)` if `n ∣ k`, else `1`. -/
def T (n k : ℕ) : ℤ := if n ∣ k then -((n : ℤ) - 1) else 1

/-- `∑_{k ≥ 1} T(4, k) / k = log 4`, as the limit of the partial sums. -/
theorem main :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 4 k : ℝ) / k) Filter.atTop
      (nhds (Real.log 4)) := by
  sorry

end OMA.S_oeis_a016627

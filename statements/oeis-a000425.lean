import Mathlib

/-!
# A000425: Coefficients of ménage hit polynomials.

Source: https://oeis.org/A000425
Credit: @Solfanbtc

A000425 is a diagonal of A058087: `a(n) = T(n, n-1)`, the coefficient of `t^1` in the ménage hit
polynomial (Kaplansky and Riordan, as in A058087)
`U_n(t) = Sum_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`.
Since `[t^1] (t-1)^k = k * (-1)^(k-1)`, this gives the explicit sum `a` below. Evaluated with
`#eval`, it gives `2, 0, 0, 8, 30, 192, 1344, 10800, 97434, ...` for `n = 1, 2, ...` (the data of
A000425, offset 1).

A000271(n) (offset 0) is the number of permutations `p` of `{1, ..., n}` with `p(i) - i ∉ {0, 1}`
(comment by Andrew Howroyd); `numA000271` evaluates to `1, 0, 0, 1, 3, 16, 96, 675`.

The entry states two conjectures (R. J. Mathar, Nov 02 2015):

1. `(n-1)(n-3) a(n) - n(n-2)(n-3) a(n-1) - n(n-1)(n-3) a(n-2) - n(n-1) a(n-3) = 0`. It involves
   `a(n-3)` and the offset is 1, so it is stated for `n ≥ 4`.
2. `a(n) = 2n * A000271(n)`. Read with the current offset 0 of A000271, this is false (`n = 4`:
   `a(4) = 8` but `2 * 4 * A000271(4) = 24`), while `a(n) = 2n * A000271(n-1)` agrees with the data
   for every `1 ≤ n < 400` (checked with python3). The literal claim is off by one in the index of
   A000271 (it holds if A000271 is read with offset 1), and the minimal fix states `a(n) = 2n * A000271(n-1)` for all `n ≥ 1`.

`main` is the conjunction of the two conjectures.
-/

namespace OMA.S_oeis_a000425

/-- A000425(n): the coefficient of `t^1` in the ménage hit polynomial
`U_n(t) = Sum_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1) ^ (k + 1) * (k : ℚ) * ((2 * n : ℚ) / (2 * n - k)) * ((2 * n - k).choose k : ℚ) *
      ((n - k).factorial : ℚ)

/-- A000271(n): permutations `σ` of `{0, ..., n-1}` with `σ i ≠ i` and `σ i ≠ i + 1` for all `i`. -/
def numA000271 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, (σ i : ℕ) ≠ i ∧ (σ i : ℕ) ≠ i + 1).card

/-- Mathar's two conjectures for A000425 (the second with the index of A000271 shifted by one). -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      ((n : ℚ) - 1) * ((n : ℚ) - 3) * a n - (n : ℚ) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * a (n - 1)
        - (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 2)
        - (n : ℚ) * ((n : ℚ) - 1) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 * (n : ℚ) * (numA000271 (n - 1) : ℚ)) := by
  sorry

end OMA.S_oeis_a000425

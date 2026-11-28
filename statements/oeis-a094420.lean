import Mathlib

/-!
# A094420: Generalized ordered Bell numbers Bo(n,n).

Source: https://oeis.org/A094420
Credit: @Solfanbtc

Conjecture (Velin Yanev, Jul 27 2026, as stated in the entry):
  a(n) = polylog(-n, n/(n + 1))/(n + 1) for n > 0.

Definitions.
* `a n = ∑_{k=0}^{n} k! * n^k * S(n, k)` with `S` the Stirling numbers of the second kind
  (formula of Seiichi Manyama in the entry; it reproduces the data 1, 1, 10, 219, 8676, ...).
* For `|z| < 1` and a nonnegative integer `n`, `polylog(-n, z) = ∑_{k ≥ 1} k^n z^k`. Here
  `z = n/(n+1) ∈ (0,1)`, so the series converges; we state the identity as a `HasSum`
  (convergence of the series to `(n+1) * a(n)`), summing over `k : ℕ`; the `k = 0` term is
  `0^n = 0` since `n > 0`.
* The restriction `n > 0` is the source's: at `n = 0` the right side is `polylog(0, 0) = 0`,
  while `a(0) = 1`.

Note: this identity is the diagonal case `r = n` of the formula
`Bo(r, n) = 1/(r+1) * Sum_{k>=1} k^n * (r/(r+1))^k` (r > 0, n > 0) recorded in A094416
(the n-th moment of a geometric distribution); it is therefore expected to be true.
Checked numerically with python3 for n = 1..6.
-/

namespace OMA.S_oeis_a094420

/-- A094420(n) = Bo(n, n) = ∑_{k=0}^{n} k! n^k S₂(n, k). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k.factorial * n ^ k * Nat.stirlingSecond n k

theorem main :
    ∀ n : ℕ, 0 < n →
      HasSum (fun k : ℕ => (k : ℝ) ^ n * ((n : ℝ) / (n + 1)) ^ k) (((n : ℝ) + 1) * (a n : ℝ)) := by
  sorry

end OMA.S_oeis_a094420

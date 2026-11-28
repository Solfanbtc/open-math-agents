import Mathlib

/-!
# A055615: a(n) = n * mu(n), where mu is the Möbius function A008683.

Source: https://oeis.org/A055615
Credit: @Solfanbtc

Conjectures (Gerald McGarvey, Sep 26 2004):
`lim_{b → 1+} Sum_{n=1..∞} a(n) * b^(-n) = -12` and `lim_{b → 1-} Sum_{n=1..∞} a(n) * b^n = -12`
(`1 / zeta(-1) = -12`: the series `Sum mu(n) * n` would be Abel summable to `1 / zeta(-1)`).

`main` is the conjunction of the two limits, `b → 1` from above and from below
(`nhdsWithin 1 (Set.Ioi 1)` and `nhdsWithin 1 (Set.Iio 1)`). For `0 < b < 1` and for `b > 1`
the respective series converge absolutely (`|a(n)| ≤ n`), so the sums are genuine sums. The
`n = 0` term of `∑'` is `0` since `μ 0 = 0` in Mathlib. Numerically, with `x = 0.99, 0.999,
0.9999` the second sum is about `-10.69, -11.80, -11.98`.
-/

namespace OMA.S_oeis_a055615

/-- A055615(n) = n * mu(n). -/
def a (n : ℕ) : ℤ := n * ArithmeticFunction.moebius n

/-- McGarvey's conjectures: both Abel-type limits of `Sum a(n) b^(∓n)` equal `-12`. -/
theorem main :
    Filter.Tendsto (fun b : ℝ => ∑' n : ℕ, (a n : ℝ) * b ^ (-(n : ℤ)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (-12)) ∧
    Filter.Tendsto (fun b : ℝ => ∑' n : ℕ, (a n : ℝ) * b ^ n)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (-12)) := by
  sorry

end OMA.S_oeis_a055615

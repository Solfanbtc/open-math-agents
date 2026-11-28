import Mathlib

/-!
# A003881: Decimal expansion of Pi/4.

Source: https://oeis.org/A003881
Credit: @Solfanbtc

The entry has the formula (Mats Granvik, 2011): `π/4 = lim_{n→∞} n · A001586(n-1) / A001586(n)`
(conjecture), where A001586 are the Springer numbers (generalized Euler numbers), defined by the
exponential generating function `1 / (cos x - sin x)`:
`A001586(n) = n! [xⁿ] 1/(cos x - sin x) = (dⁿ/dxⁿ) (1/(cos x - sin x)) at x = 0`
(`1, 1, 3, 11, 57, 361, 2763, ...`).

We state the limit exactly. Note: A001586 also records the asymptotic (Vaclav Kotesovec, 2013)
`A001586(n) ~ 4 n^(n+1/2) (4/π)^n / (√π eⁿ)`, which implies this limit, and the e.g.f. has its
nearest singularity, a simple pole, at `x = π/4`, so the statement is expected to be provable;
the formula is still labelled a conjecture in A003881.

`iteratedDeriv n f 0` only depends on `f` near `0`, where `cos x - sin x ≠ 0`, so Lean's junk
value of the division away from there does not matter. With the 22 listed terms (python3),
`n · a(n-1)/a(n)` is `0.785380` at `n = 10` and `0.785398` at `n = 21` (`π/4 = 0.7853981…`).
-/

namespace OMA.S_oeis_a003881

/-- The exponential generating function `1 / (cos x - sin x)` of the Springer numbers. -/
noncomputable def egf (x : ℝ) : ℝ := 1 / (Real.cos x - Real.sin x)

/-- The Springer numbers `A001586(n)`, as the `n`-th derivative of the e.g.f. at `0`. -/
noncomputable def springer (n : ℕ) : ℝ := iteratedDeriv n egf 0

/-- `n · A001586(n-1) / A001586(n) → π/4`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * springer (n - 1) / springer n) Filter.atTop
      (nhds (Real.pi / 4)) := by
  sorry

end OMA.S_oeis_a003881

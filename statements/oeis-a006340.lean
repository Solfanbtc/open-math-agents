import Mathlib

/-!
# A006340: An "eta-sequence": [ (n+1)*tau + 1/2 ] - [ n*tau + 1/2 ], tau = (1 + sqrt(5))/2.

Source: https://oeis.org/A006340
Credit: @Solfanbtc

Conjecture (listed in the entry): A006340 is the continued fraction expansion of
2.729967741... = sup{f(n,1)}, where f(1,x) = x + 1 and thereafter f(n,x) = x + 1 if n is in the
lower Wythoff sequence (A000201), else f(n,x) = 1/x.

Reading of the source: `f(n, ·)` is applied to the previous value, i.e. `f(1,1) = 2` and the
n-th value is obtained from the (n-1)-th one by `x ↦ x + 1` when `n ∈ A000201` and `x ↦ 1/x`
otherwise. This reproduces the first values listed in A245216:
2, 1/2, 3/2, 5/2, 2/5, 7/5, 5/7, 12/7, 19/7, 7/19, 26/19, 45/19, ...
Since `1 = ⌊φ⌋` lies in A000201, the rule for `n = 1` is the same as for later `n`, so the values
are `val n` (n ≥ 1) with `val 0 = 1`. The supremum is over `n ≥ 1`.

A006340 is taken with offset 0: `b k = ⌊(k+1)τ + 1/2⌋ - ⌊kτ + 1/2⌋`, so b = 2, 1, 2, 1, 2, 2, ...
"Continued fraction expansion" means the simple continued fraction `[b 0; b 1, b 2, ...]`:
the head term of `GenContFract.of x` is `b 0` and its k-th partial denominator is `b (k+1)`,
for every k (in particular the expansion does not terminate).
Numerically (exact rational arithmetic, n < 400) the largest value is 2.7299677415998...,
whose first 25 partial quotients agree with b.
-/

namespace OMA.S_oeis_a006340

open Real

/-- The lower Wythoff sequence A000201: `⌊k φ⌋` for `k ≥ 1`. -/
def lowerWythoff : Set ℕ := {n | ∃ k : ℕ, 1 ≤ k ∧ (n : ℤ) = ⌊(k : ℝ) * goldenRatio⌋}

open Classical in
/-- `val n = f(n, ...)` iterated from `1`: `val 0 = 1`, and `val (n+1)` is `val n + 1` if
`n + 1` is in the lower Wythoff sequence, else `1 / val n`. -/
noncomputable def val : ℕ → ℝ
  | 0 => 1
  | n + 1 => if n + 1 ∈ lowerWythoff then val n + 1 else 1 / val n

/-- A006340 (offset 0): `⌊(k+1)τ + 1/2⌋ - ⌊kτ + 1/2⌋`, `τ` the golden ratio. -/
noncomputable def b (k : ℕ) : ℤ :=
  ⌊((k : ℝ) + 1) * goldenRatio + 1 / 2⌋ - ⌊(k : ℝ) * goldenRatio + 1 / 2⌋

/-- The supremum `sup {f(n,1) : n ≥ 1}`. -/
noncomputable def supVal : ℝ := sSup {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = val n}

/-- Conjecture: the simple continued fraction expansion of `sup {f(n,1)}` is A006340. -/
theorem main : (GenContFract.of supVal).h = (b 0 : ℝ) ∧
    ∀ k : ℕ, (GenContFract.of supVal).partDens.get? k = some ((b (k + 1) : ℝ)) := by
  sorry

end OMA.S_oeis_a006340

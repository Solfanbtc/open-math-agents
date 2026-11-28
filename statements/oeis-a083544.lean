import Mathlib

/-!
# A083544: a(n) = maximal value of the sum of Mobius function values over a block of n consecutive natural numbers.

Source: https://oeis.org/A083544
Credit: @Solfanbtc

Hugh Montgomery's comment in the entry: let `Q(M, k)` be the number of integers `n` with
`M + 1 ≤ n ≤ M + k` that are not divisible by the square of any prime `p ≤ √k`, and
`Q⁺(k) = max_M Q(M, k)`. Montgomery expects that the sum of `μ(n)` over `n = M+1..M+k` can be
as large as `Q⁺(k)` and as small as `-Q⁺(k)` (and that this could be shown to follow from
the prime k-tuple conjecture). Since only the `n` counted by `Q(M, k)` can have `μ(n) ≠ 0`,
`|Σ μ(n)| ≤ Q⁺(k)` always, so the expectation says that `a(k) = Q⁺(k)` and that the minimal
block sum is `-Q⁺(k)`. We checked by computer that `Q⁺(k)` equals every listed term
`a(1..76)` of %S, %T, %U. (See also W. van Doorn and T. Tao, arXiv:2512.01087, Sect. 1.5.)

`M` ranges over natural numbers `M ≥ 0` (blocks of natural numbers `M+1, ..., M+k`), and
`p ≤ √k` is written `p * p ≤ k`. The statement is for every block length `k ≥ 1`.
-/

namespace OMA.S_oeis_a083544

/-- `Q(M, k)`: the `n ∈ [M+1, M+k]` divisible by no `p^2` with `p` prime, `p ≤ √k`. -/
def Q (M k : ℕ) : ℕ :=
  ((Finset.Icc (M + 1) (M + k)).filter fun n =>
    ∀ p ∈ Finset.range (k + 1), p.Prime → p * p ≤ k → ¬ p ^ 2 ∣ n).card

/-- `Q⁺(k) = max_M Q(M, k)` (the values are at most `k`, so the supremum is attained). -/
noncomputable def Qplus (k : ℕ) : ℕ := sSup (Set.range fun M => Q M k)

/-- The sum of the Möbius function over the block `M+1, ..., M+k`. -/
def blockSum (M k : ℕ) : ℤ := ∑ n ∈ Finset.Icc (M + 1) (M + k), ArithmeticFunction.moebius n

/-- Montgomery's expectation: block sums reach `Q⁺(k)` and `-Q⁺(k)`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (∃ M : ℕ, blockSum M k = Qplus k) ∧ (∃ M : ℕ, blockSum M k = -(Qplus k : ℤ)) := by
  sorry

end OMA.S_oeis_a083544

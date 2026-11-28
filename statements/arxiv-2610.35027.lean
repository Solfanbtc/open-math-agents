import Mathlib

/-!
# On almost perfect additive complements

Source: https://arxiv.org/abs/2610.35027
Credit: @Solfanbtc

The abstract: let `A, B` be infinite sets of non-negative integers with `n ∈ A + B` for all
sufficiently large integers `n`. The authors prove that if `A(x)B(x) - x` does not tend to
infinity, then `limsup_{x → ∞} A(x)B(x)/x ∈ [3/2, 2]`, and they conjecture that the interval
`(3/2, 8/5)` is also excluded for such *almost perfect* additive complements, i.e. that this
limsup never lies in the open interval `(3/2, 8/5)`.

Conventions:
* `A(x) = #{a ∈ A : a ≤ x}` (the sets are sets of non-negative integers, as in the source, so
  `0` may belong to them and is counted), `x` ranges over the natural numbers.
* The limsup is taken in `EReal` so that it is meaningful without assuming boundedness
  (the proved theorem shows it is in fact in `[3/2, 2]`). This follows the convention of
  `Erdos785` in formal-conjectures (which states Chen's `3/2` conjecture, now proved by
  the source, but not this `8/5` conjecture).
-/

namespace OMA.S_arxiv_2610_35027

open Filter Pointwise

/-- The counting function `A(x) = #{a ∈ A : a ≤ x}`. -/
noncomputable def counting (A : Set ℕ) (x : ℕ) : ℕ :=
  (A ∩ Set.Iic x).ncard

/-- Conjecture: if `A, B ⊆ ℕ` are infinite, `A + B` contains every sufficiently large integer and
`A(x)B(x) - x` does not tend to infinity, then `limsup A(x)B(x)/x ∉ (3/2, 8/5)`. -/
theorem main :
    ∀ A B : Set ℕ, A.Infinite → B.Infinite → (∀ᶠ n : ℕ in atTop, n ∈ A + B) →
      ¬ Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop →
      limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
        ∉ Set.Ioo ((3 / 2 : ℝ) : EReal) ((8 / 5 : ℝ) : EReal) := by
  sorry

end OMA.S_arxiv_2610_35027

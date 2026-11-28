import Mathlib

/-!
# A214948: a(n) is the sum over all proper integer partitions of n of the previous terms.

Source: https://oeis.org/A214948
Credit: @Solfanbtc

Definition: `a(1) = 1` and, for `n ≥ 2`, `a(n) = Σ_{p} Σ_{i ∈ p} a(i)`, where `p` runs over the
integer partitions of `n` other than `{n}` ("proper" partitions) and `i` over the parts of `p`
with multiplicity. E.g. `a(4) = (a(3)+a(1)) + (a(2)+a(2)) + (a(2)+a(1)+a(1)) + 4·a(1) = 19`.

Conjecture (Bill McEachen, Dec 26 2023): "a(n) ~ exp(k) * a(n-1), k = 0.992632731...".

Formalization.
* `IsA214948 a` is the defining recursion; it determines `a(n)` for every `n ≥ 1` (all parts of a
  proper partition of `n` are `< n`), so the conjecture is stated for every `a` satisfying it.
* `a(n) ~ exp(k) a(n-1)` means `a(n)/a(n-1) → exp(k)`. The constant is given by its first nine
  decimals; "k = 0.992632731..." is read as `0.992632731 ≤ k < 0.992632732`. (V. Kotesovec's
  asymptotic `a(n) ~ c·d^n` with `d = 2.6983291064742...` (A246828) gives
  `log d = 0.99263273198...`, and python gives `log(a(60)/a(59)) = 0.99263273199...`, both
  consistent with this reading.)
-/

namespace OMA.S_oeis_a214948

open Filter Topology

/-- The defining recursion of A214948. -/
def IsA214948 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
  ∀ n : ℕ, 2 ≤ n →
    a n = ∑ p ∈ (Finset.univ : Finset n.Partition).filter (fun p => p.parts ≠ {n}),
      (p.parts.map a).sum

/-- McEachen's conjecture: `a(n)/a(n-1) → exp(k)` with `k = 0.992632731...`. -/
theorem main : ∀ a : ℕ → ℕ, IsA214948 a →
    ∃ k : ℝ, 0.992632731 ≤ k ∧ k < 0.992632732 ∧
      Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 (Real.exp k)) := by
  sorry

end OMA.S_oeis_a214948

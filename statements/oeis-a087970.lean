import Mathlib

/-!
# A087970: Maximal term in Collatz-iteration started at 2^n+1.

Source: https://oeis.org/A087970
Credit: @Solfanbtc

The Collatz map is `x ↦ x/2` for even `x`, `x ↦ 3x + 1` for odd `x`, iterated until 1 (1 is
taken as a fixed point, as in A025586: `a(0) = 2` for the trajectory 2, 1). `a(n)` (offset 0)
is the largest term of the trajectory of `2^n + 1`: 2, 16, 16, 52, 52, 100, 196, 9232, ...

Conjecture (Chai Wah Wu, 2025): `a(n) = 3 a(n-1) - 2 a(n-2)` for `n > 13`. (The accompanying
g.f. is the same claim together with the initial terms.) `main` states the recurrence for all
`n > 13`, whenever the three trajectories involved have a largest term. Checked with python3:
the recurrence holds for `14 ≤ n < 400` and fails at `n = 13`; the terms there are
`a(n) = 3 · 2^n + 4`.
-/

namespace OMA.S_oeis_a087970

/-- The Collatz map with 1 as a fixed point. -/
def T (x : ℕ) : ℕ := if x = 1 then 1 else if x % 2 = 0 then x / 2 else 3 * x + 1

/-- `M` is the largest term of the trajectory of `x`. -/
def IsPeak (x M : ℕ) : Prop := IsGreatest {y | ∃ k : ℕ, y = T^[k] x} M

theorem main :
    ∀ n M M₁ M₂ : ℕ, 13 < n →
      IsPeak (2 ^ n + 1) M → IsPeak (2 ^ (n - 1) + 1) M₁ → IsPeak (2 ^ (n - 2) + 1) M₂ →
        (M : ℤ) = 3 * M₁ - 2 * M₂ := by
  sorry

end OMA.S_oeis_a087970

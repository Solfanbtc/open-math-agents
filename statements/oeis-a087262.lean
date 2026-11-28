import Mathlib

/-!
# A087262: Integer quotient of largest and initial values in 3x+1 iteration, started at n.

Source: https://oeis.org/A087262
Credit: @Solfanbtc

The 3x+1 map is iterated as in the Mathematica program: `x ↦ x/2` for even `x`, `x ↦ 3x + 1`
for odd `x`, except that 1 is a fixed point (the trajectory stops at 1). The peak of `n` is the
largest value of its trajectory (A025586), and `a(n) = ⌊peak / n⌋`. For example, `n = 3` has peak
16 and `a(3) = 5`. `a(n) = 1` exactly when the peak is the start value (A166245).

Conjecture (in the entry): if peak / initial value is an integer, then it equals 1. `main`
states: for every `n ≥ 1` and every `M` that is the largest value of the trajectory of `n`, if
`n ∣ M` then `M = n`. It is stated for trajectories that have a largest value, so it makes no
claim about (hypothetical) divergent trajectories. (python3: no counterexample for
`n ≤ 3·10^6`.)
-/

namespace OMA.S_oeis_a087262

/-- The 3x+1 map with 1 as a fixed point. -/
def T (x : ℕ) : ℕ := if x = 1 then 1 else if x % 2 = 0 then x / 2 else 3 * x + 1

theorem main :
    ∀ n M : ℕ, 1 ≤ n → IsGreatest {y | ∃ k : ℕ, y = T^[k] n} M → n ∣ M → M = n := by
  sorry

end OMA.S_oeis_a087262

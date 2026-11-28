import Mathlib

/-!
# A077085: Initial values such that if A077080(x)=phi(sigma(x)+phi(x)) is started at these numbers then the sequence does not converge.

Source: https://oeis.org/A077085
Credit: @Solfanbtc

Let `f(x) = φ(σ(x) + φ(x))` (A077080). The iteration started at `x` "converges" when it
reaches a fixed point of `f` (A077081 lists the fixed point reached, A077083 the number of
steps). A077085 lists the initial values for which it does not converge; the entry says
"these terms are only conjectures" (they survive 1000 iterations, S. A. Irvine).

`main` states the claim of the entry with its full data: among `1 ≤ x ≤ 1136` (the range
covered by %S, %T, %U), the iteration does not converge exactly for the 41 listed values.
We checked by computer that every other `x ≤ 1136` reaches a fixed point (within 47 steps),
while the 41 listed values have not reached one after 200 steps.
-/

namespace OMA.S_oeis_a077085

/-- `f(x) = φ(σ(x) + φ(x))`. -/
def f (x : ℕ) : ℕ := Nat.totient (ArithmeticFunction.sigma 1 x + Nat.totient x)

/-- The iteration from `x` reaches a fixed point of `f`. -/
def Converges (x : ℕ) : Prop := ∃ n : ℕ, f (f^[n] x) = f^[n] x

/-- The terms of A077085 listed in %S, %T, %U. -/
def listed : Finset ℕ :=
  {534, 556, 557, 580, 624, 702, 710, 738, 739, 740, 748, 784, 789, 822, 823, 841, 852,
    853, 900, 912, 913, 916, 924, 931, 938, 960, 961, 962, 1020, 1021, 1029, 1032, 1033,
    1034, 1065, 1089, 1092, 1093, 1098, 1126, 1136}

/-- The listed values are exactly the initial values up to 1136 whose iteration does not
converge. -/
theorem main : ∀ x : ℕ, 1 ≤ x → x ≤ 1136 → (x ∈ listed ↔ ¬ Converges x) := by
  sorry

end OMA.S_oeis_a077085

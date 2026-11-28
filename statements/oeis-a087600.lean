import Mathlib

/-!
# A087600: Largest n-digit term of A087597, or 0 if no such number exists.

Source: https://oeis.org/A087600
Credit: @Solfanbtc

A040115(m) is the number formed by the absolute differences of adjacent decimal digits of `m`
(e.g. `A040115(7503) = 253`; it is `0` for one-digit `m`, as in the Maple program of A087597).
A087597 is the triangular numbers `m` with A040115(m) triangular. `a(n)` is the largest
`n`-digit term of A087597, or `0` if there is none. This reproduces the data for
`n = 1, …, 12` (Python).

Conjecture (in the entry): no term is zero, i.e. for every `n ≥ 1` there is an `n`-digit
(`10^(n-1) ≤ m < 10^n`) triangular `m` with A040115(m) triangular.
-/

namespace OMA.S_oeis_a087600

/-- `x` is a triangular number `t(t+1)/2`. -/
def Tri (x : ℕ) : Prop := ∃ t : ℕ, x = t * (t + 1) / 2

/-- A040115: absolute differences of adjacent digits (least significant digit first). -/
def A040115 (m : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.zipWith (fun x y => Int.natAbs ((x : ℤ) - y))
    (Nat.digits 10 m).tail (Nat.digits 10 m))

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, 10 ^ (n - 1) ≤ m ∧ m < 10 ^ n ∧ Tri m ∧ Tri (A040115 m) := by
  sorry

end OMA.S_oeis_a087600

import Mathlib

/-!
# A087599: Smallest nonzero n-digit term of A087597

Source: https://oeis.org/A087599
Credit: @Solfanbtc

A040115: `dd(m)` is the number formed by the absolute differences of successive decimal digits of
`m` (leading zeros dropped; `dd(m) = 0` for one-digit `m`). A087597: triangular numbers `m` such
that `dd(m)` is also triangular (`0` counts as triangular): `0, 1, 3, 6, 10, 21, 28, …`. A087599
(offset 1): the smallest nonzero `n`-digit term of A087597, or `0` if there is none:
`1, 10, 105, 2211, 16836, 105111, 2220778, …` (a search reproduces the first 7 data terms; e.g.
`dd(2211) = 10`).

Conjecture (OEIS comment): no term is zero, i.e. for every `n ≥ 1` there is an `n`-digit triangular
number `m` with `dd(m)` triangular.
-/

namespace OMA.S_oeis_a087599

/-- `x` is a triangular number `k(k+1)/2`. -/
def IsTri (x : ℕ) : Prop := ∃ k : ℕ, x = k * (k + 1) / 2

/-- A040115: absolute differences of successive digits (`Nat.digits` is least significant first;
the differences keep that order). -/
def dd (m : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.zipWith (fun x y => if x ≤ y then y - x else x - y)
    (Nat.digits 10 m) (Nat.digits 10 m).tail)

/-- No term of A087599 is zero. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, 10 ^ (n - 1) ≤ m ∧ m < 10 ^ n ∧ IsTri m ∧ IsTri (dd m) := by
  sorry

end OMA.S_oeis_a087599

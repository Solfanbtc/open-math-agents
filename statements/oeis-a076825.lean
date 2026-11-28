import Mathlib

/-!
# A076825: Let u(1)=1, u(n)=2^u(n-1) (mod n), sequence gives values of n such that u(n)=1.

Source: https://oeis.org/A076825
Credit: @Solfanbtc

`u(1) = 1` and `u(n) = 2^u(n-1) mod n` for `n ≥ 2` (the least nonnegative residue, as in the
entry's `PowerMod` program). A076825 is the increasing list `a(1) = 1, a(2) = 3, a(3) = 15, …`
of the `n ≥ 1` with `u(n) = 1`, i.e. `a(n) = Nat.nth T (n - 1)` for the set `T` of such `n`.
This reproduces every term of %S, %T, %U (checked in Python).

Conjecture (formula in the entry): `a(n)/n^2 → ∞`. (If `T` were finite, `Nat.nth` would be `0`
from some point on and the statement would be false, as the conjecture presupposes that `a(n)`
exists for every `n`.)
-/

namespace OMA.S_oeis_a076825

/-- `u(n)`; position `0` is unused (set to `1`). -/
def u : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 ^ u (n + 1) % (n + 2)

/-- The terms of A076825. -/
def T : Set ℕ := {n | 1 ≤ n ∧ u n = 1}

/-- `a(n)`, `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ T) (n - 1)

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a076825

import Mathlib

/-!
# A070993: Numbers n whose 3x+1 trajectory reaches n+1

Source: https://oeis.org/A070993
Credit: @Solfanbtc

The "3x+1" map is `C(x) = x/2` for even `x` and `3x + 1` for odd `x`; `n` is a term if some iterate
`C^[k](n)`, `k ≥ 1`, equals `n + 1`: `3, 7, 9, 15, 19, 25, 33, 39, …, 4857, 7287` (a direct search
reproduces all 37 data terms; the trajectory is followed until it reaches `1`).

Question (Benoit Cloitre and Boris Gourevitch, OEIS comment): "Is this sequence finite? (it seems
there are no further terms below `10^6`)"; Donovan Johnson: no more terms `< 10^9`. Stated in its
expected form: the set of terms is finite.
-/

namespace OMA.S_oeis_a070993

/-- The 3x+1 map. -/
def C (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The trajectory of `n ≥ 1` under `C` reaches `n + 1`. -/
def IsTerm (n : ℕ) : Prop := 1 ≤ n ∧ ∃ k : ℕ, 1 ≤ k ∧ C^[k] n = n + 1

/-- The sequence A070993 is finite. -/
theorem main : {n : ℕ | IsTerm n}.Finite := by
  sorry

end OMA.S_oeis_a070993

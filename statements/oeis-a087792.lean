import Mathlib

/-!
# A087792: Indices n such that S^n(1) is an integer where S(x) = 4/3*ceiling(x).

Source: https://oeis.org/A087792
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, OEIS A087792): a(n) = 3n + O(sqrt(n)).

Definitions: S(x) = (4/3) ceiling(x) on ℚ; the terms are the m >= 0 with S^m(1) an integer, in
increasing order (offset 0: a(0) = 0, a(1) = 3, a(2) = 5, ...), so a(n) = `Nat.nth` of that set
at n. The set is infinite (as the conjecture presupposes; numerically about one m in three).
The claim is the big-O statement a(n) - 3n = O(sqrt n) as n → ∞.
Checked numerically: the listed terms are reproduced, and |a(n) - 3n| / sqrt(n) <= 5.48 for all
terms up to m = 60000 (20108 terms).
-/

namespace OMA.S_oeis_a087792

open Filter Asymptotics

/-- S(x) = (4/3) ⌈x⌉. -/
def S (x : ℚ) : ℚ := 4 / 3 * ⌈x⌉

/-- `S^m(1)` is an integer. -/
def IsIndex (m : ℕ) : Prop := ∃ z : ℤ, S^[m] 1 = z

/-- a(n), the n-th index (from n = 0). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsIndex n

theorem main : {m : ℕ | IsIndex m}.Infinite ∧
    (fun n : ℕ => (a n : ℝ) - 3 * n) =O[atTop] (fun n : ℕ => Real.sqrt n) := by
  sorry

end OMA.S_oeis_a087792

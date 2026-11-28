import Mathlib

/-!
# A066661: Numbers m such that floor((1+1/m)^k)=k for an integer k>1.

Source: https://oeis.org/A066661
Credit: @Solfanbtc

The sequence lists, in increasing order, the positive integers `m` for which some integer
`k > 1` satisfies `⌊(1 + 1/m)^k⌋ = k` (e.g. `⌊(5/4)^11⌋ = 11`, so `4` is a term).
Data: `2, 3, 4, 5, 7, 13, 20, 27, 31, ...` (offset 1).

Conjecture (Benoit Cloitre, in the entry): `a(n) ~ C n log n` with `C = 1.5...`.

The constant is only given as "`1.5...`", so the statement is: there is `C` with decimal
expansion beginning `1.5` (`1.5 ≤ C < 1.6`) such that `a(n) ~ C n log n` (natural log). This
includes that the sequence is infinite (`Nat.nth` of a finite set is eventually `0`).

A python3 check (exact integer arithmetic, `⌊(1+1/m)^k⌋ = (m+1)^k div m^k`, scanning `k` past the
upper crossing of `(1+1/m)^k` and `k`): the definition reproduces all 59 listed terms
(`m ≤ 365`); at `n = 59`, `1.5 n log n ≈ 361` against `a(59) = 365`.
-/

namespace OMA.S_oeis_a066661

open Filter Asymptotics

/-- `m` is a term: `m ≥ 1` and `⌊(1 + 1/m)^k⌋ = k` for some integer `k > 1`. -/
def IsTerm (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ k : ℕ, 1 < k ∧ ⌊((1 : ℝ) + 1 / m) ^ k⌋ = k

/-- `a n`, the `n`-th term (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Cloitre's conjecture: `a(n) ~ C n log n` with `C = 1.5...`. -/
theorem main : ∃ C : ℝ, (1.5 : ℝ) ≤ C ∧ C < 1.6 ∧
    (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => C * n * Real.log n) := by
  sorry

end OMA.S_oeis_a066661

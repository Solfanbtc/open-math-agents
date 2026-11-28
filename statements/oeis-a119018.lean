import Mathlib

/-!
# A119018: a(1) = 1; a(n) is the smallest number not yet used that is not relatively prime to n nor relatively prime to a(n-1).

Source: https://oeis.org/A119018
Credit: @Solfanbtc

Conjecture (entry comment): this sequence includes every integer greater than 1.

Definition and the needed fix at n = 2. Read literally with a(1) = 1, no a(2) exists, since
every k is coprime to a(1) = 1. The Maple and Mathematica programs of the entry start from a
dummy value 0 (gcd(0, k) = k), which gives a(2) = 2, the data; a(1) was changed to 1 in 2024
for display only. So: a(1) = 1, and for n ≥ 2, a(n) is the least positive k not among
a(1), ..., a(n-1) with gcd(k, n) > 1 and gcd(k, b) > 1, where b = a(n-1) for n ≥ 3 and b = 0
for n = 2. This reproduces all 71 data terms (python3).

Statement: every integer m ≥ 2 is a term.
(python3: in the first 20000 terms all m < 101 occur; larger primes appear late.)
-/

namespace OMA.S_oeis_a119018

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) =>
    let L := terms (n + 1)
    let b := if n = 0 then 0 else L.getLastD 0
    L ++ [sInf {k : ℕ | 0 < k ∧ k ∉ L ∧ Nat.gcd k (n + 2) ≠ 1 ∧ Nat.gcd k b ≠ 1}]

/-- A119018(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main : ∀ m : ℕ, 2 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a119018

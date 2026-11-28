import Mathlib

/-!
# A139004: Number of operations A000142 (i.e., x!) or A000196 (i.e., floor(sqrt(x))) needed to get n, starting with 4.

Source: https://oeis.org/A139004
Credit: @Solfanbtc

Conjecture (Knuth, OEIS A139004, comment): any number can be obtained in this way, starting
from 4, i.e. every positive integer n is obtained from 4 by finitely many applications of
x ↦ x! and x ↦ floor(sqrt(x)) (so a(n) ≠ -1 for every n ≥ 1).

Conventions:
* `Reach` is the least set of natural numbers containing 4 and closed under `Nat.factorial`
  and `Nat.sqrt` (= floor(sqrt x), A000196). "Any number" is any positive integer (offset 1;
  0 is never reached since both operations map positive integers to positive integers).
* In Knuth's original formulation square roots are real and followed by floors; for natural x,
  floor(sqrt(floor(sqrt x))) = floor(sqrt(sqrt x)), so the reachable integers are the same as
  with the combined operation floor(sqrt(x)) used in this entry.
* (Sloane's remark on starting from 2 with one use of tan is conditional on Knuth's
  conjecture and is not stated.) Examples from the entry: 2 = s4, 1 = ss4, 5 = sssssff4.
-/

namespace OMA.S_oeis_a139004

/-- Numbers obtainable from 4 by factorials and integer square roots. -/
inductive Reach : ℕ → Prop
  | four : Reach 4
  | fact {x : ℕ} : Reach x → Reach x.factorial
  | sqrt {x : ℕ} : Reach x → Reach (Nat.sqrt x)

/-- Knuth's conjecture: every positive integer is obtained from 4. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Reach n := by
  sorry

end OMA.S_oeis_a139004

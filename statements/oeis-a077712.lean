import Mathlib

/-!
# A077712: a(1) = 1, a(n) = the smallest squarefree number > a(n-1) which contains all the digits of a(n-1).

Source: https://oeis.org/A077712
Credit: @Solfanbtc

"Contains all the digits of a(n-1)" is read with multiplicity: the multiset of decimal digits of
`a(n-1)` is contained in the multiset of decimal digits of `a(n)`. This is the reading that
matches the data: with mere digit-set containment the term after 101 would be 102 (squarefree,
digits ⊇ {0, 1}), while the entry has 110; and after 110 it would be 130, while the entry has 1001.
We checked by brute force that the multiset reading reproduces the terms
1, 10, 101, 110, 1001, ..., 1000010 of %S, and it matches the pattern of all listed terms
described by Ray Chandler in the entry.
If no such number existed, `sInf ∅ = 0` would be used; this never happens (an interval
`[P * 10^j, (P + 1) * 10^j)` contains squarefree numbers for large `j`).

Conjecture (from the entry): every term contains only the digits 0 and 1.
(Ray Chandler checked this up to a(740) = 10^407 + 11.)
-/

namespace OMA.S_oeis_a077712

/-- The decimal digits of `k`, counted with multiplicity, all occur in `m`. -/
def ContainsDigits (m k : ℕ) : Prop :=
  ((Nat.digits 10 k : List ℕ) : Multiset ℕ) ≤ ((Nat.digits 10 m : List ℕ) : Multiset ℕ)

/-- A077712 with offset 1 (`a 0` is an unused placeholder). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sInf {m | a (n + 1) < m ∧ Squarefree m ∧ ContainsDigits m (a (n + 1))}

/-- Conjecture: for all `n ≥ 1`, every decimal digit of `a n` is 0 or 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ d ∈ Nat.digits 10 (a n), d = 0 ∨ d = 1 := by
  sorry

end OMA.S_oeis_a077712

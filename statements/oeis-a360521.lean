import Mathlib

/-!
# A360521: a(0) = 0; for n > 0, a(n) is the smallest positive number not occurring earlier such that neither the binary string a(n-1) + a(n) nor the same string reversed appear in the binary string concatenation of a(0)..a(n-1).

Source: https://oeis.org/A360521
Credit: @Solfanbtc

Binary strings are written most significant bit first, and the binary string of `0` is `"0"`
(the entry's example: the concatenation of `a(0)..a(10)` is `"0110111001011010110100111110001"`,
starting with the `"0"` of `a(0)`). "Appears in" means occurs as a contiguous substring
(`List.IsInfix`). When the binary string of `a(n-1) + a(n)` is reversed, its leading zeros are
kept (as the entry says), which is automatic for list reversal.

`a(n)` is defined with `sInf` exactly as in the name; a candidate always exists (any `k` with
`a(n-1) + k ≥ 2^L`, `L` the length of the concatenation, has a binary string too long to appear,
and only finitely many such `k` have occurred), so `sInf` is the least candidate.

Conjecture (A360521 comment): the sequence `a(1), a(2), …` is a permutation of the positive
integers.
-/

namespace OMA.S_oeis_a360521

/-- The binary string of `m`, most significant bit first, with `bin 0 = [0]`. -/
def bin (m : ℕ) : List ℕ := if m = 0 then [0] else (Nat.digits 2 m).reverse

/-- `terms n = [a(0), …, a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let L := terms n
    let prev := L.getLastD 0
    let s := (L.map bin).flatten
    L ++ [sInf {k | 0 < k ∧ k ∉ L ∧ ¬ bin (prev + k) <:+: s ∧ ¬ (bin (prev + k)).reverse <:+: s}]

/-- A360521(n). -/
noncomputable def a360521 (n : ℕ) : ℕ := (terms n).getLastD 0

/-- Conjecture (OEIS A360521): `n ↦ a(n)` restricted to `n ≥ 1` is a permutation of the
positive integers. -/
theorem main : Set.BijOn a360521 (Set.Ici 1) (Set.Ioi 0) := by
  sorry

end OMA.S_oeis_a360521

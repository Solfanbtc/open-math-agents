import Mathlib

/-!
# A071307: 1/2 number of n X n 0..8 matrices with MM' mod 9 = I.

Source: https://oeis.org/A071307
Credit: @Solfanbtc

Conjecture (Michel Marcus, Nov 08 2022, OEIS A071307): a(n) = 3^(n(n-1)/2) * A071302(n) for n >= 1,
where A071302(n) = (1/2) * (number of n X n 0..2 matrices M with M M' mod 3 = I).

Translation: n X n matrices with entries 0..8 (resp. 0..2) and M M' ≡ I are the matrices over
`ZMod 9` (resp. `ZMod 3`) with M * Mᵀ = 1. Both sides carry the same factor 1/2, so the
conjecture is equivalent to
  #{M over ZMod 9 : M Mᵀ = 1} = 3^(n(n-1)/2) * #{M over ZMod 3 : M Mᵀ = 1},
which is what `main` states (avoiding the halving). Checked against the data: for n = 1..4 the
counts mod 9 are 2, 24, 1296, 839808 and mod 3 are 2, 8, 48, 1152, and 3^(n(n-1)/2) times the
latter gives the former.
-/

namespace OMA.S_oeis_a071307

/-- Number of `n × n` orthogonal matrices over `ZMod m`. -/
def orthCount (m n : ℕ) [NeZero m] : ℕ :=
  (Finset.univ.filter fun M : Matrix (Fin n) (Fin n) (ZMod m) => M * M.transpose = 1).card

theorem main : ∀ n : ℕ, 1 ≤ n → orthCount 9 n = 3 ^ (n * (n - 1) / 2) * orthCount 3 n := by
  sorry

end OMA.S_oeis_a071307

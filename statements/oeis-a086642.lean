import Mathlib

/-!
# A086642: Maximal number of zeros in a column of the character table of the symmetric group S_n.

Source: https://oeis.org/A086642
Credit: @Solfanbtc

Conventions. The rows of the character table of `S_n` are the irreducible complex characters,
i.e. the characters of the simple objects of Mathlib's `FDRep ℂ (Equiv.Perm (Fin n))`
(distinct irreducible representations have distinct characters, so counting characters counts
rows); a column is indexed by (a representative of) a conjugacy class, so the number of zeros
in the column of `g` is the number of irreducible characters `χ` with `χ g = 0`. `a(n)` is the
maximum of this number over `g ∈ S_n`. A000041(n) is the number of partitions of `n`.

Conjecture (Vladeta Jovovic, 2003): `a(n) = A000041(n) - n + 1` for `n > 2`
(verified for 3 ≤ n ≤ 200, per the entry). The data: a(3) = 1 = 3 - 3 + 1, ...,
a(34) = 12277 = 12310 - 34 + 1.
-/

namespace OMA.S_oeis_a086642

/-- The number of zeros in the column of `g` of the character table of `S_n`. -/
noncomputable def zeros (n : ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  Set.ncard {χ : Equiv.Perm (Fin n) → ℂ |
    ∃ V : FDRep ℂ (Equiv.Perm (Fin n)), CategoryTheory.Simple V ∧ V.character = χ ∧ χ g = 0}

/-- `a(n)`: the maximal number of zeros in a column. -/
noncomputable def a (n : ℕ) : ℕ := sSup (Set.range (zeros n))

/-- Jovovic's conjecture: `a(n) = p(n) - n + 1` for `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → a n = Fintype.card (Nat.Partition n) - n + 1 := by
  sorry

end OMA.S_oeis_a086642

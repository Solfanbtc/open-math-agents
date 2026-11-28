import Mathlib

/-!
# A085430: minimal m such that GL(m,2) has an element of order n

Source: https://oeis.org/A085430 (see A014664)
Credit: @Solfanbtc

`a(n)` is the minimal `m` such that the group `GL(m, 2)` of invertible `m × m` matrices over the
field with 2 elements has an element of order `n`: 2, 2, 3, 4, 4, 3, 5, ... (offset 2).

Conjecture (Bill McEachen, Oct 06 2025): `a(p)` divides `p - 1` for every odd prime `p`.

Status: the entry also records (Eric M. Schmidt, May 17 2013) that `a(prime(n)) = A014664(n)`, the
multiplicative order of 2 modulo `prime(n)`, for `n > 1`; together with Fermat's little theorem
this gives the conjecture. We state it faithfully nevertheless.

Encoding: `GL (Fin m) (ZMod 2)` is Mathlib's general linear group; we take `m ≥ 1`.

Sanity check (python, all matrices of size `m ≤ 4`): the element orders first occur at
`a(2..7) = 2, 2, 3, 4, 4, 3` and `a(15) = 4`, matching the data (order 8 needs `m = 5`).
-/

namespace OMA.S_oeis_a085430

/-- A085430: least `m ≥ 1` such that `GL(m, 2)` has an element of order `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∃ g : GL (Fin m) (ZMod 2), orderOf g = n}

/-- McEachen's conjecture. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → a p ∣ p - 1 := by
  sorry

end OMA.S_oeis_a085430

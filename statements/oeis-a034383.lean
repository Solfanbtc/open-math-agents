import Mathlib

/-!
# A034383: Number of labeled groups

Source: https://oeis.org/A034383
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of labeled groups of order `n`, i.e. (Jianing Song, OEIS comment)
the number of ways to define a group structure on a set of `n` elements:
`1, 2, 3, 16, 30, 480, 840, …`. Below, a group structure on `Fin n` is a binary operation
`m : Fin n → Fin n → Fin n` that is associative, has a two-sided identity `e`, and in which
every element has a two-sided inverse with respect to `e`; `a(n)` is the number of such `m`.
(A brute-force count with this definition gives `1, 2, 3` for `n = 1, 2, 3`.)

Conjecture (from the comment of Jianing Song, Mar 02 2024): "It is conjectured
`a(2^r) > a(2^r + 1)` for all sufficiently large `r`." (The entry notes the sequence is strictly
increasing for its first 256 terms, and that `a(2^20) > a(2^20 + 1)` would follow from the
conjecture `A059773(2^r) = A002884(r)`.)
-/

namespace OMA.S_oeis_a034383

/-- `m` is a group law on `Fin n`: associative, with a two-sided identity and two-sided inverses. -/
def IsGroupLaw (n : ℕ) (m : Fin n → Fin n → Fin n) : Prop :=
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
  ∃ e, (∀ x, m e x = x ∧ m x e = x) ∧ ∀ x, ∃ y, m x y = e ∧ m y x = e

/-- A034383: the number of group structures on a set with `n` elements. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {m : Fin n → Fin n → Fin n // IsGroupLaw n m}

/-- `a(2^r) > a(2^r + 1)` for all sufficiently large `r`. -/
theorem main : ∃ R : ℕ, ∀ r : ℕ, R ≤ r → a (2 ^ r + 1) < a (2 ^ r) := by
  sorry

end OMA.S_oeis_a034383

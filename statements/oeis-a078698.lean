import Mathlib

/-!
# A078698: Shoe lacings in which each eyelet has a direct connection to the opposite side

Source: https://oeis.org/A078698
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of ways to lace a shoe that has `n` pairs of eyelets such that
each eyelet has at least one direct connection to the opposite side: `1, 2, 20, 396, 14976, …`.
The lace passes through every eyelet exactly once and must begin and end at the extreme
(front) pair of eyelets.

Model. Eyelets are `(side, position)` with `side : Bool` (`false` = left, `true` = right) and
`position : Fin n` (`0` = front). A lacing is an ordering `f : Fin (2n) ≃ eyelets` of all
eyelets starting at the front left eyelet and ending at the front right eyelet (as in all of the
entry's examples for `a(3) = 20`, written `1 … 6`). The two ends are joined across the front (the
lace is tied there), so the "direct connections" of an eyelet are its neighbours along the
cyclic order (`f (t ± 1 mod 2n)`); the condition is that at least one of them lies on the other
side. With this model a brute-force count gives `1, 2, 20, 396, 14976` for `n = 1..5`, as in the
sequence. (Without the closing connection one gets `n = 3 ↦ 16`; the entry's lacing `124356`
starts with two eyelets on the same side, which confirms the closing connection.)

Conjecture (Vladeta Jovovic, Sep 14 2005, OEIS formula): `a(n) = (n-1)!^2 · A051286(n)`,
`A051286(n) = ∑_{k=0}^{n} C(n-k, k)^2` (Hanna's formula; `1, 1, 2, 5, 11, …`). Status: PROVED
("correct, see the Khrabrov/Kokhas reference", Joerg Arndt, May 26 2015). Stated for `n ≥ 1`;
the formula agrees with all 12 data terms.
-/

namespace OMA.S_oeis_a078698

/-- A lacing of `n` pairs of eyelets with the opposite-side condition. -/
def IsLacing (n : ℕ) (f : Fin (2 * n) ≃ Bool × Fin n) : Prop :=
  (∀ t : Fin (2 * n), ((t : ℕ) = 0 ↔ (f t).1 = false ∧ ((f t).2 : ℕ) = 0)) ∧
  (∀ t : Fin (2 * n), ((t : ℕ) = 2 * n - 1 ↔ (f t).1 = true ∧ ((f t).2 : ℕ) = 0)) ∧
  ∀ t : Fin (2 * n), (f (finRotate _ t)).1 ≠ (f t).1 ∨ (f ((finRotate _).symm t)).1 ≠ (f t).1

/-- A078698. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {f : Fin (2 * n) ≃ Bool × Fin n // IsLacing n f}

/-- A051286: `∑_{k=0}^{n} C(n-k, k)^2`. -/
def A051286 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (Nat.choose (n - k) k) ^ 2

/-- Jovovic's formula (proved): `a(n) = (n-1)!^2 · A051286(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (n - 1).factorial ^ 2 * A051286 n := by
  sorry

end OMA.S_oeis_a078698

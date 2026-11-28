import Mathlib

/-!
# A079243: Number of isomorphism classes of associative non-commutative non-anti-associative anti-commutative closed binary operations on a set of order n.

Source: https://oeis.org/A079243
Credit: @Solfanbtc

Conventions (C. van den Bosch's series of entries A079195-A079245):
* commutative: `x * y = y * x` for all `x, y`; non-commutative: its negation;
* anti-commutative: `x * y = y * x` implies `x = y`;
* anti-associative: `(x * y) * z ≠ x * (y * z)` for all `x, y, z`; non-anti-associative: its
  negation, i.e. `(x * y) * z = x * (y * z)` for some `x, y, z`.
Two operations on the set `{0, ..., n-1}` are isomorphic when some permutation `σ` satisfies
`σ (f x y) = g (σ x) (σ y)`.
We checked by computer that these conventions give 0, 2, 2, 8, 2 labeled operations for
`n = 1..5` (A079242) and 0, 2, 2, 3, 2 isomorphism classes (the terms of A079243).

Conjecture (Andrew Howroyd, 2022): `a(n) = A000005(n)`, the number of divisors of `n`, for `n > 1`.
-/

namespace OMA.S_oeis_a079243

/-- The operations counted by A079242 on a set of order `n`. -/
def Counted (n : ℕ) (f : Fin n → Fin n → Fin n) : Prop :=
  (∀ x y z, f (f x y) z = f x (f y z)) ∧
  (∃ x y, f x y ≠ f y x) ∧
  (∃ x y z, f (f x y) z = f x (f y z)) ∧
  (∀ x y, f x y = f y x → x = y)

/-- Isomorphism of binary operations on `Fin n`. -/
def Iso (n : ℕ) (f g : {f : Fin n → Fin n → Fin n // Counted n f}) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ x y, σ (f.1 x y) = g.1 (σ x) (σ y)

/-- `a(n)`: the number of isomorphism classes. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card (Quot (Iso n))

/-- Conjecture: `a(n)` is the number of divisors of `n` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n = n.divisors.card := by
  sorry

end OMA.S_oeis_a079243

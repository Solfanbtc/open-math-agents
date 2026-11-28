import Mathlib

/-!
# A005157: Number of totally symmetric plane partitions that fit in an n X n X n box.

Source: https://oeis.org/A005157
Credit: @Solfanbtc

Conjectures (Peter Bala, OEIS A005157, checked up to p = 1009):
* if `p == 1 (mod 6)` is prime then `a(p) == 2^((p+5)/6) (mod p^2)`;
* if `p == 5 (mod 6)` is prime then `a(p) == 2^((p+1)/6) (mod p^2)`.

Formalized: a plane partition fitting in an `n × n × n` box is identified with its
three-dimensional Young diagram, a down-closed subset of `{0,…,n-1}^3` (coordinatewise order).
It is totally symmetric when the diagram is invariant under every permutation of the three
coordinates; the transpositions `(x,y,z) ↦ (y,x,z)` and `(x,y,z) ↦ (x,z,y)` generate the
symmetric group, so invariance under these two suffices. `a n` counts such subsets; it is
OEIS A005157 with its offset 0 (`a 0 = 1`, the empty partition). Brute-force enumeration of this
definition gives `1, 2, 5, 16, 66` for `n = 0..4`, matching the OEIS terms, and Stembridge's
product formula `∏_{1≤i≤j≤k≤n} (i+j+k-1)/(i+j+k-2)` confirms both congruences for every prime
`p < 120` with this indexing. The congruences are stated with `Int.ModEq`; the exponents
`(p+5)/6` and `(p+1)/6` are exact natural-number quotients for the primes concerned.
-/

namespace OMA.S_oeis_a005157

open Classical

/-- `S` is the 3D diagram of a totally symmetric plane partition in the `n × n × n` box:
down-closed in each coordinate and invariant under permutations of the coordinates. -/
def IsTSPP (n : ℕ) (S : Finset (Fin n × Fin n × Fin n)) : Prop :=
  (∀ x y z x' y' z' : Fin n, (x, y, z) ∈ S → x' ≤ x → y' ≤ y → z' ≤ z → (x', y', z') ∈ S) ∧
  (∀ x y z : Fin n, (x, y, z) ∈ S → (y, x, z) ∈ S ∧ (x, z, y) ∈ S)

/-- A005157: the number of totally symmetric plane partitions that fit in an `n × n × n` box. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (IsTSPP n)).card

theorem main :
    (∀ p : ℕ, p.Prime → p % 6 = 1 → (a p : ℤ) ≡ 2 ^ ((p + 5) / 6) [ZMOD (p : ℤ) ^ 2]) ∧
    (∀ p : ℕ, p.Prime → p % 6 = 5 → (a p : ℤ) ≡ 2 ^ ((p + 1) / 6) [ZMOD (p : ℤ) ^ 2]) := by
  sorry

end OMA.S_oeis_a005157

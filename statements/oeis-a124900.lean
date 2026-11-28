import Mathlib

/-!
# A124900: Largest order of any solvable transitive Galois group for an irreducible polynomial of degree n.

Source: https://oeis.org/A124900
Credit: @Solfanbtc

Conjecture (entry comment): "The sequence a(prime(n)), which begins 2, 6, 20, 42, 110, 156,
272, 342, 506, 812, increases without bound. It appears that a(prime(n)) may equal
prime(n)(prime(n)-1), which is A036689."

Status: this follows from Galois's classical theorem that a solvable transitive permutation
group of prime degree p is (conjugate to) a subgroup of the affine group AGL(1, p), of order
p(p-1), which is itself solvable and transitive. It is stated here faithfully.

Formalization.
* The Galois group of an irreducible polynomial of degree n over ℚ acts transitively on its n
  roots; conversely every transitive solvable permutation group of degree n occurs (Shafarevich:
  every finite solvable group is a Galois group over ℚ; take the fixed field of a point
  stabilizer and the minimal polynomial of a primitive element). So a(n) is the largest order of
  a solvable transitive subgroup of the symmetric group on n letters; we define it that way.
* Statement: for every prime p, a(p) = p(p-1), and a(prime(n)) → ∞.
-/

namespace OMA.S_oeis_a124900

/-- A124900(n): largest order of a solvable transitive subgroup of `Perm (Fin n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : Subgroup (Equiv.Perm (Fin n)),
    IsSolvable G ∧ MulAction.IsPretransitive G (Fin n) ∧ Nat.card G = k}

theorem main :
    (∀ p : ℕ, p.Prime → a p = p * (p - 1)) ∧
      Filter.Tendsto (fun n : ℕ => a (Nat.nth Nat.Prime n)) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a124900

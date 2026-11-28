import Mathlib

/-!
# A002106: Number of transitive permutation groups of degree n.

Source: https://oeis.org/A002106
Credit: @Solfanbtc

Conjecture (OEIS A002106): `a(n)`, the number of transitive permutation groups of degree `n`
(i.e. of conjugacy classes of transitive subgroups of `S_n`), is the number of Galois groups of
irreducible polynomials of degree `n` (over `ℚ`), each viewed as a permutation group on the
`n` roots, up to the same equivalence (conjugacy in `S_n`).

Every such Galois group is transitive (the source notes this), so the set of realized classes is
a subset of the finite set of transitive classes, and the two counts agree iff every transitive
subgroup `G ≤ S_n` is realized. We state that equivalent form: for every `n ≥ 1` and every
transitive `G ≤ Perm (Fin n)`, some irreducible `f ∈ ℚ[X]` of degree `n` has a labelling
`e : roots of f in ℂ ≃ Fin n` of its roots that carries the image of `Gal(f/ℚ)` in the
permutations of the roots exactly onto `G` (so `Gal(f)` is conjugate to `G` in `S_n`).

Conventions:
* Base field `ℚ`: the source's standard reading (it cites the open case `K = ℚ`).
* `n ≥ 1`: A002106 starts at `n = 1`. For `n = 0` the trivial action on the empty set is
  vacuously transitive, but no irreducible polynomial has degree `0`, so the literal
  statement would fail trivially there; this is the minimal fix.
-/

namespace OMA.S_oeis_a002106

open Polynomial

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ G : Subgroup (Equiv.Perm (Fin n)),
    MulAction.IsPretransitive G (Fin n) →
    ∃ f : ℚ[X], Irreducible f ∧ f.natDegree = n ∧
      ∃ e : f.rootSet ℂ ≃ Fin n,
        letI := Gal.splits_ℚ_ℂ (p := f)
        (Gal.galActionHom f ℂ).range.map (Equiv.permCongrHom e).toMonoidHom = G := by
  sorry

end OMA.S_oeis_a002106

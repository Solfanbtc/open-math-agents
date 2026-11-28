import Mathlib

/-!
# A conjecture on Galois groups and large fields

Source: https://arxiv.org/abs/2610.41843
Credit: @Solfanbtc

Let `p` be a prime number and `K` a field such that `p` is prime to the absolute Galois group
`Gal(K)`, in the sense that `p` does not divide the degree of any finite Galois extension of `K`.
The abstract conjectures that `K` is large in the sense of Pop: any smooth algebraic curve `C`
over `K` with a `K`-rational point has infinitely many `K`-rational points.

Conventions.
* A finite Galois extension of `K` is a field `L` with `[Algebra K L]`, finite dimensional and
  `IsGalois K L` (normal and separable). Every finite extension of `K` is isomorphic to one in the
  universe of `K`, so quantifying over `L : Type u` loses nothing.
* A smooth curve over `K` is a `K`-scheme `f : C ⟶ Spec K` with `C` integral, `f` separated,
  of finite type (locally of finite type and quasi-compact) and smooth of relative dimension `1`.
  A `K`-rational point is a section `s : Spec K ⟶ C` of `f`.
  (Dropping integrality or separatedness gives an equivalent notion of large field, since a
  `K`-point of any smooth `K`-scheme of relative dimension `1` lies on an integral affine open
  subscheme that is again a smooth curve; we keep the standard definition.)
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace OMA.S_arxiv_2610_41843

/-- `p` is prime to the absolute Galois group of `K`: `p` divides the degree of no finite
Galois extension of `K`. -/
def PrimeToAbsGalois (p : ℕ) (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ¬ p ∣ Module.finrank K L

/-- The `K`-rational points of a `K`-scheme `f : C ⟶ Spec K`: sections of `f`. -/
def RationalPoints (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of K)) :
    Type u :=
  {s : Spec (CommRingCat.of K) ⟶ C // s ≫ f = 𝟙 _}

/-- `K` is large in the sense of Pop: every smooth curve over `K` (integral, separated, of finite
type, smooth of relative dimension `1`) with a `K`-rational point has infinitely many
`K`-rational points. -/
def IsLargeField (K : Type u) [Field K] : Prop :=
  ∀ (C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of K)),
    IsIntegral C → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    SmoothOfRelativeDimension 1 f →
    Nonempty (RationalPoints K f) → Infinite (RationalPoints K f)

/-- Conjecture (arXiv 2610.41843): if `p` is a prime and `p` does not divide the degree of any
finite Galois extension of the field `K`, then `K` is large in the sense of Pop. -/
theorem main : ∀ (p : ℕ), p.Prime → ∀ (K : Type u) [Field K], PrimeToAbsGalois p K →
    IsLargeField K := by
  sorry

end OMA.S_arxiv_2610_41843

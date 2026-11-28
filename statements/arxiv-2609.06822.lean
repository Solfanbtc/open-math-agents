import Mathlib

/-!
# High dimensional Riemann–Roch spaces in linear spaces with small squares

Source: https://arxiv.org/abs/2609.06822
Credit: @Solfanbtc

Let `F` be a function field over an algebraically closed field `K` and `S` a finite dimensional
`K`-subspace of `F`. The square `S²` is spanned by all products of pairs of elements of `S`.
Conjecture (from the abstract): if `dim S² ≤ 3 dim S - 4`, then `S²` contains a Riemann–Roch
space of dimension at least `2 dim S - 1 + g`, where `g` is the genus of `F`.

Conventions (standard, following Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1):
* A function field over `K` is modelled by Mathlib's `FunctionField K F`: `F` is a finite
  extension of the rational function field `K(t)`.
* A place of `F/K` is a valuation subring `O` of `F` with `K ⊆ O ⊊ F`; it is a discrete
  valuation ring. A uniformizer `π` of `O` generates its maximal ideal; for `x ∈ F` and `n ∈ ℤ`,
  `v_O(x) ≥ -n` iff `x * π ^ n ∈ O` (independent of the uniformizer).
* A divisor is a finitely supported `ℤ`-valued function on places. Since `K` is algebraically
  closed every place has degree 1, so `deg D = ∑ D(P)`.
* The Riemann–Roch space is `L(D) = {x ∈ F | x = 0 ∨ ∀ P, v_P(x) ≥ -D(P)}`, a `K`-subspace
  (we use its span, which equals it), and `ℓ(D) = dim_K L(D)`.
* The genus is `g = max_D (deg D - ℓ(D) + 1)` (Stichtenoth, Def. 1.4.15; the maximum exists by
  Riemann's theorem). We take `sSup` of this set of integers.
* `S²` is `S * S` (Mathlib's product of submodules, the span of all products). Dimensions are
  compared in `ℤ` so that `3 dim S - 4` is not truncated (for `dim S ≤ 1` the hypothesis fails).
* "`S²` contains a Riemann–Roch space": some divisor `D` has `L(D) ⊆ S²`. This class of
  subspaces is closed under scaling by `F^×`, matching the scaling invariance of the hypothesis.
-/

namespace OMA.S_arxiv_2609_06822

open Module

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Places of `F/K`: valuation subrings of `F` containing `K`, other than `F` itself. -/
def Place : Type _ :=
  {O : ValuationSubring F // (∀ c : K, algebraMap K F c ∈ O) ∧ O ≠ ⊤}

variable {K F}

/-- `π` is a uniformizer of the valuation subring `O`: a non-unit of `O` generating its
maximal ideal. -/
def IsUniformizer (O : ValuationSubring F) (π : F) : Prop :=
  π ∈ O ∧ π⁻¹ ∉ O ∧ ∀ x ∈ O, x⁻¹ ∉ O → x * π⁻¹ ∈ O

/-- `v_O(x) ≥ -n`. -/
def OrdGE (O : ValuationSubring F) (x : F) (n : ℤ) : Prop :=
  ∃ π, IsUniformizer O π ∧ x * π ^ n ∈ O

/-- The Riemann–Roch space `L(D)` as a set. -/
def RRSet (D : Place K F →₀ ℤ) : Set F :=
  {x | x = 0 ∨ ∀ P : Place K F, OrdGE P.1 x (D P)}

/-- `ℓ(D) = dim_K L(D)`. -/
noncomputable def ell (D : Place K F →₀ ℤ) : ℤ :=
  (finrank K (Submodule.span K (RRSet D)) : ℤ)

/-- Degree of a divisor (all places have degree 1 since `K` is algebraically closed). -/
def deg (D : Place K F →₀ ℤ) : ℤ := D.sum fun _ n => n

variable (K F)

/-- The genus `g = max_D (deg D - ℓ(D) + 1)`. -/
noncomputable def genus : ℤ :=
  sSup (Set.range fun D : Place K F →₀ ℤ => deg D - ell D + 1)

theorem main : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (S : Submodule K F), FiniteDimensional K S →
    (finrank K ↥(S * S) : ℤ) ≤ 3 * (finrank K S : ℤ) - 4 →
    ∃ D : Place K F →₀ ℤ, RRSet D ⊆ (S * S : Submodule K F) ∧
      2 * (finrank K S : ℤ) - 1 + genus K F ≤ ell D := by
  sorry

end OMA.S_arxiv_2609_06822

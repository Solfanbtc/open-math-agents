import Mathlib

/-!
# A130519: a(n) = Sum_{k=0..n} floor(k/4). (Partial sums of A002265.)

Source: https://oeis.org/A130519
Credit: @Solfanbtc

Conjecture (Stefano Spezia, Jan 04 2019): `a(n+2)` is the maximum effective weight of a
numerical semigroup `S` of genus `n` (Nathan Pflueger, "On nonprimitive Weierstrass points";
`a(n+2) = floor((n+1)^2/8)`, Pflueger's conjectured bound).

Conventions (Pflueger).
* A numerical semigroup is an additive submonoid `S` of `ℕ` with finite complement; its genus
  is the number of gaps `ℕ \ S`.
* A minimal generator of `S` is a nonzero `s ∈ S` that is not the sum of two nonzero elements
  of `S`.
* The effective weight `ewt(S)` is the number of pairs `(s, b)` with `s` a minimal generator,
  `b` a gap and `s < b`.
`main` states that `a(n+2)` is the greatest effective weight among the numerical semigroups of
genus `n`, for every `n ≥ 0`. Brute force (python3, all semigroups of genus `≤ 11`, counts
`1, 1, 2, 4, 7, 12, 23, 39, 67, 118, 204, 343`): the maxima are `0, 0, 1, 2, 3, 4, 6, 8, 10,
12, 15, 18 = a(2), ..., a(13)`.
-/

namespace OMA.S_oeis_a130519

/-- A130519(n) = Sum_{k=0..n} floor(k/4). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k / 4

/-- `s` is a minimal generator of `S`. -/
def IsMinGen (S : AddSubmonoid ℕ) (s : ℕ) : Prop :=
  s ∈ S ∧ s ≠ 0 ∧ ¬ ∃ x ∈ S, ∃ y ∈ S, x ≠ 0 ∧ y ≠ 0 ∧ x + y = s

/-- Pflueger's effective weight of `S`. -/
noncomputable def ewt (S : AddSubmonoid ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | IsMinGen S p.1 ∧ p.2 ∉ S ∧ p.1 < p.2}

/-- Effective weights of the numerical semigroups of genus `n`. -/
def ewts (n : ℕ) : Set ℕ :=
  {w | ∃ S : AddSubmonoid ℕ, ((S : Set ℕ)ᶜ).Finite ∧ ((S : Set ℕ)ᶜ).ncard = n ∧ ewt S = w}

/-- Spezia's conjecture: the maximum effective weight in genus `n` is `a(n+2)`. -/
theorem main : ∀ n : ℕ, IsGreatest (ewts n) (a (n + 2)) := by
  sorry

end OMA.S_oeis_a130519

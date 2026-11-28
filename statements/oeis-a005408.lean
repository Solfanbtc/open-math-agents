import Mathlib

/-!
# A005408: The odd numbers: a(n) = 2*n + 1.

Source: https://oeis.org/A005408
Credit: @Solfanbtc

Conjecture (Gary W. Adamson, on A005408, relating to A216371): an integer `b` of the form
`4q - 1` or `4q + 1` with `q > 0` is in A216371 (odd primes with one coach) iff the top row of
its coach is a permutation of the first `q` odd integers `1, 3, ..., 2q - 1`.

Conventions (Hilton and Pedersen's coaches, cf. A003558, A135303, A216371):
* For odd `b`, the top row of the coach of `b` is `a₁ = 1, a₂, a₃, ...` where
  `b - aᵢ = 2^(kᵢ) * aᵢ₊₁` with `aᵢ₊₁` odd, stopped just before the sequence returns to `1`.
  Example from the source: `19 : [1, 9, 5, 7, 3]`, since `19 - 1 = 2 * 9`, `19 - 9 = 2 * 5`,
  `19 - 5 = 2 * 7`, `19 - 7 = 2^2 * 3`, `19 - 3 = 2^4 * 1`.
  Here `coachStep b a` is the odd part of `b - a`, and the row is the orbit of `1` under it,
  listed for one minimal period.
* A003558: `suborder b` is the least `m ≥ 1` with `2^m ≡ ±1 (mod b)`.
* A135303 (number of coaches of `b = 2n + 1`): `φ(b) / (2 * suborder b)` (Coach theorem).
  We index it by `b` itself rather than by `n = (b - 1)/2`.
* A216371: odd primes `p` with `A135303((p - 1)/2) = 1`.

The conjecture quantifies over all integers `b = 4q ± 1` with `q > 0`, i.e. all odd `b ≥ 3`;
it is not restricted to primes. Checked numerically (both directions) for all odd `b ≤ 3000`.
-/

namespace OMA.S_oeis_a005408

/-- One step of the top row of the coach of `b`: the odd part of `b - a`. -/
def coachStep (b a : ℕ) : ℕ := (b - a) / 2 ^ padicValNat 2 (b - a)

/-- The top row of the coach of `b`: the orbit of `1` under `coachStep b`,
listed for one minimal period (`a₁ = 1, a₂, ...` up to, excluding, the return to `1`). -/
noncomputable def coachTopRow (b : ℕ) : List ℕ :=
  (List.range (Function.minimalPeriod (coachStep b) 1)).map fun i => (coachStep b)^[i] 1

/-- A003558 (indexed by `b = 2n + 1`): least `m ≥ 1` with `2^m ≡ 1` or `2^m ≡ -1 (mod b)`. -/
noncomputable def suborder (b : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (2 ^ m ≡ 1 [MOD b] ∨ 2 ^ m + 1 ≡ 0 [MOD b])}

/-- A135303 (indexed by `b = 2n + 1`): the number of coaches of `b`, `φ(b) / (2 k(b))`. -/
noncomputable def numCoaches (b : ℕ) : ℕ := Nat.totient b / (2 * suborder b)

/-- A216371: odd primes with one coach. -/
def A216371 : Set ℕ := {p | p.Prime ∧ Odd p ∧ numCoaches p = 1}

theorem main : ∀ b q : ℕ, 0 < q → (b = 4 * q - 1 ∨ b = 4 * q + 1) →
    (b ∈ A216371 ↔ (coachTopRow b).Perm ((List.range q).map fun i => 2 * i + 1)) := by
  sorry

end OMA.S_oeis_a005408

import Mathlib

/-!
# Nivat's conjecture

Source: https://en.wikipedia.org/wiki/Nivat%27s_conjecture
Credit: @Solfanbtc

From the source: let `A` be a finite alphabet and let `x : ℤ² → A` be a two-dimensional
configuration. For positive integers `n` and `m`, let `P_x(n, m)` be the number of distinct
`n × m` rectangular patterns that occur in `x`. The configuration is called periodic if there is a
nonzero vector `v ∈ ℤ²` such that `x (u + v) = x u` for every `u ∈ ℤ²`. Nivat's conjecture states
that if there exist positive integers `n, m` such that `P_x(n, m) ≤ n m`, then `x` is periodic.

The source records partial results: periodicity under `P_x(n, m) ≤ n m / 16` (Quas–Zamboni) and
`P_x(n, m) ≤ n m / 2` (Cyr–Kra), the cases of height at most `2` (Sander–Tijdeman) and `3`
(Cyr–Kra), and uniformly recurrent configurations (Kari–Moutot).

Encoding: `ℤ²` is `ℤ × ℤ`; the `n × m` pattern of `x` at `u` is the map `(i, j) ↦ x (u + (i, j))`
on `Fin n × Fin m`, and `P_x(n, m)` is the number of elements of the set of these patterns as `u`
ranges over `ℤ²` (a finite set, since `A` is finite).
-/

namespace OMA.S_wpc_nivat_conjecture

/-- The `n × m` rectangular pattern of `x` at position `u`. -/
def pattern {A : Type} (x : ℤ × ℤ → A) (n m : ℕ) (u : ℤ × ℤ) : Fin n → Fin m → A :=
  fun i j => x (u.1 + i, u.2 + j)

/-- `P_x(n, m)`: the number of distinct `n × m` rectangular patterns that occur in `x`. -/
noncomputable def patternCount {A : Type} (x : ℤ × ℤ → A) (n m : ℕ) : ℕ :=
  (Set.range (pattern x n m)).ncard

/-- `x` is periodic: some nonzero vector `v` satisfies `x (u + v) = x u` for every `u`. -/
def IsPeriodic {A : Type} (x : ℤ × ℤ → A) : Prop :=
  ∃ v : ℤ × ℤ, v ≠ 0 ∧ ∀ u, x (u + v) = x u

/-- **Nivat's conjecture**: a configuration of `ℤ²` over a finite alphabet that has, for some
positive integers `n` and `m`, at most `n m` distinct `n × m` rectangular patterns is periodic. -/
theorem main : ∀ (A : Type) [Finite A] (x : ℤ × ℤ → A),
    (∃ n m : ℕ, 0 < n ∧ 0 < m ∧ patternCount x n m ≤ n * m) → IsPeriodic x := by
  sorry

end OMA.S_wpc_nivat_conjecture

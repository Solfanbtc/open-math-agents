import Mathlib

/-!
# Super-positivity via Dirichlet theta functions

Source: https://arxiv.org/abs/2611.12152 (Arshay Sheth, Wayne Voo)
Credit: @Solfanbtc

The abstract: let `χ` be a quadratic Dirichlet character and `Λ(s, χ)` its completed `L`-function.
The authors conjecture that the sequence `(Λ^{(2m)}(1/2, χ))_{m ≥ 0}` is always eventually
increasing and has at most one turning point.

Conventions (standard readings, stated here explicitly):
* A *quadratic* Dirichlet character is one of order exactly `2` (`χ ^ 2 = 1`, `χ ≠ 1`). The
  completed `L`-function is the one attached to a *primitive* character, so `χ` is taken primitive
  (this is the setting in which `Λ(s, χ)` is entire and satisfies `Λ(1 - s, χ) = Λ(s, χ)`).
* `Λ(s, χ) = N ^ (s / 2) * completedLFunction χ s`, where Mathlib's
  `DirichletCharacter.completedLFunction χ s = Γ_ℝ(s + a) L(s, χ)` (`a = 0` for even, `a = 1` for
  odd `χ`). This equals the classical `(N / π) ^ (s / 2) Γ((s + a) / 2) L(s, χ)` up to the positive
  constant `π ^ (a / 2)`, so it has the same sign and monotonicity pattern of derivatives; it is
  the normalisation symmetric about `s = 1/2` (only for that normalisation are the odd derivatives
  at `1/2` zero, which is why the source only looks at the even ones).
  A numerical check (theta-integral representation, characters mod 3, 4, 5, 8) gives the odd
  derivatives at `1/2` equal to `0` and even ones decreasing then increasing, as conjectured.
* `Λ` is real on the real line for real `χ`, so the derivatives at `1/2` are real; we take `.re`.
* "Eventually increasing with at most one turning point" is read as: there is `M` such that the
  sequence is strictly decreasing on `m ≤ M` and strictly increasing on `m ≥ M` (`M = 0` means
  increasing throughout; the single possible turning point is at `M`).
-/

namespace OMA.S_arxiv_2611_12152

open DirichletCharacter

/-- The completed `L`-function `Λ(s, χ) = N ^ (s / 2) Γ_ℝ(s + a) L(s, χ)`, symmetric about `1/2`
for a primitive real character. -/
noncomputable def completedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * completedLFunction χ s

/-- The sequence `m ↦ Λ^{(2m)}(1/2, χ)` (real-valued for real `χ`). -/
noncomputable def evenDerivSeq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (m : ℕ) : ℝ :=
  (iteratedDeriv (2 * m) (completedL χ) (1 / 2)).re

/-- Conjecture (Sheth–Voo): for every primitive quadratic Dirichlet character `χ`, the sequence
`(Λ^{(2m)}(1/2, χ))_{m ≥ 0}` is eventually increasing and has at most one turning point. -/
theorem main :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 → χ.IsPrimitive →
    ∃ M : ℕ, (∀ m < M, evenDerivSeq χ (m + 1) < evenDerivSeq χ m) ∧
      (∀ m, M ≤ m → evenDerivSeq χ m < evenDerivSeq χ (m + 1)) := by
  sorry

end OMA.S_arxiv_2611_12152

import Mathlib

/-!
# A010033: The one-sided one-lie Rényi-Ulam game

Source: https://oeis.org/A010033
Credit: @Solfanbtc

`a(n)` (offset 0) is the maximum size of a set `M` such that one can determine a chosen element
`x ∈ M` with at most `n` questions "Is x in T?" (adaptively chosen), when the answer can be a lie
once, but only when the true answer is Yes. Data: `1, 1, 2, 3, 6, 11, 20, 36, 66, 121, ...`.

Conjecture (M. F. Hasler, Jun 26 2026, in the entry): `a(n+1) = 2a(n) - b(n)` with `b = o(a)`,
`b(n) > 0` for all `n ≥ 0` except `b(1) = b(3) = 0`; and `b(n+1) = 2b(n) - c(n)` with `c = o(b)`.
Since `b` and `c` are determined by these equations, they are defined as
`b(n) = 2a(n) - a(n+1)`, `c(n) = 2b(n) - b(n+1)`, and the conjecture is: `b(n) > 0` for
`n ∉ {1, 3}`, `b(1) = b(3) = 0`, `b = o(a)` and `c = o(b)` as `n → ∞`.

The game (`Solvable n S₀ S₁`): the questioner's knowledge is the set `S₀` of candidates for `x`
with the lie still unused, and the set `S₁` of candidates for which the lie has already been used.
`x` is determined when `|S₀ ∪ S₁| ≤ 1`. A question `T` has the answers
* Yes (always truthful, since a lie is only possible when the truth is Yes):
  `(S₀, S₁) ↦ (S₀ ∩ T, S₁ ∩ T)`;
* No (truthful, `x ∉ T`, or a lie, `x ∈ T` with the lie unused):
  `(S₀, S₁) ↦ (S₀ \ T, (S₁ \ T) ∪ (S₀ ∩ T))`.
`Solvable (n+1) S₀ S₁` holds if `x` is already determined or some question leads to solvable
states after both answers. `a(n)` is the largest `m` with `Solvable n {0, ..., m-1} ∅` (the
nature of the elements does not matter, as the entry notes).

A python3 check: this game (by state sizes) gives `a(0), ..., a(10) = 1, 1, 2, 3, 6, 11, 20, 36,
66, 121, 223`, matching the data; from the 35 data terms, `b(n) ≤ 0` only at `n = 1, 3`, and
`b(n)/a(n)` decreases to `0.060` at `n = 32`, `c(n)/b(n)` to `0.089` at `n = 32`.
-/

namespace OMA.S_oeis_a010033

open Asymptotics Filter

/-- `Solvable n S₀ S₁`: the chosen element can be determined with at most `n` more questions. -/
def Solvable : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, S₀, S₁ => (S₀ ∪ S₁).card ≤ 1
  | n + 1, S₀, S₁ => (S₀ ∪ S₁).card ≤ 1 ∨
      ∃ T : Finset ℕ, Solvable n (S₀ ∩ T) (S₁ ∩ T) ∧ Solvable n (S₀ \ T) ((S₁ \ T) ∪ (S₀ ∩ T))

/-- `a n = A010033(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m | Solvable n (Finset.range m) ∅}

/-- `b(n) = 2a(n) - a(n+1)`. -/
noncomputable def b (n : ℕ) : ℤ := 2 * (a n : ℤ) - a (n + 1)

/-- `c(n) = 2b(n) - b(n+1)`. -/
noncomputable def c (n : ℕ) : ℤ := 2 * b n - b (n + 1)

/-- Hasler's conjecture on the second differences of A010033. -/
theorem main :
    (∀ n : ℕ, n ≠ 1 → n ≠ 3 → 0 < b n) ∧ b 1 = 0 ∧ b 3 = 0 ∧
    (fun n => (b n : ℝ)) =o[atTop] (fun n => (a n : ℝ)) ∧
    (fun n => (c n : ℝ)) =o[atTop] (fun n => (b n : ℝ)) := by
  sorry

end OMA.S_oeis_a010033

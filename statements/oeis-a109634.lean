import Mathlib

/-!
# A109634: ones in ternary strings without consecutive 1's, versus A073388

Source: https://oeis.org/A109634 (with https://oeis.org/A073388 and https://oeis.org/A002605)
`a(n)` (offset 0) is the number of 1's that appear among all ternary strings of length `n` that
contain no consecutive 1's: 0, 1, 4, 16, 56, 188, ...
A073388 (offset 0) is the convolution of A002605 with itself, shifted:
`A073388(m) = ∑_{k=0}^{m} b(k) b(m-k)` with `b(k) = A002605(k+1)`, where A002605 is
`u(0) = 0`, `u(1) = 1`, `u(n) = 2u(n-1) + 2u(n-2)`: 1, 4, 16, 56, 188, ...
Conjecture (R. J. Mathar, Aug 18 2008): `a(n) = A073388(n-1)`, for `n ≥ 1` (at `n = 0` the
right side would be `A073388(-1)`, so the range is `n ≥ 1`).

Conventions. A ternary string of length `n` is a map `Fin n → Fin 3`; "no consecutive 1's" means
no `i` with `w i = 1` and `w (i+1) = 1`; the 1's of `w` are counted with multiplicity over all
strings.
Checked: an `#eval` of these definitions gives `a(0..8) = 0, 1, 4, 16, 56, 188, 608, 1920, 5952`
and `A073388(0..7) = 1, 4, 16, 56, 188, 608, 1920, 5952`; python3 confirms the identity for all
26 listed terms.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a109634

/-- The ternary string `w` has no two consecutive 1's. -/
def NoConsecutiveOnes {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = i + 1 → ¬ (w i = 1 ∧ w j = 1)

instance {n : ℕ} : DecidablePred (@NoConsecutiveOnes n) := fun w => by
  unfold NoConsecutiveOnes; infer_instance

/-- A109634: the total number of 1's in the ternary strings of length `n` without
consecutive 1's. -/
def a (n : ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter NoConsecutiveOnes,
    (Finset.univ.filter (fun i => w i = 1)).card

/-- A002605: `u 0 = 0`, `u 1 = 1`, `u (n+2) = 2 u (n+1) + 2 u n`. -/
def u : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * u (n + 1) + 2 * u n

/-- A073388: `∑_{k=0}^{m} u(k+1) u(m-k+1)`. -/
def A073388 (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), u (k + 1) * u (m - k + 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A073388 (n - 1) := by
  sorry

end OMA.S_oeis_a109634

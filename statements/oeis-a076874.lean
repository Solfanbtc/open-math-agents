import Mathlib

/-!
# A076874: a(n) = n - floor((4n+1)^(1/2)).

Source: https://oeis.org/A076874
Credit: @Solfanbtc

A walk of `n` steps on the square lattice is given by its moves `m : Fin n → Fin 4` (directions
`+x, +y, -x, -y`), starting at the origin; `pos m i` is the point after `i` steps. At step `i`
(`i < n`), going from `pos m i`, the walker has `choices m i` options: the neighbours of
`pos m i` not yet visited (`pos m 0, …, pos m i`). A self-avoiding walk is *trapped after `n`
steps* when all four neighbours of `pos m n` have been visited (`choices m n = 0`).
`trapped n` is the finset of these walks. (Their numbers, divided by the 8 lattice symmetries,
are A077482: `1, 2, 11, 25, 95, 228, 752, 1860, 5741, 14477` for `n = 7..16`, checked with
python3.)

A077484(n) (`n ≥ 7`) is the exponent of `2` in the denominator of the reduced fraction
`P(n)`. Here `P(n)` is the probability that the walk that picks each step uniformly among the
unvisited neighbours is trapped after exactly `n` steps, i.e. the sum over trapped walks of
`∏_{i<n} 1/choices m i` (`P(7) = 2/729`, `P(8) = 5/2187`).

Conjecture (from the entry): for `n ≥ 7`,
1. `a(n) - 2` is the maximum, over walks trapped after `n` steps, of the number of steps at which
   the walker had only 2 choices for the next step;
2. `a(n) ≥ A077484(n) + 2`.
Checked with python3 by exhaustive enumeration for `7 ≤ n ≤ 16`: both hold, and the computed
exponents reproduce A077484 (`0, 0, 0, 1, 2, 0, 2, 4, 5, 2`).
-/

namespace OMA.S_oeis_a076874

/-- A076874(n) = n - ⌊√(4n+1)⌋. -/
def a (n : ℕ) : ℕ := n - Nat.sqrt (4 * n + 1)

/-- The four unit steps. -/
def dir : Fin 4 → ℤ × ℤ := ![(1, 0), (0, 1), (-1, 0), (0, -1)]

/-- The point reached after `i` steps of the walk with moves `m`. -/
def pos {n : ℕ} (m : Fin n → Fin 4) (i : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < i), dir (m j)

/-- The points visited after `i` steps: `pos m 0, …, pos m i`. -/
def visited {n : ℕ} (m : Fin n → Fin 4) (i : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (i + 1)).image (pos m)

/-- The number of unvisited neighbours of `pos m i`, i.e. the choices for the next step. -/
def choices {n : ℕ} (m : Fin n → Fin 4) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin 4 => pos m i + dir d ∉ visited m i).card

/-- The walk never revisits a point. -/
def SelfAvoiding {n : ℕ} (m : Fin n → Fin 4) : Prop :=
  ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1), pos m i = pos m j → i = j

instance {n : ℕ} (m : Fin n → Fin 4) : Decidable (SelfAvoiding m) := by
  unfold SelfAvoiding; infer_instance

/-- Self-avoiding walks trapped after `n` steps. -/
def trapped (n : ℕ) : Finset (Fin n → Fin 4) :=
  Finset.univ.filter fun m => SelfAvoiding m ∧ choices m n = 0

/-- The number of steps at which the walker had only 2 choices. -/
def twoCount {n : ℕ} (m : Fin n → Fin 4) : ℕ :=
  ((Finset.range n).filter fun i => choices m i = 2).card

/-- The probability that the myopic random walk is trapped after exactly `n` steps. -/
def P (n : ℕ) : ℚ := ∑ m ∈ trapped n, ∏ i ∈ Finset.range n, (1 / (choices m i : ℚ))

/-- A077484(n): the exponent of 2 in the denominator of `P(n)`. -/
def A077484 (n : ℕ) : ℕ := padicValNat 2 (P n).den

/-- The conjecture of A076874 (both parts), for `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    IsGreatest ((fun m => twoCount m) '' (trapped n : Set (Fin n → Fin 4))) (a n - 2) ∧
    A077484 n + 2 ≤ a n := by
  sorry

end OMA.S_oeis_a076874

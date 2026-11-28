import Mathlib

/-!
# A067589: Numbers k such that A067588(k) is an odd number.

Source: https://oeis.org/A067589 (and https://oeis.org/A067588, https://oeis.org/A000009)
Credit: @Solfanbtc

A067588(k) is the total number of parts in all partitions of `k` into odd parts, and A067589
(offset 1) lists the `k ≥ 1` for which it is odd: 1, 5, 7, 15, 35, 51, 57, 77, 117, ...
(the definitions below reproduce the listed terms of A067588 and A067589, checked in Python).
J. Sellers (2007) proved that the terms are exactly the odd generalized pentagonal numbers.

The entry records two conjectures, both stated here:

1. R. J. Mathar (2009): the g.f. of the sequence is
   `x(x^2+4x+1)(x^4-2x^3+4x^2-2x+1) / ((x^2+1)^2 (1-x)^3)`,
   stated as the identity `(1+x^2)^2 (1-x)^3 · Σ_{n≥1} a(n) x^n = x(x^2+4x+1)(x^4-2x^3+4x^2-2x+1)`
   in `ℤ⟦X⟧`. This follows from Sellers' characterization, so it is a known result; it is
   recorded because the entry states it as a conjecture.

2. P. Bala (2025): for every positive integer `m`, with
   `b_m(n) = Σ_{k=1..n} k^(2m+1) q(k) q(n-k)` where `q = A000009` (partitions into distinct
   parts): (i) for odd `n`, `n ∣ b_m(n)`; (ii) `n ∣ b_m(2n)`, and `b_m(2n)/n` is odd iff `n` is
   a term of this sequence. Here `n` ranges over `n ≥ 1` (the sequence has offset 1 and
   `b_m(n)/n` needs `n ≠ 0`). Checked numerically for `1 ≤ m ≤ 4`, `1 ≤ n ≤ 200`. Open.
-/

namespace OMA.S_oeis_a067589

open PowerSeries

/-- A000009: number of partitions of `n` into distinct parts. -/
def q (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- A067588: total number of parts in all partitions of `n` into odd parts. -/
def A067588 (n : ℕ) : ℕ := ∑ π ∈ Nat.Partition.odds n, π.parts.card

/-- Membership in A067589. -/
def InSeq (k : ℕ) : Prop := 0 < k ∧ Odd (A067588 k)

/-- A067589(n) for `n ≥ 1` (`a 0 = 0` is not a term; it makes the g.f. start at `x^1`). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else Nat.nth InSeq (n - 1)

/-- Bala's `b_m(n)`. -/
def b (m n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, k ^ (2 * m + 1) * q k * q (n - k)

theorem main :
    ((1 + X ^ 2) ^ 2 * (1 - X) ^ 3 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (X ^ 2 + 4 * X + 1) * (X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 2 * X + 1)) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 1 ≤ n →
      (Odd n → n ∣ b m n) ∧ n ∣ b m (2 * n) ∧ (Odd (b m (2 * n) / n) ↔ InSeq n) := by
  sorry

end OMA.S_oeis_a067589

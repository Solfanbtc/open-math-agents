import Mathlib

/-!
# A041017: Denominators of continued fraction convergents to sqrt(12).

Source: https://oeis.org/A041017
Credit: @Solfanbtc

Conjecture (Ralf Stephan, Sep 23 2013, in the entry; also in A227790: "the indices of the maxima
are apparently in A041017"): the terms of A041017 are the values i where A227790(i)/i reaches a
new maximum, A227790(i) being the difference between 3i^2 and the nearest square.

Conventions.
* sqrt(12) = [3; 2, 6, 2, 6, ...]; the convergent denominators are q(-1) = 0, q(0) = 1,
  q(n) = c(n) q(n-1) + q(n-2) with c(n) = 2 for odd n and 6 for even n ≥ 2. `q` below starts
  q 0 = 1, q 1 = 2 and gives 1, 2, 13, 28, 181, 390, 2521, ... (the data, offset 0).
* A227790(i) (i ≥ 1) = min(3i^2 - s^2, (s+1)^2 - 3i^2) with s = floor(sqrt(3 i^2)) (entry
  formula; 3i^2 is never a square for i ≥ 1). "Reaches a new maximum" = strict record over
  1 ≤ j < i, ratios compared in ℚ.
* Stated as an equality of sets: record indices = {q n | n ∈ ℕ}. (python3: the record indices
  below 3·10^6 are exactly 1, 2, 13, 28, 181, 390, 2521, 5432, 35113, 75658, 489061, 1053780.)
-/

namespace OMA.S_oeis_a041017

/-- A041017: denominators of the convergents of sqrt(12) = [3; 2, 6, 2, 6, ...]. -/
def q : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => (if (n + 2) % 2 = 1 then 2 else 6) * q (n + 1) + q n

/-- A227790: distance from 3i^2 to the nearest square. -/
def d (i : ℕ) : ℕ :=
  min (3 * i ^ 2 - Nat.sqrt (3 * i ^ 2) ^ 2) ((Nat.sqrt (3 * i ^ 2) + 1) ^ 2 - 3 * i ^ 2)

/-- i is a record index of A227790(i)/i. -/
def IsRecord (i : ℕ) : Prop :=
  1 ≤ i ∧ ∀ j : ℕ, 1 ≤ j → j < i → (d j : ℚ) / j < (d i : ℚ) / i

theorem main : {i : ℕ | IsRecord i} = Set.range q := by
  sorry

end OMA.S_oeis_a041017

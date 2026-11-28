import Mathlib

/-!
# A091524: multipliers of sqrt(2) from the Graham-Pollak constants

Source: https://oeis.org/A091524 (see A003151, A003152, A028982, A006337)
Credit: @Solfanbtc

A091524 (offset 1): 1, 1, 2, 2, 3, 4, 3, 5, 4, 6, 7, 5, ... (multipliers of `sqrt 2` in constants
attached to the Graham-Pollak recurrence). The entry gives a complete characterization (Benoit
Cloitre, formula section): "Sequence is completely defined by: a(floor(n*(1+sqrt(2))))=n;
a(floor(n*(1+1/sqrt(2))))=n, n>=1 since A003151 and A003152 are Beatty sequences partitioning the
integers"; we use this as the definition: `a(m)` is the unique `n ≥ 1` with
`m = ⌊n(1+√2)⌋` or `m = ⌊n(1+1/√2)⌋`.

A028982 lists the squares and twice squares in increasing order: 1, 2, 4, 8, 9, 16, 18, ...
A006337 is the eta-sequence `⌊(n+1)√2⌋ - ⌊n√2⌋`: 1, 2, 1, 2, 1, 1, 2, ... (offset 1).

Conjecture (Mikhail Kurkov, Apr 25 2024): `a(n) = sqrt(A028982(n) / A006337(n))`.

Sanity check (python, exact integer square roots): the characterization gives all 52 listed terms
(and every `m < 2·10^5` is covered), and the identity holds for `1 ≤ n < 3000`.
-/

namespace OMA.S_oeis_a091524

/-- A091524 via Cloitre's characterization. -/
noncomputable def a (m : ℕ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ (m = ⌊(n : ℝ) * (1 + Real.sqrt 2)⌋₊ ∨
    m = ⌊(n : ℝ) * (1 + 1 / Real.sqrt 2)⌋₊)}

/-- A028982: the `n`-th positive integer that is a square or twice a square. -/
noncomputable def A028982 (n : ℕ) : ℕ :=
  Nat.nth (fun m => 0 < m ∧ ∃ k : ℕ, m = k ^ 2 ∨ m = 2 * k ^ 2) (n - 1)

/-- A006337: `⌊(n+1)√2⌋ - ⌊n√2⌋`. -/
noncomputable def A006337 (n : ℕ) : ℕ :=
  ⌊((n : ℝ) + 1) * Real.sqrt 2⌋₊ - ⌊(n : ℝ) * Real.sqrt 2⌋₊

/-- Kurkov's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℝ) = Real.sqrt ((A028982 n : ℝ) / (A006337 n : ℝ)) := by
  sorry

end OMA.S_oeis_a091524

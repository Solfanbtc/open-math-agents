import Mathlib

/-!
# A025486: Least k with A025485(k) = n.

Source: https://oeis.org/A025486
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Apr 23 2007, in the entry): a(n) = A006892(n+1) + 3 for n >= 3.

Conventions.
* A025485(k): number of iterations of f(k) = ceiling(sqrt(k))^2 - k on k required to force the
  value to be ≤ 2 (0 if k ≤ 2). Below, `iters k = sInf {j | f^[j] k ≤ 2}`; f(k) < k for k ≥ 3,
  so this set is nonempty. Data of A025485: 0,0,0,1,1,2,2,1,1,1,3,...
* A025486(n) (offset 0) = least k with A025485(k) = n: 0, 3, 5, 10, 26, 170, 7226, ...
* A006892(n) (offset 1): the least positive integer whose representation as a sum of squares by
  the greedy algorithm (repeatedly subtract the largest square ≤ the remainder) uses n squares:
  1, 2, 3, 7, 23, 167, 7223, ...
* Checked with python3 (brute force over k < 10^5): both definitions reproduce the data
  above, and a(n) = A006892(n+1) + 3 for n = 3, 4, 5, 6.
-/

namespace OMA.S_oeis_a025486

/-- f(k) = ceiling(sqrt(k))^2 - k. -/
def f (k : ℕ) : ℕ :=
  (if Nat.sqrt k * Nat.sqrt k = k then Nat.sqrt k else Nat.sqrt k + 1) ^ 2 - k

/-- A025485: iterations of `f` needed to reach a value ≤ 2. -/
noncomputable def iters (k : ℕ) : ℕ := sInf {j : ℕ | f^[j] k ≤ 2}

/-- A025486: least k with A025485(k) = n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | iters k = n}

/-- Number of squares used by the greedy algorithm. -/
def greedy (m : ℕ) : ℕ :=
  if h : m = 0 then 0 else 1 + greedy (m - Nat.sqrt m ^ 2)
decreasing_by
  have : 0 < Nat.sqrt m := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero h)
  have : Nat.sqrt m ^ 2 ≤ m := by rw [sq]; exact Nat.sqrt_le m
  have : 0 < Nat.sqrt m ^ 2 := by positivity
  omega

/-- A006892: least positive integer needing n squares in the greedy algorithm. -/
noncomputable def A006892 (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ greedy m = n}

theorem main : ∀ n : ℕ, 3 ≤ n → a n = A006892 (n + 1) + 3 := by
  sorry

end OMA.S_oeis_a025486

import Mathlib

/-!
# A140100: Start with Y(0)=0, X(1)=1, Y(1)=2. For n > 1, choose least positive integers Y(n) > X(n) such that neither Y(n) nor X(n) appear in {Y(k), 1 <= k < n} or {X(k), 1 <= k < n} and such that Y(n) - X(n) does not appear in {Y(k) - X(k), 1 <= k < n} or {Y(k) + X(k), 1 <= k < n}; sequence gives X(n) (for Y(n) see A140101).

Source: https://oeis.org/A140100
Credit: @Solfanbtc

Conjectures recorded in the entry (t = tribonacci constant, the real root of t^3 = t^2 + t + 1,
t = 1.83928675521...):
1. A140100(n) - A140098(n) is always 0 or 1, where A140098(n) = floor(n (1 + 1/t)).
2. X(n)/n -> 1 + 1/t, Y(n)/n -> 1 + t, Y(n)/X(n) -> t, hence
   (Y(n) + X(n))/(Y(n) - X(n)) -> t^2 and (Y(n)^2 + X(n)^2)/(Y(n)^2 - X(n)^2) -> t.
3. (J. Cassaigne; verified with Walnut by Jeffrey Shallit, Oct 04 2022, so now a theorem) for all
   n >= 1, X(Y(n)) = X(n) + Y(n) or Y(X(n)) = X(n) + Y(n).
`main` states all of them.

Definition of X, Y (from the name): X(1) = 1, Y(1) = 2; for n > 1, X(n) is the least positive
integer not among X(k), Y(k) (1 <= k < n), and Y(n) is the least integer > X(n) not among them with
Y(n) - X(n) not among the earlier differences Y(k) - X(k) and sums Y(k) + X(k). ("Least positive
integers Y(n) > X(n)" is read lexicographically, X first, as in the example and the queens
construction; a valid Y always exists.) The example also requires Y + X to be new; with or without
that extra condition the sequences coincide for n <= 20000, so the name is followed. `main`
quantifies over all X, Y satisfying this specification (exactly one pair does).
Checked numerically for n <= 20000: the listed terms of A140100 and A140101 are reproduced, the
difference in 1 is always 0 or 1, and X(n)/n = 1.54365, Y(n)/n = 2.83925 at n = 20000.
-/

namespace OMA.S_oeis_a140100

open Filter

/-- The greedy specification of the name. -/
def Spec (X Y : ℕ → ℕ) : Prop :=
  Y 0 = 0 ∧ X 1 = 1 ∧ Y 1 = 2 ∧
  ∀ n : ℕ, 2 ≤ n →
    IsLeast {x : ℕ | 0 < x ∧ ∀ k, 1 ≤ k → k < n → x ≠ X k ∧ x ≠ Y k} (X n) ∧
    IsLeast {y : ℕ | X n < y ∧ (∀ k, 1 ≤ k → k < n → y ≠ X k ∧ y ≠ Y k) ∧
      ∀ k, 1 ≤ k → k < n →
        (y : ℤ) - X n ≠ (Y k : ℤ) - X k ∧ (y : ℤ) - X n ≠ (Y k : ℤ) + X k} (Y n)

theorem main : ∀ X Y : ℕ → ℕ, Spec X Y → ∀ t : ℝ, 1 < t → t ^ 3 = t ^ 2 + t + 1 →
    (∀ n : ℕ, 1 ≤ n → (X n : ℤ) - ⌊(n : ℝ) * (1 + 1 / t)⌋ ∈ ({0, 1} : Set ℤ)) ∧
    Tendsto (fun n : ℕ => (X n : ℝ) / n) atTop (nhds (1 + 1 / t)) ∧
    Tendsto (fun n : ℕ => (Y n : ℝ) / n) atTop (nhds (1 + t)) ∧
    Tendsto (fun n : ℕ => (Y n : ℝ) / X n) atTop (nhds t) ∧
    Tendsto (fun n : ℕ => ((Y n : ℝ) + X n) / ((Y n : ℝ) - X n)) atTop (nhds (t ^ 2)) ∧
    Tendsto (fun n : ℕ => ((Y n : ℝ) ^ 2 + (X n : ℝ) ^ 2) / ((Y n : ℝ) ^ 2 - (X n : ℝ) ^ 2))
      atTop (nhds t) ∧
    (∀ n : ℕ, 1 ≤ n → X (Y n) = X n + Y n ∨ Y (X n) = X n + Y n) := by
  sorry

end OMA.S_oeis_a140100

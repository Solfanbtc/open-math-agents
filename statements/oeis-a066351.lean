import Mathlib

/-!
# A066351: Bisection of A007059.

Source: https://oeis.org/A066351
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Aug 25 2014, in the entry): a(n) ~ 0.721... * 4^n / n.

Conventions.
* a(n) = A007059(2n+1) (offset 0): the data 1, 2, 5, 14, 43, 140, ... are the odd-indexed terms
  of A007059 = 0, 1, 1, 2, 3, 5, 8, 14, 24, 43, 77, 140, ...
* A007059(n) (number of balanced ordered trees with n nodes) is used in Joerg Arndt's
  equivalent form from that entry: for n ≥ 1, the number of compositions of n in which all
  parts are smaller than the first part (lists of positive integers with sum n whose tail
  entries are all < the head). python3: this gives 0, 1, 1, 2, 3, 5, 8, 14, 24, 43, 77, 140,
  256, 472, ... (A007059's data; the empty composition is excluded, so A007059(0) = 0).
* "~ 0.721... · 4^n/n" is stated as: a(n) n / 4^n converges to a limit L whose decimal
  expansion begins 0.721, i.e. 0.721 ≤ L < 0.722. (python3: 0.71742, 0.71937, 0.72036, 0.72067
  for n = 50, 100, 200, 300, increasing slowly.)
-/

namespace OMA.S_oeis_a066351

/-- A007059(n): compositions of n in which all parts after the first are smaller than it. -/
noncomputable def A007059 (n : ℕ) : ℕ :=
  Nat.card {l : List ℕ // l ≠ [] ∧ (∀ x ∈ l, 0 < x) ∧ l.sum = n ∧ ∀ x ∈ l.tail, x < l.headD 0}

/-- A066351: a(n) = A007059(2n+1). -/
noncomputable def a (n : ℕ) : ℕ := A007059 (2 * n + 1)

theorem main : ∃ L : ℝ,
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) * n / 4 ^ n) Filter.atTop (nhds L) ∧
      0.721 ≤ L ∧ L < 0.722 := by
  sorry

end OMA.S_oeis_a066351

import Mathlib

/-!
# A123929: Simili-primes of order 2.

Source: https://oeis.org/A123929
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, Feb 11 2007): a(n) is asymptotic to c*n*log(n) with c about 1.5.

Definition (entry comment and M. F. Hasler's PARI program): a(1) = 3 and a(n+1) is the second
integer greater than a(n) that is divisible by none of a(1), ..., a(n). This reproduces all 57
data terms 3, 5, 8, 13, 17, 22, ... (python3).

Formalization of the conjecture: there is a constant c > 0 with a(n) / (n log n) → c. The value
"about 1.5" is an informal numerical estimate and is not part of the statement (python3:
a(n)/(n log n) is 1.41 at n = 1000, 1.34 at n = 5000, 1.29 at n = 20000).
-/

namespace OMA.S_oeis_a123929

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [3]
  | (n + 2) =>
    let L := terms (n + 1)
    L ++ [Nat.nth (fun m => L.getLastD 0 < m ∧ ∀ x ∈ L, ¬ x ∣ m) 1]

/-- A123929(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n * Real.log n)) Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a123929

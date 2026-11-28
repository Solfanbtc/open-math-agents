import Mathlib

/-!
# A114726: Fixed points of permutation A114650.

Source: https://oeis.org/A114726
Credit: @Solfanbtc

Conjecture (entry comment, Klaus Brockhaus): the sequence is infinite and
lim_{n -> infinity} a(n+1)/a(n) = e = 2.718281828...

Definitions.
* A114650 (offset 1): a(1) = 1; for n > 1, a(n) is the smallest positive integer not among the
  earlier terms with floor(log a(n)) ≠ floor(log a(n-1)), log the natural logarithm
  (as in the example of A114650: floor(log 11) = 2, so a(12) = 21, the least m with
  floor(log m) = 3).
* A114726 lists the fixed points n (a(n) = n) in increasing order; `fix k` is the k-th one
  (offset 1). python3 reproduces the 14 data terms 1, 4, 11, 30, ..., 646864 (next: 1758345).
* Statement: there are infinitely many fixed points, and fix(k+1)/fix(k) → e.
-/

namespace OMA.S_oeis_a114726

/-- `terms n = [A114650(1), ..., A114650(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) =>
    let L := terms (n + 1)
    L ++ [sInf {m : ℕ | 0 < m ∧ m ∉ L ∧
      ⌊Real.log (m : ℝ)⌋ ≠ ⌊Real.log ((L.getLastD 1 : ℕ) : ℝ)⌋}]

/-- A114650(n). -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- `n ≥ 1` is a fixed point of A114650. -/
def IsFixed (n : ℕ) : Prop := 1 ≤ n ∧ a n = n

/-- A114726(k), offset 1. -/
noncomputable def fix (k : ℕ) : ℕ := Nat.nth IsFixed (k - 1)

theorem main :
    {n : ℕ | IsFixed n}.Infinite ∧
      Filter.Tendsto (fun k : ℕ => (fix (k + 1) : ℝ) / fix k) Filter.atTop
        (nhds (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a114726

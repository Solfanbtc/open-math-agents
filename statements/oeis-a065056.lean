import Mathlib

/-!
# A065056: Partial sums of Recamán's sequence A005132.

Source: https://oeis.org/A065056
Credit: @Solfanbtc

Conjecture (in the entry): lim_{n -> oo} a(n)/n^2 exists and is about 0.8...

Conventions.
* Recamán's sequence A005132: R(0) = 0; R(n) = R(n-1) - n if that is positive and not already
  in the sequence, otherwise R(n) = R(n-1) + n. `recList n` is the list R(n), R(n-1), ..., R(0)
  (most recent first), so the "not already in the sequence" test is membership in it.
* a(n) = R(0) + ... + R(n) (offset 0), the sum of `recList n`.
* "Is about 0.8..." is read as: the limit L exists and its decimal expansion starts 0.8, i.e.
  0.8 ≤ L < 0.9. (python3: a(n)/n^2 = 0.826, 0.864, 0.868, 0.846, 0.859 for n = 10^4, 10^5,
  10^6, 3·10^6, 10^7; the convergence is slow and oscillating.)
-/

namespace OMA.S_oeis_a065056

/-- R(n), R(n-1), ..., R(0) for Recamán's sequence. -/
def recList : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let L := recList n
    let r := L.headD 0
    (if n + 1 < r ∧ r - (n + 1) ∉ L then r - (n + 1) else r + (n + 1)) :: L

/-- A065056: partial sums of Recamán's sequence. -/
def a (n : ℕ) : ℕ := (recList n).sum

theorem main : ∃ L : ℝ,
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds L) ∧
      0.8 ≤ L ∧ L < 0.9 := by
  sorry

end OMA.S_oeis_a065056

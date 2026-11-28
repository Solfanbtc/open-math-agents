import Mathlib

/-!
# A084761: A sequence of primes such that (a(n)-a(n-1)) / (a(n-1)-a(n-2)) is a unique integer.

Source: https://oeis.org/A084761
Credit: @Solfanbtc

Offset 1. `a(1) = 2`, `a(2) = 3`, and for `n ≥ 3`, `a(n)` is the smallest prime `> a(n-1)`
such that `r = (a(n) - a(n-1)) / (a(n-1) - a(n-2))` is an integer not obtained as such a ratio
before. Since `a(n-1) - a(n-2) > 0`, this is `a(n) = a(n-1) + r (a(n-1) - a(n-2))` with `r` the
least positive integer, not used before, making this number prime. This greedy rule is the one
implied by the name and the example; we checked by computer that it reproduces all 24 terms of
%S, %T, %U, with ratios 2, 1, 3, 4, 5, 6, 8, 7, 12, ... as in the entry's comment.
(Such an `r` always exists by Dirichlet's theorem, as `a(n-1)` and `a(n-1) - a(n-2)` are
coprime; `sInf ∅ = 0` is never used.)

Conjecture (Murthy and Srikanth, 2003): every positive integer `r` occurs as a ratio, i.e.
for every `r ≥ 1` there is `k ≥ 3` with `(a(k) - a(k-1)) / (a(k-1) - a(k-2)) = r`.
-/

namespace OMA.S_oeis_a084761

/-- One step: from `(a(n-2), a(n-1), ratios used)` to `(a(n-1), a(n), ratios used)`. -/
noncomputable def step (s : ℕ × ℕ × Finset ℕ) : ℕ × ℕ × Finset ℕ :=
  let r := sInf {r : ℕ | 1 ≤ r ∧ r ∉ s.2.2 ∧ (s.2.1 + r * (s.2.1 - s.1)).Prime}
  (s.2.1, s.2.1 + r * (s.2.1 - s.1), insert r s.2.2)

/-- `a(n)`, offset 1 (`a 0` is an unused placeholder). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (step^[n] (2, 3, ∅)).1

/-- Every positive integer occurs as a ratio of successive differences. -/
theorem main : ∀ r : ℕ, 1 ≤ r → ∃ k : ℕ, 3 ≤ k ∧
    ((a k : ℤ) - a (k - 1)) = (r : ℤ) * ((a (k - 1) : ℤ) - a (k - 2)) := by
  sorry

end OMA.S_oeis_a084761

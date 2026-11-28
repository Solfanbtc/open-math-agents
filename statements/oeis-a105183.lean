import Mathlib

/-!
# A105183: a(n) = 1 + a(n-1)*(a(n-1) + 1), with a(0)=2.

Source: https://oeis.org/A105183
Credit: @Solfanbtc

Conjecture (Gerald McGarvey, Dec 12 2007): "a(n) is asymptotic to d - 1/2 -(5/2^3)/d
-(65/2^7)/d^3 -(650/2^11)/d^5 -(19045/2^15)/d^7 -(274950/2^19)/d^9 -(6979050/2^23)/d^11
-(130292500/2^27)/d^13 ... where d = c^(2^n) and c is a constant =
1.288203192684485177845610784851700404829443712770079185959554466777577486352420255603915828361833141546...."
(The other formula of the same comment, a(n) = Sum_{k<n} a(k)^2 + n + 2, is elementary and is
not part of this statement.)

Index fix (needed, explained). With a(0) = 2 (offset 0, as in the entry) the expansion holds
with `d = c^(2^(n+2))`, not `c^(2^n)`: python3 (400-digit arithmetic) gives
`(a(11) + 1/2)^(1/2^11) = 2.7538322695... = c^4`, whose fourth root agrees with all 102 listed
decimals of `c`, and with `d = c^(2^(n+2))` the error of the expansion truncated after the
listed terms is about -1.655 / d^15 for n = 2, 3, 4, 5. Read literally (`d = c^(2^n)`), the
claim fails already in its leading term (a(n) / c^(2^n) → ∞), so the exponent was written for a
shifted index; we state the conjecture with the shift that makes it hold.

Formalization of "asymptotic to" an expansion given by its first terms: with `d = c^(2^(n+2))`,
the difference between a(n) and the displayed expansion (all listed terms) is `o(1/d^13)`,
i.e. `(a(n) - E(d)) * d^13 → 0`; this contains every shorter truncation. The constant is known
from its 102 listed decimals (followed by "...", so the precision is stated as
`|c - 1.288...546| < 10^(-102)`).
-/

namespace OMA.S_oeis_a105183

/-- A105183. -/
def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => 1 + a n * (a n + 1)

/-- The displayed expansion as a function of `d`. -/
noncomputable def E (d : ℝ) : ℝ :=
  d - 1 / 2 - (5 / 2 ^ 3) / d - (65 / 2 ^ 7) / d ^ 3 - (650 / 2 ^ 11) / d ^ 5
    - (19045 / 2 ^ 15) / d ^ 7 - (274950 / 2 ^ 19) / d ^ 9 - (6979050 / 2 ^ 23) / d ^ 11
    - (130292500 / 2 ^ 27) / d ^ 13

theorem main :
    ∃ c : ℝ,
      |c - 1.288203192684485177845610784851700404829443712770079185959554466777577486352420255603915828361833141546| <
        (10 : ℝ) ^ (-102 : ℤ) ∧
      Filter.Tendsto
        (fun n : ℕ => ((a n : ℝ) - E (c ^ (2 ^ (n + 2)))) * (c ^ (2 ^ (n + 2))) ^ 13)
        Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a105183

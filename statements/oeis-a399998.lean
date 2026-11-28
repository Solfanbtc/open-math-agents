import Mathlib

/-!
# A399998: a(n+1) = a(n - a(a(n))^2) + 1, a(0) = 0, and a(n) ~ 2^(1/4) n^(1/2)

Source: https://oeis.org/A399998
Credit: @Solfanbtc

A399998 (R. Cestnik): `a(0) = 0`, `a(n+1) = a(n - a(a(n))^2) + 1`. Data 0, 1, 1, 2, 2, 3, 2, 4, …

Conjecture (in the entry, %F): `a(n) ~ 2^(1/4) * n^(1/2)`, i.e.
`a(n) / (2^(1/4) sqrt(n)) → 1`. (The entry supports it by a continuum approximation; it is
not proved.)

Definition. The recursion refers to the earlier terms `a(a(n))` and `a(n - a(a(n))^2)`; we build
the list of the terms `a(0), …, a(n)` step by step and read terms with `List.getD`. The
sequence is well defined (every index used is `≤ n`), checked with python3 for `n < 4·10^5`;
so the default value of `getD` and the truncated subtraction in `ℕ` are never used along the
genuine sequence (if an index ever left the range, the source sequence itself would not be
defined). The python3 check also reproduces the data, and the ratio is about 0.997 at
`n = 4·10^5`.
-/

namespace OMA.S_oeis_a399998

/-- `terms n = [a(0), …, a(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := terms n
    l ++ [l.getD (n - (l.getD (l.getD n 0) 0) ^ 2) 0 + 1]

/-- A399998: `a(n)`. -/
def a (n : ℕ) : ℕ := (terms n).getD n 0

open Filter Topology in
/-- Conjecture: `a(n) ~ 2^(1/4) n^(1/2)`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a399998

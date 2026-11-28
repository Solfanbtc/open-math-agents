import Mathlib

/-!
# A095769: a(1)=a(2)=1; a(n)=a(a(a(a(n-1))))+a(n-a(a(a(n-1)))).

Source: https://oeis.org/A095769
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, OEIS A095769, %F line):
`lim_{n → ∞} a(n)/n = 0.682327803828...`, the real positive root of `x^3 + x = 1`.

Formalization.
* `aList n = [a 0, a 1, ..., a n]` with a placeholder `a 0 = 0`; the recursion reads earlier
  list entries. All indices read are genuine earlier terms: by induction `1 ≤ a(k) ≤ k` for
  `k ≥ 1` (if `y = a(a(a(n-1)))` then `1 ≤ y ≤ n - 1`, so `1 ≤ n - y ≤ n - 1`, and
  `a(n) = a(y) + a(n - y) ≤ y + (n - y) = n`), so neither the placeholder nor the
  out-of-range default `0` of `getD` is ever used for `n ≥ 1`.
* `x^3 + x - 1` is strictly increasing on `ℝ`, so it has exactly one real root, which is
  positive; the statement asks for that root `c` and `a(n)/n → c`.

Checked with python3 and `#eval`: the definition reproduces all listed %S/%T/%U terms
(1, 1, 2, 3, 4, 4, 5, ..., 51, 52).
-/

namespace OMA.S_oeis_a095769

open Filter Topology

/-- `[a 0, a 1, ..., a n]` with the placeholder `a 0 = 0`. -/
def aList : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | n + 3 =>
      let l := aList (n + 2)
      let g := fun i => l.getD i 0
      l ++ [g (g (g (g (n + 2)))) + g (n + 3 - g (g (g (n + 2))))]

/-- A095769 (offset 1). -/
def a (n : ℕ) : ℕ := (aList n).getD n 0

/-- `a(n)/n` tends to the real root of `x^3 + x = 1`. -/
theorem main : ∃ c : ℝ, 0 < c ∧ c ^ 3 + c = 1 ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a095769

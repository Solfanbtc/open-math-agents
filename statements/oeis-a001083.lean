import Mathlib

/-!
# A001083: lengths of the Kolakoski growth stages grow like c (3/2)^n with c = 0.5819…

Source: https://oeis.org/A001083
Credit: @Solfanbtc

A001083 (offset 1): the length of one version of the Kolakoski sequence at the `n`-th growth
stage. Following the entry's PARI program: start with the word `[2]`; from a word `v`, the next
word lists, for `i = 1, 2, …`, `v(i)` copies of the letter `1` if `i` is odd and `2` if `i` is
even (`next1`). The stages are `2 -> 11 -> 12 -> 122 -> 12211 -> 1221121 -> …`, and `a(n)` is
the length of the `n`-th one, `a(1) = 1`. Data 1, 2, 2, 3, 5, 7, 10, 15, 23, …

Conjecture (B. Cloitre, Jun 01 2004): "a(n) is asymptotic to c*(3/2)^n where c=0.5819....".
`main` states: there is a constant `c` with `0.5819 ≤ c < 0.5820` (the decimal digits given)
such that `a(n)/(3/2)^n → c`; then `a(n) ~ c (3/2)^n` since `c > 0`.

Checked with python3: the construction reproduces the 38 listed terms, and
`a(n)/(3/2)^n = 0.58190, 0.58196, 0.58195` at `n = 30, 38, 44`.
-/

namespace OMA.S_oeis_a001083

/-- One growth step: the `i`-th letter (from 0) of `v` gives `v[i]` copies of `1` (`i` even) or
`2` (`i` odd). -/
def next1 (v : List ℕ) : List ℕ :=
  (List.range v.length).flatMap fun i =>
    List.replicate (v.getD i 0) (if i % 2 = 0 then 1 else 2)

/-- A001083: the length of the `n`-th growth stage, starting from `[2]` at `n = 1`. -/
def a (n : ℕ) : ℕ := ((next1)^[n - 1] [2]).length

open Filter Topology in
/-- Cloitre's conjecture: `a(n) ~ c (3/2)^n` with `c = 0.5819…`. -/
theorem main : ∃ c : ℝ, 0.5819 ≤ c ∧ c < 0.5820 ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / (3 / 2 : ℝ) ^ n) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a001083

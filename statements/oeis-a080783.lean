import Mathlib

/-!
# A080783: a(1)=1, a(n)=a(n-1)-1 if n is already in the sequence, a(n)=a(n-1)+5 otherwise.

Source: https://oeis.org/A080783
Credit: @Solfanbtc

Conjecture (OEIS A080783): a(n) is asymptotic to 3n as n → ∞, i.e. a(n)/n → 3.

Definition (offset 1): a(1) = 1; for n >= 2, a(n) = a(n-1) - 1 if n is among a(1), ..., a(n-1),
and a(n) = a(n-1) + 5 otherwise ("already in the sequence" read as: among the earlier terms;
this reading reproduces the data 1, 6, 11, 16, 21, 20, 25, ...). The values are computed with a
list of the earlier terms (`prefixList n` = [a(1), ..., a(n)]); `a 0` is a junk value.
Numerical note: a(n)/n = 3.0857, 3.0827, 3.0823 at n = 10^5, 10^6, 10^7, so the limit, if it
exists, looks slightly larger than 3; the statement is the one recorded in the entry.
-/

namespace OMA.S_oeis_a080783

open Filter

/-- The list [a(1), ..., a(n)] (for n ≥ 1; `prefixList 0 = []`). -/
def prefixList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 1 =>
    let l := prefixList n
    let x := l.getLastD 0
    l ++ [if n + 1 ∈ l then x - 1 else x + 5]

/-- a(n), for n ≥ 1. -/
def a (n : ℕ) : ℕ := (prefixList n).getLastD 0

theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds 3) := by
  sorry

end OMA.S_oeis_a080783

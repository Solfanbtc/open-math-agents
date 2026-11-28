import Mathlib

/-!
# A065941: Adamson's "r-t table" (doubling mod N) and A003558

Source: https://oeis.org/A065941
Credit: @Solfanbtc

Conjecture (Gary W. Adamson, Aug 25 2019, in A065941): for odd N, build the first row of the
"r-t table" by starting from 1 and repeatedly doubling mod N, each time choosing, between the two
representatives 2x mod N and -(2x) mod N, the smaller in absolute value (e.g. for N = 11 after
4 come 8 and -3, and 3 is chosen); the row ends when the trajectory produces a term already used.
Then the number of terms in the first row equals A003558 corresponding to N, i.e.
A003558(n) with N = 2n + 1, where A003558(n) = least m > 0 such that 2^m ≡ ±1 (mod 2n+1).
(Entry examples: N = 11 gives (1, 2, 4, 3, 5), 5 terms; N = 13 gives (1, 2, 4, 5, 3, 6);
N = 15 gives (1, 2, 4, 7).)

Conventions.
* The step is g(x) = min(2x mod N, N - (2x mod N)) (the absolute value of the representative
  of smaller absolute value). The row is 1, g(1), g(g(1)), ..., stopping before the first
  repeated term, so its length is the least m ≥ 1 with g^[m](1) ∈ {g^[j](1) : j < m}.
* The table in the entry starts at N = 3, so the statement is for N = 2n + 1 with n ≥ 1.
  (python3: the row lengths agree with A003558(n) for 1 ≤ n < 3000, and the rows for
  N = 3..15 agree with the entry's table.)
-/

namespace OMA.S_oeis_a065941

/-- The doubling step mod N, reduced to the representative of smaller absolute value. -/
def g (N x : ℕ) : ℕ := min (2 * x % N) (N - 2 * x % N)

/-- Length of the first row of the r-t table for N. -/
noncomputable def rowLength (N : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∃ j < m, (g N)^[m] 1 = (g N)^[j] 1}

/-- A003558(n): least m > 0 with 2^m ≡ ±1 (mod 2n+1). -/
noncomputable def A003558 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (2 ^ m ≡ 1 [MOD 2 * n + 1] ∨ 2 ^ m + 1 ≡ 0 [MOD 2 * n + 1])}

theorem main : ∀ n : ℕ, 1 ≤ n → rowLength (2 * n + 1) = A003558 n := by
  sorry

end OMA.S_oeis_a065941

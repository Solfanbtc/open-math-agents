import Mathlib

/-!
# A056636: Conjecturally largest even integer which is the sum of two primes in at most n ways.

Source: https://oeis.org/A056636
Credit: @Solfanbtc

Conjecture (OEIS A056636, %N, Brian Galebach): for each n, the listed a(n) is the largest even
integer which is the sum of two primes in at most n ways. `main` states this for every listed
term, n = 0..45 (%S, %T, %U). The case n = 0 (a(0) = 2: every even number ≥ 4 is a sum of
two primes in at least one way) is Goldbach's conjecture, so this is a strengthening of it.

Conventions:
* Ways are unordered: `r m` = #{p ≤ m/2 : p and m - p prime} (A045917 at m/2); the example of
  the entry counts 12 = 5 + 7 as the only way, so a(1) = 12.
* "largest even integer with at most n ways" is `IsGreatest {m | Even m ∧ r m ≤ n} (a n)`,
  which also asserts that the set is bounded above.
* Checked in Python: for m ≤ 4·10^6, the largest even m with r(m) ≤ n is the listed a(n) for
  each n = 0..45 (also a(n) = max of A000954(0..n), per %F).
-/

namespace OMA.S_oeis_a056636

/-- Number of ways to write `m` as `p + q` with `p ≤ q` primes. -/
def r (m : ℕ) : ℕ :=
  ((Finset.range (m / 2 + 1)).filter fun p => p.Prime ∧ (m - p).Prime).card

/-- The listed terms a(0), ..., a(45). -/
def terms : List ℕ :=
  [2, 12, 68, 128, 152, 188, 332, 398, 398, 488, 632, 692, 692, 992, 992, 992, 1112, 1112,
    1412, 1412, 1448, 1718, 1718, 1718, 1718, 2048, 2252, 2252, 2672, 2672, 2672, 2936, 2936,
    2936, 2978, 3092, 3092, 3218, 3272, 3296, 3632, 3632, 3754, 4022, 4058, 4412]

/-- Each listed `a(n)` is the largest even integer that is a sum of two primes in at most `n`
ways. -/
theorem main :
    ∀ n (hn : n < terms.length),
      IsGreatest {m : ℕ | Even m ∧ r m ≤ n} (terms.get ⟨n, hn⟩) := by
  sorry

end OMA.S_oeis_a056636

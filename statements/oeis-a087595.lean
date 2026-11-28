import Mathlib

/-!
# A087595: Smallest n-digit member of A087593

Source: https://oeis.org/A087595
Credit: @Solfanbtc

`dd(k)` is the number formed by concatenating the absolute differences of successive (decimal)
digits of `k` (read as a number, so leading zeros are dropped: `dd(101) = 11`, `dd(113) = 02 = 2`,
`dd(10009) = 1009`). A087593: primes `p` with `dd(p)` prime: `13, 29, 31, 41, …`. A087595
(offset 2): the smallest `n`-digit member of A087593: `13, 101, 1009, 10009, 100363, 1000003, …`
(this definition reproduces both data lists checked).

Conjecture (OEIS comment): the sequence is infinite. Each digit length has finitely many members of
A087593, so A087595 is infinite iff A087593 is infinite (the conjecture also recorded in A087593);
it is stated as: there are infinitely many primes `p` with `dd(p)` prime.
-/

namespace OMA.S_oeis_a087595

/-- `dd(k)`: the number whose digits are the absolute differences of successive digits of `k`
(`Nat.digits` is least significant first; the differences keep that order). -/
def dd (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.zipWith (fun x y => if x ≤ y then y - x else x - y)
    (Nat.digits 10 k) (Nat.digits 10 k).tail)

/-- There are infinitely many primes `p` with `dd(p)` prime (so A087595 is infinite). -/
theorem main : {p : ℕ | p.Prime ∧ (dd p).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a087595

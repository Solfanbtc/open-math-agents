import Mathlib

/-!
# A095258: a(n+1) is the smallest divisor of (2 + sum of first n terms) but not occurring earlier; a(1) = 1.

Source: https://oeis.org/A095258
Credit: @Solfanbtc

Conjecture (Reinhard Zumkeller, revised Dec 31 2014): the sequence is an integer permutation
with inverse A095259: a(A095259(n)) = A095259(a(n)) = n.

A095259(n) is defined in its entry as the smallest m with A095258(m) = n, so the inverse
relation holds by definition as soon as A095258 is a permutation of the positive integers.
The content of the conjecture is therefore: the construction never gets stuck (every
2 + a(1) + ... + a(n) has a divisor not yet used) and every positive integer occurs.
Injectivity holds by construction; we state the full bijectivity.

Formalization.
* `terms n = [a(1), ..., a(n)]`; the next term is the least `d > 0` with `d ∣ s`,
  `s = 2 + a(1) + ... + a(n)`, `d` not among the previous terms (all such `d` are `≤ s`, so
  searching `d < s + 1` is complete). If no such `d` existed, the term would be `0`, which is
  excluded by the conjecture since `0` is not a positive integer.
* `a n` (offset 1) is the `n`-th term; `main` says that `a` maps `{n | 1 ≤ n}` bijectively
  onto `{m | 1 ≤ m}`.
* The definition reproduces the 67 data terms 1, 3, 2, 4, 6, 9, 27, 18, ... (`#eval`).
-/

namespace OMA.S_oeis_a095258

/-- `terms n = [a(1), ..., a(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) =>
    let L := terms (n + 1)
    let s := 2 + L.sum
    L ++ [((List.range (s + 1)).filter (fun d => 0 < d ∧ d ∣ s ∧ d ∉ L)).headD 0]

/-- A095258(n), offset 1. -/
def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main : Set.BijOn a {n : ℕ | 1 ≤ n} {m : ℕ | 1 ≤ m} := by
  sorry

end OMA.S_oeis_a095258

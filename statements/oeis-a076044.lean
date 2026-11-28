import Mathlib

/-!
# A076044: Largest a(n) values with at most n primes between a(n) and a(n)+sqrt(a(n)) inclusive.

Source: https://oeis.org/A076044
Credit: @Solfanbtc

`count(m)` is the number of primes `p` with `m ≤ p ≤ m + ⌊√m⌋` (inclusive; the example uses
`int(2558 + sqrt 2558) = 2608`). `a(n)` (offset `0`) is the largest `m` with `count(m) ≤ n`.

Conjecture (in the entry): "for every m greater than a(n), there are more than n primes between m
and m+sqrt(m)", with the listed values of `a(n)`. The terms are only verified numerically, so the
claim is that the data `a(0), …, a(48)` are correct: for each listed `n`, `count(a(n)) ≤ n`, and
`count(m) > n` for every `m > a(n)`. (Checked in Python for every `m` below `8·10^6`: the last
`m` with `count(m) ≤ n` is the listed `a(n)` for each `n ≤ 48`.)
-/

namespace OMA.S_oeis_a076044

/-- The number of primes in `[m, m + ⌊√m⌋]`. -/
def count (m : ℕ) : ℕ := ((Finset.Icc m (m + Nat.sqrt m)).filter Nat.Prime).card

/-- The listed terms `a(0), …, a(48)`. -/
def a : Fin 49 → ℕ :=
  ![116, 1330, 2481, 2558, 5929, 7371, 9961, 10743, 23378, 35608, 35612, 38361,
    44286, 46902, 69503, 69545, 88024, 107359, 110087, 110099, 113386, 126860,
    250172, 250180, 250186, 250202, 267969, 267975, 285846, 285858, 302013, 302017, 360346,
    369213, 404562, 404574, 484650, 484654, 514893, 561443, 561481, 561509, 561533, 638194,
    638208, 650020, 682490, 713634, 713636]

theorem main : ∀ n : Fin 49,
    count (a n) ≤ (n : ℕ) ∧ ∀ m : ℕ, a n < m → (n : ℕ) < count m := by
  sorry

end OMA.S_oeis_a076044

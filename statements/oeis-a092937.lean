import Mathlib

/-!
# A092937: Most common value of nextprime(2*k)-prevprime(2*k) = A060267(k) for 4 <= 2*k <= 10^n.

Source: https://oeis.org/A092937
Credit: @Solfanbtc

For an even `m ≥ 4`, `g(m) = nextprime(m) - prevprime(m)` (least prime `> m` minus largest prime
`< m`; this is A060267). `a(n)` (offset 1) is the most common value of `g(2k)` for
`4 ≤ 2k ≤ 10^n`, the smallest one in case of ties (comment of P. von Brömssen):
`2, 6, 6, 6, 6, 12, 18, 18, 30, 30, 30` (the first six checked by computer).

The entry's conjecture (Cino Hilliard): *The maximum density occurs at increasing multiples of 6
as the number of primes tested approaches infinity.* Its given example, that the most
common difference for `2k ≤ 10^10` is 30 or higher, is a single finite case (`a(10) = 30`).
The data (6, 6, 6, 6) shows that "increasing" does not mean strictly increasing at each step.
The statement takes the asymptotic claim to mean: from some `n` on, every `a(n)` is a multiple
of 6, and `a(n) → ∞`.
-/

namespace OMA.S_oeis_a092937

/-- The least prime greater than `m`. -/
def nextPrime (m : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (m + 1))

/-- The largest prime less than `m` (for `m ≥ 3`). -/
def prevPrime (m : ℕ) : ℕ := Nat.findGreatest Nat.Prime (m - 1)

/-- `g(m) = nextprime(m) - prevprime(m)`. -/
def gap (m : ℕ) : ℕ := nextPrime m - prevPrime m

/-- Number of `k` with `4 ≤ 2k ≤ N` and `g(2k) = d`. -/
def count (N d : ℕ) : ℕ := ((Finset.Icc 2 (N / 2)).filter fun k => gap (2 * k) = d).card

/-- `a n`: the most common value of `g(2k)` for `4 ≤ 2k ≤ 10^n`, smallest in case of ties. -/
noncomputable def a (n : ℕ) : ℕ := sInf {d | ∀ e, count (10 ^ n) e ≤ count (10 ^ n) d}

/-- Hilliard's conjecture: eventually the most common value is a multiple of 6, and it grows
without bound. -/
theorem main :
    (∀ᶠ n in Filter.atTop, 6 ∣ a n) ∧ Filter.Tendsto a Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a092937

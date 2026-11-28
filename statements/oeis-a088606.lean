import Mathlib

/-!
# A088606: Smallest number k such that concatenation of k and prime(n) is a prime, or 0 if no other number exists. a(1) = a(3) = 0.

Source: https://oeis.org/A088606
Credit: @Solfanbtc

`k ‖ p` is the decimal concatenation `k · 10^(number of digits of p) + p`. `a(n)` is the least
`k ≥ 1` with `k ‖ prime(n)` prime, or `0` if there is none (as for `prime(1) = 2` and
`prime(3) = 5`). This reproduces every term of %S, %T, %U (Python).

Conjecture (Amarnath Murthy, in the entry): "Subsidiary sequences: (set(1)) Index of the start
of the first occurrence of a string of n consecutive 1's or 2's or 3's etc. (set (2)): a(n) =
smallest prime such that concatenation of 1 with n successive primes starting from a(n) gives
primes in each case. (n primes are obtained.) Similarly for 2, 3, etc. Conjecture: The
subsidiary sequences are infinite."

A subsidiary sequence is infinite when its `n`-th term exists for every `n`. So, for every value
`d ≥ 1` ("1's or 2's or 3's etc."; "similarly for 2, 3, etc.") and every length `L ≥ 1`:
1. (set 1) there are `L` consecutive indices `m, …, m + L - 1` (`m ≥ 1`) with `a = d` at each;
2. (set 2) there are `L` consecutive primes `p` with `d ‖ p` prime for each of them.
(Python, primes below `3·10^5`: the longest runs of `a = 1, 2, 3, 4, 5` have lengths
`5, 4, 6, 3, 3`.) Primes are 0-indexed in Lean: `prime(n) = Nat.nth Nat.Prime (n - 1)`.
-/

namespace OMA.S_oeis_a088606

/-- Decimal concatenation `k ‖ p`. -/
def conc (k p : ℕ) : ℕ := k * 10 ^ (Nat.digits 10 p).length + p

/-- A088606 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ (conc k (Nat.nth Nat.Prime (n - 1))).Prime}

theorem main : ∀ d : ℕ, 1 ≤ d → ∀ L : ℕ, 1 ≤ L →
    (∃ m : ℕ, 1 ≤ m ∧ ∀ t : ℕ, t < L → a (m + t) = d) ∧
    (∃ i : ℕ, ∀ t : ℕ, t < L → (conc d (Nat.nth Nat.Prime (i + t))).Prime) := by
  sorry

end OMA.S_oeis_a088606

import Mathlib

/-!
# A109926: divisibility of the least k with exactly n primes k - 2^r

Source: https://oeis.org/A109926 (with https://oeis.org/A109925)
A109925(k) is the number of `r ≥ 0` with `2^r < k` and `k - 2^r` prime. A109926(n) (offset 0) is
the least `k` with A109925(k) = n: 1, 3, 4, 15, 21, 45, 75, 465, 1095, 2145, 4935, 14955, ...
(e.g. `a(4) = 21`: 19, 17, 13, 5 are prime).
Conjectures in the entry:
1. "It appears that 3 and 5 divide a(n) for n>4." (T. D. Noe, Jul 19 2005)
2. "Conjecture: a(n)==0 (mod 3) for n > 2." (Robert G. Wilson v, Jul 21 2005)
3. "Conjecture: a(n+15)==0 (mod 30) for n > 4." (Robert G. Wilson v, Jul 21 2005)

We state 1 and 2 together: for `n > 2`, `3 ∣ a(n)`, and for `n > 4`, `15 ∣ a(n)`.
Conjecture 3 is refuted by the entry's own data and is not stated: it claims `30 ∣ a(20)`, but
`a(20) = 2282745465` is odd (`a(20) ≡ 15 (mod 30)`); all listed terms `a(n)`, `n ≥ 1`, are odd.

Conventions. `a(n)` is spoken of through `IsLeast` (the least `k ≥ 1` with exactly `n` such `r`),
so the statement does not presuppose that `a(n)` exists. The `r` are counted among `r < k`, which
loses nothing since `2^r < k` forces `r < k`.
Checked with python3: the definition gives the listed terms `a(0..15)` (search up to `2·10^6`);
conjectures 1 and 2 hold for all 21 listed terms.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a109926

/-- A109925: the number of `r` with `2^r < k` and `k - 2^r` prime. -/
def count (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun r => 2 ^ r < k ∧ (k - 2 ^ r).Prime)).card

theorem main :
    (∀ n k : ℕ, 2 < n → IsLeast {m : ℕ | 1 ≤ m ∧ count m = n} k → 3 ∣ k) ∧
    (∀ n k : ℕ, 4 < n → IsLeast {m : ℕ | 1 ≤ m ∧ count m = n} k → 3 ∣ k ∧ 5 ∣ k) := by
  sorry

end OMA.S_oeis_a109926

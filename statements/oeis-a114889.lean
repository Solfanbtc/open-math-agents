import Mathlib

/-!
# A114889: Layman's formula for the differences of the power-of-3-sum-free greedy sequence

Source: https://oeis.org/A114889 (with https://oeis.org/A114890)
A114889 (offset 1): `a(1) = 1` and, for `n > 1`, `a(n)` is the smallest integer greater than
`a(n-1)` such that `a(n) + a(i)` is not a power of 3 for `i = 1, ..., n-1`:
1, 3, 4, 7, 9, 10, 11, 12, 13, 19, ...
The entry: "The differences of {a(n)}, together with a conjectured formula for them, is given in
A114890." A114890 (offset 1) is `d(n) = a(n+1) - a(n)`: 2, 1, 3, 2, 1, 1, 1, 1, 6, ...
Conjecture (John W. Layman, A114890): "a(1)=2 and, for n>1, a(n)=1+3+9+...+3^(k-1) + 2, if n=3^k,
a(n)=a(n-3^k), if 3^k < n < 2*3^k - 1, else a(n)=1. (This has been verified for n<=3000.)"

Formalization. `d(1) = 2`, and for `n > 1` with `k` the exponent such that `3^k ≤ n < 3^(k+1)`:
`d(n) = (3^k - 1)/2 + 2` if `n = 3^k` (as `1 + 3 + ... + 3^(k-1) = (3^k - 1)/2`);
`d(n) = d(n - 3^k)` if `3^k < n < 2·3^k - 1`; and `d(n) = 1` otherwise, i.e. if
`2·3^k - 1 ≤ n < 3^(k+1)`. The three cases are stated for each such `k`. "Power of 3" includes
`3^0 = 1` (it never matters: `a(n) + a(i) ≥ 2`).
`terms n` is `[a(1), ..., a(n)]`; each new term is an `sInf` (it exists: only finitely many
`m` are excluded).
Checked with python3: the definition reproduces the listed terms of A114889 and A114890, and
the formula holds for all `n ≤ 30000`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a114889

/-- `m` is a power of 3. -/
def IsPow3 (m : ℕ) : Prop := ∃ j : ℕ, m = 3 ^ j

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {m : ℕ | l.getLastD 0 < m ∧ ∀ x ∈ l, ¬ IsPow3 (m + x)}]

/-- A114889: `a(n)`, `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- A114890: `d(n) = a(n+1) - a(n)`. -/
noncomputable def d (n : ℕ) : ℕ := a (n + 1) - a n

theorem main :
    d 1 = 2 ∧
    ∀ n k : ℕ, 1 < n → 3 ^ k ≤ n → n < 3 ^ (k + 1) →
      (n = 3 ^ k → d n = (3 ^ k - 1) / 2 + 2) ∧
      (3 ^ k < n → n < 2 * 3 ^ k - 1 → d n = d (n - 3 ^ k)) ∧
      (2 * 3 ^ k - 1 ≤ n → d n = 1) := by
  sorry

end OMA.S_oeis_a114889

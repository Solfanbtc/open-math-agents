import Mathlib

/-!
# A083677: smallest k making "p1 k p2 k ... k pn" prime

Source: https://oeis.org/A083677 (see A007504, A083684)
Credit: @Solfanbtc

`f(n, k)` is the concatenation (in decimal) of the first `n` primes with `n - 1` copies of `k`
inserted between them, e.g. `f(4, 0) = 2030507`, `f(4, 1) = 2131517`. `a(n)` is the smallest
`k ≥ 0` such that `f(n, k)` is prime, or `-1` if there is none: 0, 2, -1, 1, 4, 10, ...

Known (entry): `a(3) = -1` (every `f(3, k)` is a multiple of 5), and `a(n) = -1` whenever
`n ≡ 1 (mod 3)` and `A007504(n) = p_1 + ... + p_n ≡ 0 (mod 3)` (every `f(n, k)` is then a multiple
of 3).

Conjecture (entry): "for all other n, -1 < a(n) < n*p(n)", i.e. for every `n ≥ 1` not of these
two kinds there is `k` with `0 ≤ k < n · p_n` such that `f(n, k)` is prime.

Encoding: the decimal string of `x` is `(Nat.digits 10 x).reverse`, except that `0` is the
string "0" (`Nat.digits 10 0` is empty, but inserting `k = 0` inserts a digit 0).

Sanity check (python): this reproduces all 44 listed terms, and the `n ≤ 44` with `a(n) = -1` are
exactly the excluded ones (3, 10, 16, 28, 34, 40).
-/

namespace OMA.S_oeis_a083677

/-- Decimal string of `x`, most significant digit first (`0` gives `[0]`). -/
def decStr (x : ℕ) : List ℕ := if x = 0 then [0] else (Nat.digits 10 x).reverse

/-- `p_i`, the `i`-th prime (`p_1 = 2`). -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- The digit string `p_1 k p_2 k ... k p_n`. -/
noncomputable def fStr (n k : ℕ) : List ℕ :=
  decStr (p 1) ++ ((List.range (n - 1)).map (fun i => decStr k ++ decStr (p (i + 2)))).flatten

/-- `f(n, k)` as a number. -/
noncomputable def f (n k : ℕ) : ℕ := Nat.ofDigits 10 (fStr n k).reverse

/-- The conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 3 →
    ¬ (n % 3 = 1 ∧ (∑ i ∈ Finset.Icc 1 n, p i) % 3 = 0) →
    ∃ k : ℕ, k < n * p n ∧ (f n k).Prime := by
  sorry

end OMA.S_oeis_a083677

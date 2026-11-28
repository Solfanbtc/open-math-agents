import Mathlib

/-!
# A050647: a(n+1)^3 is next smallest cube ending with a(n)^3, initial term is 1.

Source: https://oeis.org/A050647
Credit: @Solfanbtc

Definition (the entry's name, offset 1): `a(1) = 1` and `a(n+1)` is the least `m > a(n)` such that
the decimal expansion of `m^3` ends with that of `a(n)^3`, i.e. `m^3 ≡ a(n)^3 (mod 10^d)` where
`d` is the number of decimal digits of `a(n)^3` (as `a(n)^3 < 10^d`, this says the last `d`
digits of `m^3` are exactly those of `a(n)^3`). Data: `1, 11, 10011, 10000000010011, ...`.

Conjecture (Frank Ellermann, Jun 11 2001, in the entry): with `b(n) = 10^(3^n - 1)`,
`a(n)` is the decimal concatenation `b(n-2) || a(n-1)` for `n > 1`, that is
`a(n) = b(n-2) * 10^(number of digits of a(n-1)) + a(n-1)`.
The entry also records the formula `a(n) = ∑_{i=0}^{n-1} 10^((3^i-1)/2)` (Max Alekseyev,
Jan 07 2015), which implies the conjecture; it is listed without proof in the entry.

A python3 check: brute force gives `a(2) = 11`, `a(3) = 10011`; the data `a(1..5)` satisfy the
concatenation rule, and so do `a(n)`, `n ≤ 8`, computed from the definition.

Conventions: `seq k = a(k + 1)`; the least `m` is `sInf` of the (nonempty: `m = x + 10^d` is in
it) set of candidates.
-/

namespace OMA.S_oeis_a050647

/-- Number of decimal digits of `x` (`0` for `x = 0`; only used for `x ≥ 1`). -/
def numDigits (x : ℕ) : ℕ := (Nat.digits 10 x).length

/-- The least `m > x` whose cube ends with the decimal digits of `x^3`. -/
noncomputable def next (x : ℕ) : ℕ :=
  sInf {m : ℕ | x < m ∧ m ^ 3 % 10 ^ numDigits (x ^ 3) = x ^ 3}

/-- `seq k = a(k + 1)`. -/
noncomputable def seq : ℕ → ℕ
  | 0 => 1
  | k + 1 => next (seq k)

/-- `a n` for `n ≥ 1` (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := seq (n - 1)

/-- Ellermann's conjecture: `a(n) = b(n-2) || a(n-1)` for `n > 1`, `b(k) = 10^(3^k - 1)`. -/
theorem main : ∀ n : ℕ, 1 < n →
    a n = 10 ^ (3 ^ (n - 2) - 1) * 10 ^ numDigits (a (n - 1)) + a (n - 1) := by
  sorry

end OMA.S_oeis_a050647

import Mathlib

/-!
# A088628: Smallest prime using all the digits of first n numbers. If necessary, extra digits can be used.

Source: https://oeis.org/A088628
Credit: @Solfanbtc

`a(n)` is the smallest prime whose (base-10) digits contain, with multiplicity, all the digits of
`1, 2, …, n` (extra digits allowed). E.g. `a(5) = 112543`, `a(10) = 10123457689`, `a(11)` uses
the digits `1,0,1,1,1,1,1,2,2,3,4` plus `5,…,9`.

Conjecture (OEIS entry): there exists `k` such that for all `m > k` with `m` not `≡ 0` or
`2 (mod 3)` (i.e. `m ≡ 1 (mod 3)`), `a(m)` does not use any extra digit, i.e. the digit
multiset of `a(m)` equals the digit multiset of `1, …, m`.

Formalization: `digitsUpTo n` is the multiset of decimal digits of `1, …, n`. `IsA n p` says that
`p` is `a(n)`: a prime containing `digitsUpTo n`, and no smaller prime does. The statement asserts
that, for such `m`, `a(m)` exists and has exactly the digits `digitsUpTo m`. (`a(m)` exists for
every `m`, so this is the conjecture as stated.)
Checked with python3: the definition reproduces a(1..7) = 11, 127, 1123, 1423, 112543,
1124653, 1234657; of these only a(4) and a(7) use no extra digit.
-/

namespace OMA.S_oeis_a088628

/-- The multiset of decimal digits of `1, 2, …, n`. -/
def digitsUpTo (n : ℕ) : Multiset ℕ :=
  ∑ i ∈ Finset.Icc 1 n, ((Nat.digits 10 i : List ℕ) : Multiset ℕ)

/-- `p` uses all the digits of `1, …, n` (with multiplicity; extra digits allowed). -/
def UsesAll (n p : ℕ) : Prop :=
  digitsUpTo n ≤ ((Nat.digits 10 p : List ℕ) : Multiset ℕ)

/-- `p = a(n)`: the smallest prime using all the digits of `1, …, n`. -/
def IsA (n p : ℕ) : Prop :=
  p.Prime ∧ UsesAll n p ∧ ∀ q < p, q.Prime → ¬ UsesAll n q

/-- The conjecture: for all large `m ≡ 1 (mod 3)`, `a(m)` uses no extra digit. -/
theorem main : ∃ k : ℕ, ∀ m : ℕ, k < m → m % 3 ≠ 0 → m % 3 ≠ 2 →
    ∃ p : ℕ, IsA m p ∧ ((Nat.digits 10 p : List ℕ) : Multiset ℕ) = digitsUpTo m := by
  sorry

end OMA.S_oeis_a088628

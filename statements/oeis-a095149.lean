import Mathlib

/-!
# A095149: Aitken's array with a leading diagonal of Bell numbers

Triangle read by rows: Aitken's array (A011971) but with a leading diagonal before it given by
the Bell numbers (A000110), 1, 1, 2, 5, 15, 52, ...

Source: https://oeis.org/A095149
Credit: @Solfanbtc

Rows `n ≥ 0`, columns `0 ≤ k ≤ n` (offset 0): `T(n, 0) = Bell(n)` and `T(n, k) = a(n-1, k-1)`
for `1 ≤ k ≤ n`, where `a` is Aitken's array A011971: `a(0,0) = 1`, `a(n,0) = a(n-1,n-1)`,
`a(n,k) = a(n,k-1) + a(n-1,k-1)`. The first rows are `1; 1,1; 2,1,2; 5,2,3,5; 15,5,7,10,15`.

Conjecture (Gus Wiseman, Aug 11 2020): `T(n, k)` is also the number of divisors `d` with distinct
prime multiplicities of the superprimorial `A006939(n) = ∏_{i=1}^{n} prime(i)^(n-i+1)` that are
of the form `d = m * 2^k` with `m` odd. (Row `n = 4`: the divisors of `2^4 3^3 5^2 7 = 75600` with
distinct prime multiplicities, grouped by the exponent of `2`, number `15, 5, 7, 10, 15`.)

Conventions. `prime(i)` is `Nat.nth Nat.Prime (i - 1)`; "distinct prime multiplicities" means the
exponents of the primes dividing `d` are pairwise distinct (`d = 1` qualifies); "of the form
`m * 2^k` with `m` odd" means the exponent of `2` in `d` is exactly `k`. The entry's
"Equivalently" reformulation (length-`n` vectors) is the same count and is not stated separately.
-/

namespace OMA.S_oeis_a095149

/-- Row `n` of Aitken's array A011971 (`n + 1` entries): each row starts with the last entry of
the previous row, and each later entry adds the entry above-left. -/
def aitkenRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.scanl (· + ·) ((aitkenRow n).getLastD 0) (aitkenRow n)

/-- Aitken's array `a(n, k)`, `0 ≤ k ≤ n`. -/
def aitken (n k : ℕ) : ℕ := (aitkenRow n).getD k 0

/-- The triangle A095149, offset 0: `T(n, 0) = Bell(n)`, `T(n, k) = a(n-1, k-1)` for `k ≥ 1`. -/
def T (n k : ℕ) : ℕ := if k = 0 then Nat.bell n else aitken (n - 1) (k - 1)

/-- The superprimorial `A006939(n) = ∏_{i=1}^{n} prime(i)^(n-i+1)`. -/
noncomputable def superprimorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 n, Nat.nth Nat.Prime (i - 1) ^ (n + 1 - i)

/-- The prime multiplicities of `d` are pairwise distinct. -/
def DistinctMultiplicities (d : ℕ) : Prop :=
  Set.InjOn d.factorization d.primeFactors

/-- Wiseman's conjecture: for `0 ≤ k ≤ n`, `T(n, k)` counts the divisors of `A006939(n)` with
distinct prime multiplicities whose exponent of `2` is `k`. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    Set.ncard {d : ℕ | d ∣ superprimorial n ∧ DistinctMultiplicities d ∧ d.factorization 2 = k} =
      T n k := by
  sorry

end OMA.S_oeis_a095149

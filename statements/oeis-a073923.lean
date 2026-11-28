import Mathlib

/-!
# A073923: a(1)=1, a(n) is the smallest power of 2 not included earlier such that Sum_{k=1..n} a(k) is prime.

Source: https://oeis.org/A073923
Credit: @Solfanbtc

`a` is A073923 (offset 1): `a 1 = 1`, and for `n ≥ 2`, `a n` is the least power of 2 that is not
among `a 1, …, a (n-1)` and makes `a 1 + ⋯ + a n` prime. Data: 1, 2, 4, 16, 8, 4096, 32, ...

`b` is A059661 (offset 1): `b 1 = 2`, and `b (n+1)` is the least number `b n XOR 2^i` that is
prime and greater than `b n` (the Maple program takes the least such `i`; for the XORs exceeding
`b n`, i.e. `b n + 2^i` with bit `i` of `b n` clear, the least `i` gives the least value).
Data: 2, 3, 7, 23, 31, 4127, ...

Conjecture (R. J. Mathar, 2007): `a(n) = A059661(n) - A059661(n-1)`.

Minimal fix of the range: the identity fails at `n = 2` (`a 2 = 2`, but `3 - 2 = 1`). Checked
with python3, it holds for `3 ≤ n ≤ 19`, the whole data. So `main` states it for `n ≥ 3`. (`n = 1`
has no `A059661(0)`.)

Neither sequence is known to be defined for every `n`: a next term may fail to exist. So `main`
is stated for finite prefixes. Whenever `a` satisfies the definition of A073923 up to index `N`
and `b` satisfies the definition of A059661 up to index `N`, the identity holds for
`3 ≤ n ≤ N`. Note: both sequences add, at each step, the least clear binary bit that gives a
prime, starting from the common value 3 at `n = 2`, so the conjecture is expected to follow by
induction.
-/

namespace OMA.S_oeis_a073923

/-- `a` satisfies the definition of A073923 up to index `N`. -/
def IsA073923UpTo (N : ℕ) (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
    ∀ n, 2 ≤ n → n ≤ N →
      IsLeast {x : ℕ | (∃ i : ℕ, x = 2 ^ i) ∧ x ∉ (Finset.Ico 1 n).image a ∧
        (∑ k ∈ Finset.Ico 1 n, a k + x).Prime} (a n)

/-- `b` satisfies the definition of A059661 up to index `N`. -/
def IsA059661UpTo (N : ℕ) (b : ℕ → ℕ) : Prop :=
  b 1 = 2 ∧
    ∀ n, 1 ≤ n → n < N →
      IsLeast {x : ℕ | (∃ i : ℕ, x = b n ^^^ 2 ^ i) ∧ b n < x ∧ x.Prime} (b (n + 1))

theorem main :
    ∀ (N : ℕ) (a b : ℕ → ℕ), IsA073923UpTo N a → IsA059661UpTo N b →
      ∀ n, 3 ≤ n → n ≤ N → a n = b n - b (n - 1) := by
  sorry

end OMA.S_oeis_a073923

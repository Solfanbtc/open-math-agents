import Mathlib

/-!
# A072339: minimal length of an alternating binary representation

Any number n can be written (in two ways, one with m even and one with m odd) in the form
`n = 2^k_1 - 2^k_2 + 2^k_3 - ... + 2^k_m` where the signs alternate and
`k_1 > k_2 > k_3 > ... > k_m >= 0`; the sequence gives the minimal value of `m` (`n ≥ 1`).

Source: https://oeis.org/A072339
Credit: @Solfanbtc

Conjecture (John W. Layman, Jul 18 2002), as printed: "a(n)=1 if n=2^k, a(n)=a(2^k-i)+1 if
2^k<n+i<2^(k+1)."

Reading. The printed range "2^k < n+i < 2^(k+1)" leaves `i` unrelated to `n` and cannot be meant
literally (for a fixed `n` it would force `a(n) = a(2^k - i) + 1` for many different `i`). The
evident intended condition, with a lost `=`, is `2^k < n = 2^k + i < 2^(k+1)`, i.e.
`0 < i < 2^k`: then `a(2^k + i) = a(2^k - i) + 1`. This is the reading stated here; a python
brute force (all exponent sets within `{0, ..., 13}`, which suffices for `n < 2^12` since
`k_1 ≤ log₂ n + 1`) confirms it for all `n < 2^12`, together with `a(2^k) = 1`.

Formalization. A representation is a list `[k_1, ..., k_m]` of exponents, strictly decreasing
(`List.Pairwise (· > ·)`), whose alternating sum `2^k_1 - 2^k_2 + ...` (`List.alternatingSum`
of the powers, in `ℤ`) equals `n`; `a n` is the least length of such a list.
-/

namespace OMA.S_oeis_a072339

/-- `l` is a strictly decreasing list of exponents with `2^l₁ - 2^l₂ + 2^l₃ - ... = n`. -/
def IsRep (n : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· > ·) ∧ (l.map fun k => (2 : ℤ) ^ k).alternatingSum = n

/-- A072339(n): the minimal number of terms of such a representation of `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | ∃ l : List ℕ, l.length = m ∧ IsRep n l}

/-- Layman's conjecture: `a(2^k) = 1`, and `a(2^k + i) = a(2^k - i) + 1` for `0 < i < 2^k`. -/
theorem main :
    (∀ k : ℕ, a (2 ^ k) = 1) ∧
    ∀ k i : ℕ, 0 < i → i < 2 ^ k → a (2 ^ k + i) = a (2 ^ k - i) + 1 := by
  sorry

end OMA.S_oeis_a072339

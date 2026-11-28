import Mathlib

/-!
# A086519: a(n) is the least prime not already used such that (a(n)+a(n-1))/2 is prime.

Source: https://oeis.org/A086519
Credit: @Solfanbtc

`a(1) = 3` (offset 1); for `n ≥ 2`, `a(n)` is the least prime not among `a(1), ..., a(n-1)`
such that `(a(n) + a(n-1))/2` is a prime (in particular an integer, so `a(n) + a(n-1)` is even).
Here the sequence is 0-indexed: `a 0 = 3`, `a 1 = 7`, `a 2 = 19`, ... (the same recursion,
computed in Python, reproduces the OEIS data). If no admissible prime exists the value is the
junk `sInf ∅ = 0`, which does not affect the statement below.

The entry's first conjecture, "every prime of the type 6k+1 is a member", is false as written:
D. Wasserman (Mar 11 2005) notes that after the first term every member is `≡ 7 (mod 12)`,
so e.g. `13` never occurs (terms with `a(n-1) ≡ 7`, `a(n) ≡ 1 (mod 12)` have even half-sum
`≡ 4 (mod 6)`). We state his corrected conjecture: every prime of the form `12k + 7` is a member.
Numerically, the first 3000 terms contain every prime `≡ 7 (mod 12)` below 20000.
-/

namespace OMA.S_oeis_a086519

/-- The least prime not in `used` whose half-sum with `last` is a prime. -/
noncomputable def nextTerm (last : ℕ) (used : List ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ∉ used ∧ 2 ∣ last + p ∧ ((last + p) / 2).Prime}

/-- The terms `a 0, ..., a n`, most recent first. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [3]
  | n + 1 =>
    let l := terms n
    nextTerm (l.headD 0) l :: l

/-- `a n` is the `(n+1)`-st term of A086519. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).headD 0

theorem main : ∀ p : ℕ, p.Prime → p % 12 = 7 → ∃ n : ℕ, a n = p := by
  sorry

end OMA.S_oeis_a086519

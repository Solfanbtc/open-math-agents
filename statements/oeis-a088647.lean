import Mathlib

/-!
# A088647: a(1) = 1, then the smallest number such that the concatenation a(r), a(s) is prime for all s > r.

Source: https://oeis.org/A088647
Credit: @Solfanbtc

The data (offset 0) are 1, 1, 3, 7, 73, 433, 607, 13381, 37279, 4800307. After the two initial 1's,
each term is the least number `x`, greater than the previous term, such that the decimal
concatenation `a(r) x` is prime for every earlier term `a(r)`. Example: 173, 373, 773 are prime,
giving 73. Some such restriction is needed: without one, 1 itself (11 prime) would be chosen
again and again. Checked with python3: this rule gives exactly the 10 listed terms, and so does
the variant "least `x` not already in the sequence".

`terms n` is the list of the first `n + 2` terms, as long as candidates exist, and
`Candidates l` is the set of admissible next terms after the list `l`.

Conjecture (A. Murthy): the sequence is finite, i.e. at some stage there is no admissible next
term. `main` states this.
-/

namespace OMA.S_oeis_a088647

/-- Decimal concatenation of `r` and `x`. -/
def concat (r x : ℕ) : ℕ := r * 10 ^ (Nat.digits 10 x).length + x

/-- Admissible next terms after the list `l`. -/
def Candidates (l : List ℕ) : Set ℕ :=
  {x | l.getLastD 0 < x ∧ ∀ r ∈ l, (concat r x).Prime}

/-- `terms n`: the first `n + 2` terms, starting from `[1, 1]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1, 1]
  | n + 1 => terms n ++ [sInf (Candidates (terms n))]

theorem main : ∃ n : ℕ, Candidates (terms n) = ∅ := by
  sorry

end OMA.S_oeis_a088647

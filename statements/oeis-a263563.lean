import Mathlib

/-!
# A263563: a self-describing sequence read from a string of digits

Source: https://oeis.org/A263563
Credit: @Solfanbtc

"When the sequence is read as a string of decimal digits, `a(n)` can be read from position `n`
(ignoring leading zeros). This sequence is the lexicographically earliest sequence of distinct
terms with this property." Data: `1, 2, ..., 10, 11, 110, 100, 12, 120, 1200, 20, 13, ...`.
The entry states: "This sequence is conjectured to be a permutation of natural numbers".

Reading of the definition, fixed by the entry's example table: there is one infinite string of
decimal digits `D(1) D(2) ...`, and for each `n` the digits `D(n) ... D(n + L - 1)`, for some
length `L`, spell `a(n)` with possibly some leading zeros. The readings overlap; the string is not
the concatenation of the terms (the table has `D(10..15) = 1, 0, 1, 1, 0, 0`: `a(10) = 10`,
`a(11) = 011`, `a(12) = 110`, `a(13) = 100`, `a(14) = 0012`). Terms are positive integers (with
`0` allowed the greedy choice would give `a(11) = 0`, read from `D(11) = 0`, not `11`) and pairwise
distinct. A python3 greedy construction under this reading (smallest unused value readable at
position `n`, with the fewest leading zeros) reproduces the 57 listed terms.

Formalization (0-based: `s n = a(n+1)`, `D p` = digit at 1-based position `p+1`): `SelfDescribing s`
says `s` is positive and injective and some digit string `D` has, for every `n`, a length `L`
with `ofDigits 10 [D(n+L-1), ..., D(n)] = s n` (`Nat.ofDigits` takes the least significant digit
first; leading zeros do not change the value). `IsLexEarliest` is lexicographic minimality among
such sequences. The lexicographically earliest sequence is unique, so we state that it exists
(the entry defines the sequence as this object) and that every positive integer occurs in it.
-/

namespace OMA.S_oeis_a263563

/-- `s` is a sequence of distinct positive integers, each read (with possible leading zeros) from
the same infinite digit string, starting at its own index. -/
def SelfDescribing (s : ℕ → ℕ) : Prop :=
  (∀ n, 0 < s n) ∧ Function.Injective s ∧
    ∃ D : ℕ → ℕ, (∀ p, D p < 10) ∧
      ∀ n, ∃ L : ℕ, Nat.ofDigits 10 ((List.range L).map fun i => D (n + L - 1 - i)) = s n

/-- Lexicographic order on sequences. -/
def LexLT (t s : ℕ → ℕ) : Prop := ∃ n, (∀ i < n, t i = s i) ∧ t n < s n

/-- `s` is the lexicographically earliest self-describing sequence. -/
def IsLexEarliest (s : ℕ → ℕ) : Prop := SelfDescribing s ∧ ∀ t, SelfDescribing t → ¬ LexLT t s

/-- The lexicographically earliest such sequence exists and is a permutation of the positive
integers (it is injective by definition; every positive integer occurs). -/
theorem main : ∃ s : ℕ → ℕ, IsLexEarliest s ∧ ∀ m : ℕ, 0 < m → ∃ n, s n = m := by
  sorry

end OMA.S_oeis_a263563

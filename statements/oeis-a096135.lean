import Mathlib

/-!
# A096135: permutations of a block of n consecutive numbers whose concatenation is a multiple of n

Source: https://oeis.org/A096135
Row `n` of the triangle is the permutation of the `n` numbers `T(n-1)+1, ..., T(n)`
(`T(n) = n(n+1)/2` the triangular numbers) whose decimal concatenation is the smallest multiple
of `n`; if no permutation gives a multiple of `n`, the row contains zeros.
The entry's conjecture: "No term is zero", i.e. for every `n ≥ 1` some permutation of
`T(n-1)+1, ..., T(n)` concatenates (in base 10) to a multiple of `n`.

Conventions. `concat [x₁, ..., x_k]` is the number whose decimal representation is the
decimal representations of `x₁, ..., x_k` written one after another (all entries are `≥ 1`, so
there are no leading zeros). The block `T(n-1)+1, ..., T(n)` is `List.range' (n(n-1)/2 + 1) n`.
Checked: `concat [7, 9, 10, 8] = 79108` (the example in the entry), and an `#eval` search over all
permutations finds at least one for every `1 ≤ n ≤ 9` (row 4: only `79108`, as in the entry).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a096135

/-- Decimal concatenation of a list of natural numbers. -/
def concat (l : List ℕ) : ℕ :=
  l.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ l : List ℕ, l.Perm (List.range' (n * (n - 1) / 2 + 1) n) ∧ n ∣ concat l := by
  sorry

end OMA.S_oeis_a096135

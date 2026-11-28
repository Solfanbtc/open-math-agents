import Mathlib

/-!
# A254337: Lexicographically earliest sequence of distinct numbers such that no sum of consecutive terms is prime.

Source: https://oeis.org/A254337
Credit: @Solfanbtc

`a(0), a(1), …` are distinct natural numbers such that no sum `a(i) + a(i+1) + … + a(n)`
(`i ≤ n`, including single terms) is prime, chosen lexicographically earliest. Data:
`0, 1, 8, 6, 10, 14, 12, 4, 20, …`.

The lexicographically earliest such sequence is the greedy one: each term is the least number
not used before such that every sum of consecutive terms ending with it is not prime. (A valid
next term always exists: by the Chinese remainder theorem some `k` makes the finitely many sums
`S + k` all composite and is new, so the greedy choice never gets stuck.) We define it greedily
with `sInf`, from `a(0) = 0` (itself the greedy choice); this reproduces the listed data
(checked numerically).

Conjecture (M. F. Hasler, in the entry): the sequence contains all even numbers `> 2` and no
odd number beyond `1`. (Checked numerically for the first 2000 terms.)
-/

namespace OMA.S_oeis_a254337

/-- `terms n = [a(0), …, a(n)]`, built greedily. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let L := terms n
    L ++ [sInf {k | k ∉ L ∧ ∀ i ≤ L.length, ¬ ((L.drop i).sum + k).Prime}]

/-- A254337(n). -/
noncomputable def a254337 (n : ℕ) : ℕ := (terms n).getLastD 0

/-- Conjecture (OEIS A254337): every even number `> 2` occurs, and every odd term is `1`. -/
theorem main :
    (∀ m : ℕ, Even m → 2 < m → ∃ n, a254337 n = m) ∧
    (∀ n : ℕ, Odd (a254337 n) → a254337 n = 1) := by
  sorry

end OMA.S_oeis_a254337

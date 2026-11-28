import Mathlib

/-!
# A126700: infinitely many twin simili-primes of order 2

Source: https://oeis.org/A126700 (with https://oeis.org/A123929)
A123929, simili-primes of order 2 (Eric Angelini, Hugo van der Sanden): examine the integers from
2 on and call "atom" the *second* integer (after the previous atom) which cannot be divided by
another atom: 3, 5, 8, 13, 17, 22, 28, 31, ... (with "first" instead of "second" this sieve
gives the primes).
A126700: "q > p are 'twin simili-primes of order 2' if (p, q) are in A123929 and satisfy
q - p = 3. Conjecture: this sequence is infinite." Data: 5, 8, 28, 31, 148, 151, ...

We state: there are infinitely many `p` such that `p` and `p + 3` are both in A123929.
Formalization. `atoms n` is the list of the first `n` atoms; the next atom is the second integer
greater than the last atom (greater than 1 at the start, so the scan begins at 2) that is not
divisible by any atom so far, i.e. `Nat.nth` with index 1 of that (infinite) set.
Checked with python3: the sieve reproduces the 57 listed terms of A123929, and the twin pairs
reproduce the 48 listed terms of A126700.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a126700

/-- The first `n` simili-primes of order 2. -/
noncomputable def atoms : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := atoms n
    l ++ [Nat.nth (fun k => l.getLastD 1 < k ∧ ∀ a ∈ l, ¬ a ∣ k) 1]

/-- A123929: the set of simili-primes of order 2. -/
def SimiliPrime (m : ℕ) : Prop := ∃ n : ℕ, m ∈ atoms n

theorem main : {p : ℕ | SimiliPrime p ∧ SimiliPrime (p + 3)}.Infinite := by
  sorry

end OMA.S_oeis_a126700

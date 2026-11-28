import Mathlib

/-!
# A214583: 1722 is the largest m such that m - k^2 is prime for all k coprime to m with k^2 < m

Source: https://oeis.org/A214583
Credit: @Solfanbtc

A214583: the numbers `m` such that for all `k` with `gcd(m, k) = 1` and `m > k^2`, `m - k^2` is
prime. Data 3, 4, 6, 8, 12, 14, 18, 20, 24, 30, …, 572, 930, 1722; "No further terms < 10^10."

The entry quotes L. Moser, Unsolved Problems and Conjectures, p. 84: "Is 968 the largest number
n such that for all k with (n, k) = 1 and n > k^2, n - k^2 is prime? (Erdős)", and notes that
the statement contains an error: 968 does not have the property (`968 - 25^2 = 343 = 7^3`), and
"the largest such number (1722) is larger than 968".

Minimal fix: the question as posed has a false premise; `main` states its corrected form, the
claim of the entry that `1722` is the largest number with the property. This is stronger than
the finiteness statement already upstream (`Erdos1141.erdos_1141`, proved by Alexeev, Putterman,
Sawhney, Sellke and Valiant, arXiv:2604.06609, from Pollack's bounds); finiteness alone does not
give the value of the largest term, and the entry's search only reaches `10^10`.

Conventions. `k` ranges over all natural numbers, including `k = 0` (`gcd(m, 0) = m`, so `k = 0`
counts only for `m = 1`, which is excluded since `1 - 0 = 1` is not prime), exactly as in the
upstream definition; with python3 this reproduces the data, and the terms below `2·10^5` are the
41 listed ones, the largest being 1722.
-/

namespace OMA.S_oeis_a214583

/-- `m - k^2` is prime for every `k` coprime to `m` with `k^2 < m`. -/
def Good (m : ℕ) : Prop := ∀ k : ℕ, k ^ 2 < m → Nat.Coprime m k → (m - k ^ 2).Prime

/-- Corrected Erdős-Moser question: `1722` is the largest number with the property. -/
theorem main : IsGreatest {m : ℕ | Good m} 1722 := by
  sorry

end OMA.S_oeis_a214583

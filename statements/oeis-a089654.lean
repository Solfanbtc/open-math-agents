import Mathlib

/-!
# A089654: Table T(n,k), read by rows, related to a conjecture of P. Erdos (see A039669).

Source: https://oeis.org/A089654
Credit: @Solfanbtc

Conjecture (P. Erdős, recorded in A089654 and A039669): the entries T(n, k) of row n are all
primes for n = 3, 7, 10, 22, 37, 52, and these are the only values of n with this property
(verified for n up to 2^77).

Definitions: T(n, k) = 2n + 1 - 2^k for the k >= 1 with T(n, k) > 0, i.e. 2^k < 2n + 1 (row 1: 1;
row 2: 3, 1; row 3: 5, 3; ...; row 10: 19, 17, 13, 5). `main`: for n >= 1, every entry of row n is
prime iff n ∈ {3, 7, 10, 22, 37, 52}. This is Erdős's conjecture on the m with m - 2^k prime for all
2^k < m (A039669: 4, 7, 15, 21, 45, 75, 105), restricted to odd m = 2n + 1. (Upstream
`Erdos1142.erdos_1142` asks whether that set is infinite, and its solved variant covers
m <= 2^44; neither states that the listed values are the only ones.)
-/

namespace OMA.S_oeis_a089654

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∀ k : ℕ, 1 ≤ k → 2 ^ k < 2 * n + 1 → (2 * n + 1 - 2 ^ k).Prime) ↔
      n ∈ ({3, 7, 10, 22, 37, 52} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a089654

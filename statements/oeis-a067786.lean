import Mathlib

/-!
# A067786: Numbers n such that phi(n) = 2*pi(n) where pi(n) = A000720(n) and phi(n) = A000010(n).

Source: https://oeis.org/A067786
Credit: @Solfanbtc

Conjecture (Donovan Johnson, Nov 24 2013, OEIS A067786): there are no more terms < 10^10;
the sequence is conjectured to be complete, i.e. the n with phi(n) = 2 pi(n) are exactly the 20
listed terms 11, 13, 27, 39, 63, 122, 124, 136, 152, 176, 224, 322, 364, 410, 460, 1086, 1164,
3432, 3612, 12012.

pi(n) is the number of primes <= n (`Nat.primeCounting`), phi is `Nat.totient`. n = 0 is excluded
(phi(0) = 0 = 2 pi(0) is a convention artefact; the sequence lists positive integers).
Checked numerically for n <= 10^6.
-/

namespace OMA.S_oeis_a067786

theorem main :
    {n : ℕ | 0 < n ∧ Nat.totient n = 2 * Nat.primeCounting n} =
      ({11, 13, 27, 39, 63, 122, 124, 136, 152, 176, 224, 322, 364, 410, 460, 1086, 1164, 3432,
        3612, 12012} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a067786

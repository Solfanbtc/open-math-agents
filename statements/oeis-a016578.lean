import Mathlib

/-!
# A016578: Decimal expansion of log(3/2).

Source: https://oeis.org/A016578
Credit: @Solfanbtc

Conjecture (Hugo Pfoertner, May 08 2026, OEIS A016578): log(3/2) is the asymptotic density of
the Fouvry primes A073024, i.e. of the primes p such that p - 1 has a prime factor q > p^(2/3).

The density is relative to the primes, as in the table of A395819 (to which the comment points),
which lists a(n)/primepi(10^n) for the count a(n) of Fouvry primes below 10^n (0.38018 at
n = 12, slowly increasing towards log(3/2) = 0.405465...). Fouvry showed that this relative
density, if it exists, is positive in the lower sense (A073024). We state: the number of Fouvry
primes p <= N divided by primepi(N) tends to log(3/2). Counting p <= N or p < N does not change
the limit.
-/

namespace OMA.S_oeis_a016578

/-- `p` is a Fouvry prime (A073024): `p` is prime and `p - 1` has a prime factor `q > p^(2/3)`. -/
def IsFouvry (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ q ∣ p - 1 ∧ (p : ℝ) ^ ((2 : ℝ) / 3) < q

open Classical in
/-- Number of Fouvry primes `p ≤ N`. -/
noncomputable def fouvryCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter IsFouvry).card

theorem main :
    Filter.Tendsto (fun N : ℕ => (fouvryCount N : ℝ) / (Nat.primeCounting N : ℝ))
      Filter.atTop (nhds (Real.log (3 / 2))) := by
  sorry

end OMA.S_oeis_a016578

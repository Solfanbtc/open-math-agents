import Mathlib

/-!
# A050327: Factorizations into distinct squarefree factors, indexed by prime signatures.

Source: https://oeis.org/A050327
Credit: @Solfanbtc

A050327(n) = A050326(A025487(n)): the number of factorizations into distinct squarefree factors
of the n-th product of primorials. Conjecture (Michael De Vlieger, Oct 06 2017, in the entry):
the prime signatures corresponding to the primorials A002110(i) with i > 1 set records in this
sequence (his list of record-setting terms of A025487: 1, 6, 30, 210, 420, 1260, 2310, ...).

Conventions.
* A050326(m): number of factorizations of m into distinct squarefree factors > 1, i.e. the
  number of finite sets S of squarefree integers > 1 with ∏ S = m (A050326(1) = 1, the empty
  factorization); such S consist of divisors of m.
* A025487: the products of primorials, i.e. m ≥ 1 whose prime exponents are nonincreasing
  along the primes 2, 3, 5, 7, ...: e_(p_(i+1))(m) ≤ e_(p_i)(m) for all i.
* A002110(i) = product of the first i primes. Since A050327 lists A050326 along A025487 in
  increasing order, "A002110(i) sets a record" means A050326(m) < A050326(A002110(i)) for every
  m in A025487 with m < A002110(i).
* python3: the record-setting terms of A025487 up to 30030 are 1, 6, 30, 210, 420, 1260, 2310,
  4620, 13860, 30030, matching the entry; in particular A002110(i) for i = 2..6.
-/

namespace OMA.S_oeis_a050327

/-- A050326: factorizations of m into distinct squarefree factors > 1. -/
def A050326 (m : ℕ) : ℕ :=
  (m.divisors.powerset.filter fun S => (∀ d ∈ S, 1 < d ∧ Squarefree d) ∧ ∏ d ∈ S, d = m).card

/-- A025487: products of primorials (nonincreasing prime exponents). -/
def IsProductOfPrimorials (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ i : ℕ, m.factorization (Nat.nth Nat.Prime (i + 1)) ≤ m.factorization (Nat.nth Nat.Prime i)

/-- A002110(i): the product of the first i primes. -/
noncomputable def primorialN (i : ℕ) : ℕ := ∏ j ∈ Finset.range i, Nat.nth Nat.Prime j

theorem main : ∀ i : ℕ, 1 < i →
    ∀ m : ℕ, IsProductOfPrimorials m → m < primorialN i → A050326 m < A050326 (primorialN i) := by
  sorry

end OMA.S_oeis_a050327

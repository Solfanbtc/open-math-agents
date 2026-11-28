import Mathlib

/-!
# A105974: (A001035(n) - 1)/2 where A001035 is the number of partially ordered sets ("posets") with n labeled elements.

Source: https://oeis.org/A105974
Credit: @Solfanbtc

Conjectures (Gerald McGarvey, OEIS A105974, %C line): `a(n)` is (pre)periodic modulo `m` for
all `m`, the lengths of the ending periods being given by `2 * φ(m)` if `m` is a power of 2 and
`φ(m)` otherwise (`φ` = Euler's totient, A000010).

Formalization.
* `numPosets n` (A001035) counts the partial orders on `Fin n`, i.e. the relations
  `R ⊆ Fin n × Fin n` that are reflexive, antisymmetric and transitive. It is odd (the
  involution `R ↦ R⁻¹` fixes only the discrete order), so `a n = (numPosets n - 1) / 2` is exact.
* `IsEventualPeriod f L`: `f (n + L) = f n` for all large `n`. The conjecture's period length
  `L(m)` is read as the least `L > 0` with `IsEventualPeriod (a · % m) L` ("length of the ending
  period"), for `m ≥ 3`. For `m = 1` and `m = 2` that reading fails at once: `a(n) mod 1 = 0`,
  and `a(n)` is odd for `2 ≤ n ≤ 15` (all listed terms), so the least period there is `1`, not
  `2 φ(m) = 2`. The minimal fix kept here: for `m ∈ {1, 2}` only eventual periodicity with
  period `L(m) = 2` is asserted; for `m ≥ 3`, `L(m)` is a period and the least one.
* Powers of 2 include `m = 1 = 2^0`.

Checked with python3 on the 16 listed terms (which equal `(A001035(n) - 1)/2` for all listed
terms of A001035): for `3 ≤ m ≤ 12` the residues are eventually periodic with least period
exactly `L(m)` within the data (`m = 4`: `1,1,1,3,3,1,1,3,3,...`, period 4 = `2 φ(4)`);
`#eval` gives `numPosets n = 1, 1, 3, 19, 219` for `n ≤ 4`.
-/

namespace OMA.S_oeis_a105974

/-- A001035: the number of partial orders on `Fin n`, as relations `R ⊆ Fin n × Fin n`. -/
def numPosets (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).powerset.filter (fun R =>
    (∀ x, (x, x) ∈ R) ∧ (∀ x y, (x, y) ∈ R → (y, x) ∈ R → x = y) ∧
      ∀ x y z, (x, y) ∈ R → (y, z) ∈ R → (x, z) ∈ R)).card

/-- A105974: `(A001035(n) - 1) / 2`. -/
def a (n : ℕ) : ℕ := (numPosets n - 1) / 2

/-- `L` is an eventual period of `f`. -/
def IsEventualPeriod (f : ℕ → ℕ) (L : ℕ) : Prop := ∃ N, ∀ n ≥ N, f (n + L) = f n

/-- The conjectured length of the ending period modulo `m ≥ 1` (`m` is a power of 2, including
`1 = 2^0`, iff its set of prime factors is contained in `{2}`). -/
def periodLength (m : ℕ) : ℕ := if m.primeFactors ⊆ {2} then 2 * m.totient else m.totient

/-- McGarvey's conjecture: modulo every `m ≥ 1`, `a` is eventually periodic with period
`periodLength m`, which for `m ≥ 3` is the least eventual period. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    IsEventualPeriod (fun n => a n % m) (periodLength m) ∧
    (3 ≤ m → ∀ L, 0 < L → IsEventualPeriod (fun n => a n % m) L → periodLength m ≤ L) := by
  sorry

end OMA.S_oeis_a105974

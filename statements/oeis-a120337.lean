import Mathlib

/-!
# A120337: Euler-irregular primes p dividing E(2k) for some 2k < p-1.

Source: https://oeis.org/A120337
Credit: @Solfanbtc

Conjecture (Ernvall and Metsänkylä, 1978, Math. Comp. 32, pp. 617-629; quoted in the OEIS entry
by Amiram Eldar): the asymptotic density of this sequence within the primes is
`1 - 1/sqrt(e) = 0.393469...` (A290506).

Conventions:
* `E(m)` are the (signed) Euler numbers `1, 0, -1, 0, 5, 0, -61, 0, 1385, ...` (A122045),
  defined by `E(0) = 1`, `E(m) = 0` for odd `m`, and `E(m) = -∑_{i<m} C(m,i) E(i)` for even
  `m ≥ 2` (the recurrence coming from `sech x · cosh x = 1`).
* A prime `p` is Euler-irregular when `p ∣ E(2k)` for some `k ≥ 1` with `2k < p - 1`.
  Checked in Python: this reproduces all listed terms `19, 31, …, 983` (%S, %T, %U).
* "Density within the primes" is the limit, as `x → ∞`, of the number of Euler-irregular primes
  `≤ x` divided by the number of primes `≤ x`.
-/

namespace OMA.S_oeis_a120337

open Filter Topology

/-- The signed Euler numbers `E(m)`. -/
def eulerNum (m : ℕ) : ℤ :=
  if m % 2 = 1 then 0
  else if m = 0 then 1
  else -∑ i : Fin m, (m.choose i.val : ℤ) * eulerNum i.val
termination_by m
decreasing_by exact Fin.isLt _

/-- `p` is an Euler-irregular prime: `p ∣ E(2k)` for some `1 ≤ k` with `2k < p - 1`. -/
def EulerIrregular (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ 2 * k < p - 1 ∧ (p : ℤ) ∣ eulerNum (2 * k)

/-- Ernvall–Metsänkylä: the Euler-irregular primes have density `1 - 1/√e` among the primes. -/
theorem main : Tendsto
    (fun x : ℕ => ((Nat.card {p : ℕ // p ≤ x ∧ EulerIrregular p} : ℝ) /
      (Nat.card {p : ℕ // p ≤ x ∧ p.Prime} : ℝ)))
    atTop (𝓝 (1 - 1 / Real.sqrt (Real.exp 1))) := by
  sorry

end OMA.S_oeis_a120337

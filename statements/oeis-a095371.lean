import Mathlib

/-!
# A095371: Number of distinct prime factors of record setting repunits (A328899).

Source: https://oeis.org/A095371
Credit: @Solfanbtc

Let `R(k) = (10^k - 1)/9` be the `k`-th repunit and `ω(m)` the number of distinct prime factors
of `m`. A repunit `R(k)` (`k ≥ 1`) sets a record if `ω(R(j)) < ω(R(k))` for all `1 ≤ j < k`
(A328899 lists these `k`: 1, 2, 3, 6, 12, …). A095371 lists the record values `ω(R(k))` in
increasing order, offset 1: `a(1) = 0, a(2) = 1, a(3) = 2, a(4) = 5, a(5) = 7, …, a(23) = 63`.
Here `a(i) = Nat.nth IsRecordValue (i - 1)`, the `i`-th smallest record value (record values
are strictly increasing along the records, so this is the order of the sequence).

Conjecture (Chai Wah Wu, Nov 01 2019): `a(24) = 73`, `a(25) = 94`, `a(26) = 99`, `a(27) ≥ 107`,
`a(28) ≥ 127`, `a(29) ≥ 136`, `a(30) ≥ 140`, `a(31) ≥ 151`, `a(32) ≥ 159`, `a(33) ≥ 163`,
`a(34) ≥ 178`, `a(35) ≥ 184`, `a(36) ≥ 213`, `a(37) ≥ 214`.
-/

namespace OMA.S_oeis_a095371

/-- The `k`-th repunit `(10^k - 1)/9`. -/
def repunit (k : ℕ) : ℕ := (10 ^ k - 1) / 9

/-- `ω(R(k))`: the number of distinct prime factors of the `k`-th repunit. -/
def omegaR (k : ℕ) : ℕ := (repunit k).primeFactors.card

/-- `v` is a record value: `v = ω(R(k))` for some `k ≥ 1` with `ω(R(j)) < v` for `1 ≤ j < k`. -/
def IsRecordValue (v : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ omegaR k = v ∧ ∀ j : ℕ, 1 ≤ j → j < k → omegaR j < v

/-- A095371 (offset 1). -/
noncomputable def a (i : ℕ) : ℕ := Nat.nth IsRecordValue (i - 1)

/-- Wu's conjectured values and lower bounds for `a(24), …, a(37)`. -/
theorem main :
    a 24 = 73 ∧ a 25 = 94 ∧ a 26 = 99 ∧ 107 ≤ a 27 ∧ 127 ≤ a 28 ∧ 136 ≤ a 29 ∧
    140 ≤ a 30 ∧ 151 ≤ a 31 ∧ 159 ≤ a 32 ∧ 163 ≤ a 33 ∧ 178 ≤ a 34 ∧ 184 ≤ a 35 ∧
    213 ≤ a 36 ∧ 214 ≤ a 37 := by
  sorry

end OMA.S_oeis_a095371

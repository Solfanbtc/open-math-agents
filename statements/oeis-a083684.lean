import Mathlib

/-!
# A083684: Numbers k such that there is no nonnegative integer m such that m < k*prime(k) and the concatenated decimal number fp(k,m) = prime(1).m.prime(2).m. ... .prime(k-1).m.prime(k) is prime.

Source: https://oeis.org/A083684
Credit: @Solfanbtc

`fp(k, m)` is the decimal concatenation `prime(1) m prime(2) m … m prime(k)` (`m` written in
decimal, `0` as the digit `0`; e.g. `fp(2, 2) = 223`). `k ≥ 1` is a term when no `m` with
`0 ≤ m < k·prime(k)` makes `fp(k, m)` prime. (The name's bound `m < k·prime(k)` is used; the
PARI program also tries `m = k·prime(k)`.) A Python check of the definition gives the terms
`3, 10, 16, 28, 34, 40` for `k ≤ 40`, as in the data.

Comment (Farideh Firoozbakht): if `k ≡ 1 (mod 3)` and `3` divides
`prime(1) + … + prime(k)`, then `k` is a term (the digit sum of `fp(k, m)` is `≡ prime(1) + … +
prime(k) + (k-1)·(digit sum of m) ≡ 0 (mod 3)`). Conjecture: `3` is the only term not of this
form. Stated as: every term `k ≠ 3` has `k ≡ 1 (mod 3)` and `3 ∣ prime(1) + … + prime(k)`. (All 31
listed terms up to `268` satisfy this; conversely every `k ≤ 268` of that form is listed.)
`prime(i) = Nat.nth Nat.Prime (i - 1)`.
-/

namespace OMA.S_oeis_a083684

/-- `prime(i)`, 1-indexed. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- Decimal digits of `x`, most significant first (`0` gives `[0]`). -/
def dl (x : ℕ) : List ℕ := if x = 0 then [0] else (Nat.digits 10 x).reverse

/-- `fp(k, m) = prime(1) m prime(2) m … m prime(k)` as a decimal concatenation. -/
noncomputable def fp (k m : ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.range k).flatMap
    (fun i => dl (prime (i + 1)) ++ (if i + 1 < k then dl m else []))).reverse

/-- `k` is a term of A083684. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ ∀ m : ℕ, m < k * prime k → ¬ (fp k m).Prime

theorem main : ∀ k : ℕ, IsTerm k → k ≠ 3 →
    k % 3 = 1 ∧ 3 ∣ ∑ i ∈ Finset.Icc 1 k, prime i := by
  sorry

end OMA.S_oeis_a083684

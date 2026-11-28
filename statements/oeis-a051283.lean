import Mathlib

/-!
# A051283: Numbers k such that if one writes k = Product pi^ei (pi primes) and P = max pi^e_i, then k/P > P.

Source: https://oeis.org/A051283
Credit: @Solfanbtc

`k ∈ A051283` iff `P < k / P`, where `P = A034699(k)` is the largest prime power factor of `k`
(`A034699(1) = 1`). Data: `30, 60, 70, 84, 90, 105, 120, ...`.

The entry records three conjectured characterizations, stated here together as one conjunction:
1. (Amiram Eldar, Jul 16 2021) `k ∈ A051283` iff `A346418(k) > 1`, where `A346418(k)` is the
   exponent of the largest power of `k` dividing `lcm(1, ..., k)` (and `A346418(1) = 1`).
2. (Antti Karttunen, Jun 19 2022) `k ∈ A051283` iff `A354933(k) > A034699(k)`, where
   `A354933(1) = 1` and for `n > 1`, `A354933(n) = n / c` with `c` the largest divisor of `n`
   that is coprime to a larger divisor of `n`.
3. (Ralf Stephan, Feb 20 2004) `A051283(n) = A080170(n) + 1`, where A080170 lists the `k ≥ 1` with
   `gcd(C(2k, k), C(3k, k), ..., C((k+1)k, k)) = 1`. Both sequences are increasing, so this is
   stated as: `m ∈ A051283` iff `m = k + 1` for some `k ∈ A080170`.

Status of 3: the entry A080170 says (Michael De Vlieger, Jun 29 2026) that the main result of
Guo et al. is a proof of this conjecture, with a Lean formalization in the paper.

A python3 check: 1 and 2 hold for `k ≤ 1200`, 3 holds for `k < 400`; the literal definition of
A354933 used here matches the entry's data (and Jianing Song's characterization) for `n < 800`.
The Lean kernel (`decide`) confirms `A354933 0, ..., A354933 29` against the data and that the
A080170 condition holds at `k = 29` and fails at `k = 28`.
-/

namespace OMA.S_oeis_a051283

/-- A034699: the largest prime power factor of `k` (`1` for `k = 1`; `0` for `k = 0`). -/
def A034699 (k : ℕ) : ℕ := k.primeFactors.sup (fun p => p ^ k.factorization p) ⊔ (if k = 0 then 0 else 1)

/-- Membership in A051283: `P < k / P` with `P` the largest prime power factor of `k`. -/
def InA051283 (k : ℕ) : Prop := 1 ≤ k ∧ A034699 k < k / A034699 k

/-- A346418: the exponent of the largest power of `k` dividing `lcm(1, ..., k)`; `A346418(1) = 1`. -/
noncomputable def A346418 (k : ℕ) : ℕ := if k = 1 then 1 else multiplicity k ((Finset.Icc 1 k).lcm id)

/-- A354933: `n / c`, `c` the largest divisor of `n` coprime to a larger divisor of `n`;
`A354933(1) = 1`. -/
def A354933 (n : ℕ) : ℕ :=
  if n = 1 then 1 else
    n / (n.divisors.filter (fun d => ∃ e ∈ n.divisors, d < e ∧ Nat.Coprime d e)).sup id

/-- Membership in A080170: `k ≥ 1` and `gcd_{j = 2}^{k + 1} C(j k, k) = 1`. -/
def InA080170 (k : ℕ) : Prop :=
  1 ≤ k ∧ (Finset.Icc 2 (k + 1)).gcd (fun j => (j * k).choose k) = 1

/-- The three conjectured characterizations of A051283 recorded in the entry. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → (InA051283 k ↔ 1 < A346418 k)) ∧
    (∀ k : ℕ, 1 ≤ k → (InA051283 k ↔ A034699 k < A354933 k)) ∧
    (∀ m : ℕ, InA051283 m ↔ ∃ k, InA080170 k ∧ m = k + 1) := by
  sorry

end OMA.S_oeis_a051283

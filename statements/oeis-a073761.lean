import Mathlib

/-!
# A073761: Primitive numbers whose decimal expansion of 1/n is equidistributed in base 10.

Source: https://oeis.org/A073761
Credit: @Solfanbtc

`digit n i = ⌊10^i / n⌋ mod 10` is the `i`-th digit (`i ≥ 1`) after the decimal point of `1/n`.
The expansion of `1/n` is *equidistributed* (`Equi n`) when its repeating block contains each of
the digits `0, …, 9` equally often. This is stated as: for some `s` and some `L > 0`, the digit
sequence is periodic with period `L` from position `s + 1` on, and each digit occurs exactly
`L / 10` times among positions `s+1, …, s+L`. This does not depend on the choice of `s` and
`L`: any such block is a cyclic shift of copies of the minimal repetend. Terminating expansions
(repetend `0`) are not equidistributed. A term is an equidistributed `n` that is a multiple of no
earlier term ("primitive"). This is the same as saying that no proper divisor of `n` is
equidistributed, since the least equidistributed divisor of `n` is a term.

The entry's Mathematica program only treats purely periodic `1/n`, but the comment
(Jianing Song) lists even terms (25064, 72728), so the repetend reading is the one used. Checked
with python3: this definition reproduces the b-file (terms up to 100000) except for one extra
number, 84832 = 2^5 * 11 * 241. That number is genuinely equidistributed under this reading: its
repetend has length 30 and starts after a preperiod of 5 digits, with each digit 3 times. It has
no equidistributed proper divisor. The b-file seems to have missed it.

Conjectures (Jianing Song, 2022), both stated in `main`:
1. If `p` is a prime (coprime to 10, so that `ord(10, p)` exists) with `10 ∣ ord(10, p)`, then
   `p` is a term iff `10` is a primitive root mod `p`, i.e. `ord(10, p) = p - 1`.
2. If `m` is a term with `bigomega(m) = 2`, then `m = p * q` with primes `p ≡ 1 (mod 10)`,
   `q ≡ 9 (mod 10)`, `gcd(p-1, q-1) = 2`, `ord(10, p) = (p-1)/2` and `ord(10, q) = q - 1`.
Both were checked with python3 for all `p, m < 100000` (no counterexample, as the entry says).
The entry's final question (is there an odd term with `bigomega > 2`?) is a question, not a
conjecture, and is not stated.
-/

namespace OMA.S_oeis_a073761

/-- The `i`-th digit after the decimal point of `1/n` (`i ≥ 1`). -/
def digit (n i : ℕ) : ℕ := 10 ^ i / n % 10

/-- The decimal expansion of `1/n` is equidistributed: some repeating block of it contains each
digit `0..9` the same number of times. -/
def Equi (n : ℕ) : Prop :=
  ∃ s L : ℕ, 0 < L ∧ (∀ i, s < i → digit n (i + L) = digit n i) ∧
    ∀ d < 10, 10 * ((Finset.Ioc s (s + L)).filter (fun i => digit n i = d)).card = L

/-- `n` is a term of A073761: equidistributed and not a multiple of an earlier term. -/
def IsTerm (n : ℕ) : Prop := Equi n ∧ ∀ d, d ∣ n → d < n → ¬ Equi d

/-- Jianing Song's two conjectures. -/
theorem main :
    (∀ p : ℕ, p.Prime → Nat.Coprime 10 p → 10 ∣ orderOf (10 : ZMod p) →
      (IsTerm p ↔ orderOf (10 : ZMod p) = p - 1)) ∧
    (∀ m : ℕ, IsTerm m → m.primeFactorsList.length = 2 →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q ∧ p % 10 = 1 ∧ q % 10 = 9 ∧
        Nat.gcd (p - 1) (q - 1) = 2 ∧ orderOf (10 : ZMod p) = (p - 1) / 2 ∧
        orderOf (10 : ZMod q) = q - 1) := by
  sorry

end OMA.S_oeis_a073761

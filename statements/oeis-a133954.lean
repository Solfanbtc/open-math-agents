import Mathlib

/-!
# A133954: evil minus odious multiples of p_n below 2^(p_n)

Source: https://oeis.org/A133954 (see also https://oeis.org/A001122, https://oeis.org/A139035)
Credit: @Solfanbtc

For a prime `p`, `a(p)` is the number of nonnegative evil multiples of `p` below `2^p` minus the
number of nonnegative odious multiples of `p` below `2^p` (evil: even number of 1's in binary,
odious: odd number; `0` is evil). The entry indexes by `n` with `p = p_n`, offset 2:
3, 5, -7, 11, 13, 697, ... (`p = 3, 5, 7, ...`).

Known (Shevelev, 2007): 1) if 2 is a primitive root mod `p` then `a = p`; 2) if 2 is a
semiprimitive root mod `p` then `a = -p`. Here (definition in A139035) `r` is a semiprimitive root
mod `p` when `r` has order `(p-1)/2` mod `p` and no power of `r` is `≡ -1 (mod p)` (for `r = 2`
these are the primes `p ≡ 3 (mod 4)` with primitive root `-2`, A139035).

Conjecture (entry comment, from Gerbicz's computations up to `a(46)`): the converse statements are
true as well: `a = p` implies that 2 is a primitive root mod `p`, and `a = -p` implies that 2 is
a semiprimitive root mod `p`. We state exactly these two converses, for every prime `p`
(for `p = 2`, `a = 0`, so both are vacuous).

Sanity check (python, digit DP over the bits of `m < 2^p` tracking `m mod p` and the parity of
the binary weight): this definition gives all 33 listed terms, and both converses (indeed both
equivalences) hold for every prime `p < 1500`.
-/

namespace OMA.S_oeis_a133954

/-- Evil: even binary weight. -/
def IsEvil (m : ℕ) : Bool := (Nat.digits 2 m).count 1 % 2 == 0

/-- Multiples of `p` in `[0, 2^p)`. -/
def mults (p : ℕ) : Finset ℕ := (Finset.range (2 ^ p)).filter (fun m => p ∣ m)

/-- `a(p)`: number of evil minus number of odious multiples of `p` below `2^p`. -/
def a (p : ℕ) : ℤ :=
  ((mults p).filter (fun m => IsEvil m)).card - ((mults p).filter (fun m => !IsEvil m)).card

/-- 2 is a semiprimitive root mod `p`: order `(p-1)/2` and no power of 2 is `-1`. -/
def IsSemiprimitiveRootTwo (p : ℕ) : Prop :=
  orderOf (2 : ZMod p) = (p - 1) / 2 ∧ ∀ x : ℕ, (2 : ZMod p) ^ x ≠ -1

/-- The conjectured converses of Shevelev's two theorems. -/
theorem main : ∀ p : ℕ, p.Prime →
    (a p = p → orderOf (2 : ZMod p) = p - 1) ∧
    (a p = -(p : ℤ) → IsSemiprimitiveRootTwo p) := by
  sorry

end OMA.S_oeis_a133954

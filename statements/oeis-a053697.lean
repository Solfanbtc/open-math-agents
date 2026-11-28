import Mathlib

/-!
# A053697: Base-11 "add the digitwise inverses mod 11" iteration.

Source: https://oeis.org/A053697
Credit: @Solfanbtc

a(n+1) = a(n) + a^(n), where the addition is in base 11 and a^(n) is obtained from a(n) by
replacing each digit with its multiplicative inverse modulo 11 (zero digits, if any, deleted).
The data (a(1) = 1) are the base-11 digit strings 1, 2, 8, 14, 27, 94, 137, 284, 947, 1384, ...

Conjecture (John W. Layman, in the entry): for any positive integer a(1), the sequence
eventually cycles through the forms a(k) = [1][4^a][3][(84)^b], ..., a(k+6) =
[1][4^a][3][(84)^(b+1)], or through a(k) = [1][5^a][4][(84)^b], ..., a(k+6) =
[1][5^a][4][(84)^(b+1)], for nonnegative integers a and b.

Conventions.
* Numbers are natural numbers; their base-11 digits come from `Nat.digits 11` (least significant
  first). a^ keeps the order of the nonzero digits, replacing each digit d by d^9 mod 11 (its
  inverse mod 11, by Fermat), and reads the result in base 11.
* [1][4^a][3][(84)^b] is the base-11 number whose digits, most significant first, are 1, then
  a digits 4, then 3, then b copies of the block 8, 4 (similarly with 5 and 4).
* "Eventually cycles through the forms" is stated as: there are k, a, b and a family (first or
  second) such that g^[k + 6j](x) = Form(a, b + j) for every j ≥ 0 (the six-step pattern
  continues forever; the intermediate terms are not specified by the source).
* The entry's further formulas (Barker's recurrence and g.f. for the decimal reading of the
  a(1) = 1 sequence) are stated there to follow from Israel's explicit formulas; they are not
  part of this statement.
* python3: every start 1 ≤ x < 2000 enters one of the two patterns (checked for 3 further
  periods).
-/

namespace OMA.S_oeis_a053697

/-- a^: digits replaced by their inverses mod 11, zero digits deleted (read in base 11). -/
def hat (x : ℕ) : ℕ :=
  Nat.ofDigits 11 (((Nat.digits 11 x).filter (· ≠ 0)).map fun d => d ^ 9 % 11)

/-- The iteration a ↦ a + a^. -/
def g (x : ℕ) : ℕ := x + hat x

/-- The base-11 number with digits (most significant first) `ds`. -/
def ofDigitsMSB (ds : List ℕ) : ℕ := Nat.ofDigits 11 ds.reverse

/-- Form [1][4^a][3][(84)^b] (t = false) or [1][5^a][4][(84)^b] (t = true). -/
def form (t : Bool) (a b : ℕ) : ℕ :=
  if t then ofDigitsMSB ([1] ++ List.replicate a 5 ++ [4] ++ (List.replicate b [8, 4]).flatten)
  else ofDigitsMSB ([1] ++ List.replicate a 4 ++ [3] ++ (List.replicate b [8, 4]).flatten)

theorem main : ∀ x : ℕ, 1 ≤ x →
    ∃ (t : Bool) (k a b : ℕ), ∀ j : ℕ, g^[k + 6 * j] x = form t a (b + j) := by
  sorry

end OMA.S_oeis_a053697

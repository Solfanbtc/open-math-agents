import Mathlib

/-!
# A087594: Define dd(n) = the number formed by concatenating the absolute difference of successive digits. Sequence contains primes p such that dd(p)=q is a prime, dd(q) is also a prime = r and so on until a single-digit prime (2,3,5,7) arises. (Primes in which the number formed by successive digit differences are primes at every step until a single-digit prime is obtained.).

Source: https://oeis.org/A087594
Credit: @Solfanbtc

`dd n` is the number whose decimal digits, read from the most significant end, are the absolute
differences of successive decimal digits of `n` (leading zeros vanish, as with Mathematica's
`FromDigits`: `dd 1103 = 13`; `dd` of a one-digit number is 0). A prime `p` is a member when the
iterates `dd p, dd (dd p), …` are prime up to and including the first one-digit iterate. Since
`dd` of a one-digit number is 0 (not prime), this is: for some `k`, the iterates
`dd^[1] p, …, dd^[k+1] p` are all prime and `dd^[k+1] p < 10`. One-digit primes are not members
(`dd p = 0`). Checked with python3: this gives exactly the listed terms 13, 29, 31, ..., 1663.

Conjecture (A. Murthy): the sequence is infinite. `main` states this.
-/

namespace OMA.S_oeis_a087594

/-- Absolute differences of successive digits, concatenated. -/
def dd (n : ℕ) : ℕ :=
  let L := (Nat.digits 10 n).reverse
  Nat.ofDigits 10 (List.zipWith (fun a b => (a - b) + (b - a)) L L.tail).reverse

/-- A087594 as a set. -/
def S : Set ℕ :=
  {p | p.Prime ∧ ∃ k : ℕ, (∀ i ≤ k, (dd^[i + 1] p).Prime) ∧ dd^[k + 1] p < 10}

theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a087594

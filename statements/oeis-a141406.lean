import Mathlib

/-!
# A141406: Numbers n where the sum of all of its divisors < sqrt(n) exceeds the sum of all the divisors of m < sqrt(m) for all m<n.

Source: https://oeis.org/A141406 (Robert G. Wilson v, 2008; conjecture by J. Lowell,
Aug 05 2020; OEIS Foundation, CC BY-SA 4.0). Companion sequence: A141037 (same with
divisors ≤ sqrt).
Credit: @Solfanbtc

* A141406: numbers n ≥ 1 such that the sum of the divisors d of n with d < sqrt(n) exceeds the
  corresponding sum for every m < n.
* A141037: numbers n ≥ 1 such that the sum of the divisors d of n with d ≤ sqrt(n) exceeds the
  corresponding sum for every m < n.

Conjecture (OEIS): 3600 is the largest number that belongs to exactly one of A141406 and
A141037.

Formalization notes.
* d < sqrt(n) is written d * d < n and d ≤ sqrt(n) is written d * d ≤ n (equivalent for natural
  numbers).
* Both sequences have offset 1 and are record positions among the positive integers, so the
  comparison runs over 1 ≤ m < n (n = 1 is a term of both, vacuously).
* "The largest number in exactly one of them" is `IsGreatest` of the symmetric difference.
* A python computation up to 2·10^6 reproduces the listed terms of both sequences and finds the
  symmetric difference {2, 4, 6, 9, 16, 20, 36, 40, 48, 144, 168, 3600} there.
-/

namespace OMA.S_oeis_a141406

/-- Sum of the divisors d of n with d < sqrt(n). -/
def sumBelow (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => d * d < n), d

/-- Sum of the divisors d of n with d ≤ sqrt(n). -/
def sumAtMost (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), d

/-- n is a term of A141406. -/
def InA141406 (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → sumBelow m < sumBelow n

/-- n is a term of A141037. -/
def InA141037 (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → sumAtMost m < sumAtMost n

theorem main : IsGreatest {n : ℕ | Xor (InA141406 n) (InA141037 n)} 3600 := by
  sorry

end OMA.S_oeis_a141406

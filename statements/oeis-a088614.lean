import Mathlib

/-!
# A088614: alternate primes and composites, every partial concatenation prime.

Source: https://oeis.org/A088614
Credit: @Solfanbtc

A088614 is built greedily: `a(n)` is the smallest number not included earlier such that `a(n)`
is prime for odd `n` and composite for even `n`, and the decimal concatenation
`a(1) ‖ a(2) ‖ … ‖ a(n)` is prime (`2, 29, 293, 29327, …`). `state i` is the pair
(list of the first `i` terms, their concatenation). The next term is the least admissible
candidate (an `sInf`; the conjecture presupposes that one always exists). Checked with
python3: this greedy rule reproduces the 38 listed terms.

Conjecture (entry): "1 and 5 are the only two odd nonmembers." Taken literally this fails for a
trivial reason: no term after the first can end in the digit 5 (the concatenation would be a
multiple of 5 greater than 5), so `15, 25, 35, …` are never members either. Likewise `1` is
neither prime nor composite, and `5` cannot occur for the same reason. Minimal fix, keeping
the intended content: the odd nonmembers are exactly `1` and the odd multiples of `5`. So an
odd `n` is a member iff `n ≠ 1` and `5 ∤ n`. (Python3: after 160 terms, many such `n`, e.g.
`7`, have not appeared yet, so the conjecture is far from settled numerically.)
-/

namespace OMA.S_oeis_a088614

/-- Decimal concatenation `P ‖ c` (for `c ≥ 1`). -/
def cat (P c : ℕ) : ℕ := P * 10 ^ (Nat.digits 10 c).length + c

/-- `c` has the required type at position `i` (1-indexed): prime if `i` is odd, composite if
`i` is even. -/
def Admissible (i c : ℕ) : Prop := if Odd i then c.Prime else (1 < c ∧ ¬ c.Prime)

/-- `state i = ([a(1), …, a(i)], a(1) ‖ … ‖ a(i))`. -/
noncomputable def state : ℕ → List ℕ × ℕ
  | 0 => ([], 0)
  | i + 1 =>
    let s := state i
    let c := sInf {c : ℕ | c ∉ s.1 ∧ Admissible (i + 1) c ∧ (cat s.2 c).Prime}
    (s.1 ++ [c], cat s.2 c)

/-- `n` is a member of A088614. -/
def Member (n : ℕ) : Prop := ∃ i : ℕ, n ∈ (state i).1

/-- The conjecture (with the minimal fix above): the odd members are exactly the odd `n ≠ 1`
not divisible by `5`. -/
theorem main : ∀ n : ℕ, Odd n → (Member n ↔ n ≠ 1 ∧ ¬ 5 ∣ n) := by
  sorry

end OMA.S_oeis_a088614

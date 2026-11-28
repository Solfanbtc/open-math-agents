import Mathlib

/-!
# A078616: a(n) = Sum_{k=0..n} A010815(k).

Source: https://oeis.org/A078616
Credit: @Solfanbtc

A010815(k) is the coefficient of `q^k` in `∏_{m ≥ 1} (1 - q^m)`. Expanding the product, this
is `Σ (-1)^(number of parts)` over the partitions of `k` into distinct parts, which is how it
is defined below (Mathlib's `Nat.Partition.distincts`). `a(n) = Σ_{k=0}^{n} A010815(k)`.

Comment (George Beck, May 05 2017; corrected by Ilya Gutkovskiy, Aug 18 2018), marked
"conjectured": "a(n) = (Number of ones in the distinct partitions of n with an odd number of
parts) - (number of ones in the distinct partitions of n with an even number of parts). The
partial sums give A246575."

Index. Let `b(n)` be the right-hand side. Read literally, `a(n) = b(n)` already fails at
`n = 0` (`a(0) = 1`, `b(0) = 0`: the empty partition has no ones) and at `n = 1` (`a(1) = 0`,
`b(1) = 1`). Python gives `b(0..20) = 0, 1, 0, -1, -1, -1, 0, 0, 1, 1, 1, 1, 1, 0, …`, which is
the data of A078616 shifted by one: `b(n) = a(n-1)` for `n ≥ 1`. The partial sums of `b`
(`0, 1, 1, 0, -1, -2, -2, …`) are exactly the data of A246575, as the comment says, while the
partial sums of `a` are not (they start `1, 1, 0, …`). So the comment's sequence is `b`, with
`b(n) = a(n-1)`, and that is the minimal fix stated here. (The partial-sum claim then follows
from the generating function of A246575.)

Status: the identity follows from generating functions. Since a distinct partition contains at
most one `1`, `Σ_n b(n) x^n = x ∏_{k ≥ 2} (1 - x^k) = x η(x)/(1 - x)`, and `η(x)/(1 - x)` is the
g.f. of A078616 (Benoit Cloitre). The entry still labels it "conjectured".
-/

namespace OMA.S_oeis_a078616

/-- A010815(k): coefficient of `q^k` in `∏ (1 - q^m)`, as the signed count of distinct
partitions. -/
def e (k : ℕ) : ℤ := ∑ p ∈ Nat.Partition.distincts k, (-1) ^ p.parts.card

/-- A078616. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), e k

/-- Number of ones in the distinct partitions of `n` with an odd number of parts, minus the same
count for an even number of parts. -/
def b (n : ℕ) : ℤ :=
  (∑ p ∈ (Nat.Partition.distincts n).filter (fun p => Odd p.parts.card),
      (p.parts.count 1 : ℤ)) -
    ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => Even p.parts.card), (p.parts.count 1 : ℤ)

theorem main : ∀ n : ℕ, 1 ≤ n → b n = a (n - 1) := by
  sorry

end OMA.S_oeis_a078616

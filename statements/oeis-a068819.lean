import Mathlib

/-!
# A068819: n! is divisible by the product of the integers strictly between n and the next prime

Source: https://oeis.org/A068819
Credit: @Solfanbtc

A068819: `a(n) = n!/((n+1)(n+2)⋯(n+k))` where `k` is the largest value giving an integer
quotient. The entry's comment (A. Murthy): "n! is divisible by all the numbers from n+1 to n+k
where n+k+1 is the smallest prime greater than n. Conjecture: For n > 3 n! is divisible by
product(n+k,n) = (n+1)(n+2)...(n+k)."

So with `p` the smallest prime greater than `n` (and `k = p - n - 1`), the conjecture is:
for `n > 3`, `(n+1)(n+2)⋯(p-1) ∣ n!`, the product being over `Finset.Ioo n p` (empty, hence
`1`, when `p = n + 1`). The bound `n > 3` is needed: for `n = 3`, `p = 5` and `4 ∤ 3! = 6`.
Checked with python3 for `4 ≤ n ≤ 3000`.
-/

namespace OMA.S_oeis_a068819

/-- Murthy's conjecture: for `n > 3` and `p` the smallest prime greater than `n`,
`(n+1)(n+2)⋯(p-1)` divides `n!`. -/
theorem main : ∀ n : ℕ, 3 < n → ∀ p : ℕ, IsLeast {q : ℕ | q.Prime ∧ n < q} p →
    (∏ m ∈ Finset.Ioo n p, m) ∣ n.factorial := by
  sorry

end OMA.S_oeis_a068819

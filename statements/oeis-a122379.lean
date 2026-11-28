import Mathlib

/-!
# A122379: n^2 < P(n)! for almost all n

Source: https://oeis.org/A122379
A122379 lists the `n` with `S(n)! > n^2 > P(n)!`, where `S(n)!` is the smallest factorial
divisible by `n` and `P(n)` is the greatest prime factor of `n`: 4, 9, 16, 18, 25, ...
The entry's comment: "It is conjectured that n^2 < P(n)! for almost all n. It is known that
S(n) = P(n) for almost all n."

We state the conjecture: the set of `n` with `n^2 < P(n)!` has natural density 1, i.e.
`#{1 ≤ n ≤ x : n^2 < P(n)!} / x → 1`.
Conventions. `P(n)` is the largest element of `n.primeFactors` (`P(1) = 0`, and `1^2 < 0! = 1`
fails, which does not affect the density). "Almost all" is read as natural density 1.
Remark: this looks provable from the smooth-number estimate `Ψ(x, (log x)^2) = o(x)`, since
`P(n) > (log n)^2` already gives `P(n)! > n^2` for large `n`; it is stated as the source poses it.
Checked with python3: the proportion of `n ≤ x` with `n^2 < P(n)!` is 0.871, 0.9635, 0.98894,
0.996636 for `x = 10^3, ..., 10^6`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a122379

open Filter Topology

/-- The greatest prime factor of `n` (`0` for `n = 1`). -/
def P (n : ℕ) : ℕ := n.primeFactors.sup id

theorem main :
    Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n => n ^ 2 < (P n).factorial)).card : ℝ) / x)
      atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a122379

import Mathlib

/-!
# A087817: a(n) = a(a(a(n-1)))+a(n-a(n-1)) with a(1)=a(2)=1.

Source: https://oeis.org/A087817
Credit: @Solfanbtc

`a(1) = a(2) = 1` and `a(n) = a(a(a(n-1))) + a(n - a(n-1))` for `n ≥ 3`. The recursion only
calls earlier positions (computed to `n = 10^7`, where `1 ≤ a(k) < k` for `2 < k`), so it
determines the sequence. We quantify over any `a : ℕ → ℕ` satisfying it (the value at `0` is
irrelevant). This reproduces the data (Python).

Conjecture (Benoit Cloitre, Jun 05 2004): `a(n)` is asymptotic to `n^c` with `c = 0.677...`.
Stated with the standard meaning of "asymptotic to" (`a(n) / n^c → 1`), for some `c` whose
decimal expansion starts `0.677` (`0.677 ≤ c < 0.678`).

Numerical remark: `log a(n) / log n` is `0.6771` at `n = 10^4`, `0.6738` at `10^5`, `0.6698` at
`10^6` and `0.6667` at `10^7`, and the local exponent `log_10 (a(10n)/a(n))` is about `0.648` for
`n = 10^6`. So the data seem to drift below `0.677`, and the conjecture may well be false.
-/

namespace OMA.S_oeis_a087817

theorem main : ∀ a : ℕ → ℕ, a 1 = 1 → a 2 = 1 →
    (∀ n : ℕ, 3 ≤ n → a n = a (a (a (n - 1))) + a (n - a (n - 1))) →
    ∃ c : ℝ, 0.677 ≤ c ∧ c < 0.678 ∧
      Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

end OMA.S_oeis_a087817

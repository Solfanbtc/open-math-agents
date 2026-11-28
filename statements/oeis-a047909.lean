import Mathlib

/-!
# A047909: Array read by antidiagonals upwards: h(n,k) = number of sequences with n copies each of 1,2,...,k and longest increasing subsequence of length k

Source: https://oeis.org/A047909
Credit: @Solfanbtc

Conjectures (OEIS A047909, comments, Vaclav Kotesovec, Feb 21 2016):
* Column k > 1 is asymptotic to k^(k*n + 1/2) / (2*Pi*n)^((k-1)/2).
* Row k > 1 is asymptotic to sqrt(k) * (k^k/(k-1)!)^n * n^((k-1)*n) / exp((k-1)*(n+1)).

Conventions:
* `h n k` counts the words of length `n * k` over the alphabet `{0, ..., k-1}` (standing for
  `1, ..., k`) in which every letter occurs exactly `n` times and which have a strictly
  increasing subsequence of length `k`. No strictly increasing subsequence can be longer than
  `k` (there are only `k` letters), so this is the same as the longest increasing subsequence
  having length `k`.
* Row n of the array is `k ↦ h n k` and column k is `n ↦ h n k` (the entry lists rows
  1, 5, 47, 641, 11389 for n = 2 and columns such as A030662 = 1, 5, 19, 69, ... for k = 2).
  In the second conjecture the letter k names the fixed row index (the number of copies of
  each letter) and n the varying number of letters; in the statement these are `c` and `m`.
  Both readings were checked against the listed data: the column formula for k = 2 is the
  asymptotic 4^n / sqrt(Pi n) of binomial(2n, n) - 1, and the row formula gives about 11218
  for h(2, 5) = 11389 and about 4.66e7 for h(3, 5) = 50775091.
* `~` is `Asymptotics.IsEquivalent` along `atTop`; the powers with real exponents are `rpow`.
-/

namespace OMA.S_oeis_a047909

open Filter Real

/-- `h n k`: the number of words with `n` copies of each of `k` letters that have a strictly
increasing subsequence of length `k`. -/
noncomputable def h (n k : ℕ) : ℕ :=
  Nat.card {w : Fin (n * k) → Fin k //
    (∀ i : Fin k, (Finset.univ.filter fun j => w j = i).card = n) ∧
    ∃ g : Fin k → Fin (n * k), StrictMono g ∧ StrictMono (w ∘ g)}

/-- Both conjectured asymptotics: every column `k > 1` and every row `c > 1`. -/
theorem main :
    (∀ k : ℕ, 1 < k →
      Asymptotics.IsEquivalent atTop (fun n : ℕ => (h n k : ℝ))
        (fun n : ℕ => (k : ℝ) ^ ((k : ℝ) * n + 1 / 2) /
          (2 * π * n) ^ (((k : ℝ) - 1) / 2))) ∧
    (∀ c : ℕ, 1 < c →
      Asymptotics.IsEquivalent atTop (fun m : ℕ => (h c m : ℝ))
        (fun m : ℕ => √(c : ℝ) * ((c : ℝ) ^ c / ((c - 1).factorial : ℝ)) ^ m *
          (m : ℝ) ^ (((c : ℝ) - 1) * m) / exp (((c : ℝ) - 1) * (m + 1)))) := by
  sorry

end OMA.S_oeis_a047909

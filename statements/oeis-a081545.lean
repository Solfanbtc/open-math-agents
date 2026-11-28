import Mathlib

/-!
# A081545: Smallest prime which is 1 more than the product of n distinct composite numbers.

Source: https://oeis.org/A081545
Credit: @Solfanbtc

Conjecture (M. F. Hasler, Jun 16 2007, in the entry): "Let K(m) be the smallest possible K
satisfying the Theorem. Conjecture: K(m) ~ m, i.e., a(k) ~ A002808(1)*...*A002808(k), only very
few of the last factors will be insignificantly larger."

Conventions.
* A002808: the composite numbers 4, 6, 8, 9, 10, ...; `c i` below is A002808(i+1) (0-based).
* a(k) is the least prime of the form 1 + (product of k distinct composite numbers); a(0) = 2
  (empty product). The set is nonempty for every k (it is the content of the entry's
  computation), and `sInf` returns this least element.
* The conjecture is stated in the explicit form given after "i.e.":
  a(k) ~ c(1)·c(2)·…·c(k) as k → ∞ (asymptotic equivalence, ratio → 1). The auxiliary form
  "K(m) ~ m" depends on the Theorem of the entry ("a(k) - 1 is divisible by the first m
  composite numbers" for k > K), whose divisibility notion is not made precise there; the
  entry itself presents the product asymptotic as the meaning of the conjecture.
* Data check (python3): a(k)/(c(1)⋯c(k)) for k = 0..17 is
  2, 1.25, 1.54, 1.005, 1.25, 1.33, 1.17, 1.0000003, 1.29, 1.375, 1.43, 1.000000000004,
  1.048, 1.227, 1.042, 1.3, 1.0, 1.077.
-/

namespace OMA.S_oeis_a081545

open Filter Asymptotics

/-- `n` is composite. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- A002808, 0-based: `c 0 = 4`, `c 1 = 6`, `c 2 = 8`, `c 3 = 9`, .... -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth IsComposite i

/-- A081545: the least prime equal to 1 + a product of `k` distinct composite numbers. -/
noncomputable def a (k : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ S : Finset ℕ, S.card = k ∧ (∀ x ∈ S, IsComposite x) ∧
    p = (∏ x ∈ S, x) + 1}

theorem main :
    (fun k : ℕ => (a k : ℝ)) ~[atTop] fun k : ℕ => ((∏ i ∈ Finset.range k, c i : ℕ) : ℝ) := by
  sorry

end OMA.S_oeis_a081545

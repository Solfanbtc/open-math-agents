import Mathlib

/-!
# A112826: Goldbach gaps that never occur

Source: https://oeis.org/A112826 (with https://oeis.org/A112825)
For an even `k ≥ 4`, the Goldbach gap of `k` is `q - p`, where `p` is the least prime with
`k - p` prime and `q` is the largest prime `≤ k/2` with `k - q` prime (the entries' Mathematica
function `f`; e.g. `10 = 3 + 7 = 5 + 5` has gap `5 - 3 = 2`). A112825(n) is the least even `k`
with Goldbach gap `2n`, or 0 if none exists; A112826 lists the gaps `2n` with A112825(n) = 0:
58, 62, 82, 88, 108, ... "It is conjectured that there does not exist a Goldbach partition
yielding a Goldbach 'gap' of n as defined, for n=58,62,82,...."

We state the conjecture for all 52 listed values `g`: no even `k` has Goldbach gap `g`. To avoid
presupposing Goldbach's conjecture, the gap is spoken of through its witnesses: there are no `k`,
`p`, `q` such that `p` is the least prime with `k - p` prime, `q` is the largest prime `≤ k/2` with
`k - q` prime, and `q - p = g`. (When `k` has a Goldbach partition, `p ≤ q` both exist and are
unique.)
Checked with python3: for all even `4 ≤ k ≤ 2·10^6`, the even gaps up to 412 that never occur are
exactly the 52 listed values.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a112826

/-- `p` is the least prime with `k - p` prime. -/
def IsLeastPart (k p : ℕ) : Prop :=
  p.Prime ∧ p ≤ k ∧ (k - p).Prime ∧ ∀ r < p, r.Prime → ¬ (k - r).Prime

/-- `q` is the largest prime `≤ k/2` with `k - q` prime. -/
def IsLargestPart (k q : ℕ) : Prop :=
  q.Prime ∧ 2 * q ≤ k ∧ (k - q).Prime ∧ ∀ r, q < r → 2 * r ≤ k → r.Prime → ¬ (k - r).Prime

/-- The listed values of A112826. -/
def listed : Finset ℕ :=
  {58, 62, 82, 88, 108, 112, 114, 116, 118, 122, 130, 140, 148, 152, 162, 182, 184, 196, 198,
    200, 202, 212, 214, 218, 240, 242, 244, 250, 254, 256, 258, 262, 272, 282, 284, 292, 296, 298,
    316, 320, 322, 332, 336, 340, 358, 362, 366, 382, 394, 400, 410, 412}

theorem main : ∀ g ∈ listed, ∀ k p q : ℕ, Even k → 4 ≤ k →
    IsLeastPart k p → IsLargestPart k q → q - p ≠ g := by
  sorry

end OMA.S_oeis_a112826

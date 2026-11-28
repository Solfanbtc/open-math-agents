import Mathlib

/-!
# A022553: Number of binary Lyndon words containing n letters of each type

Source: https://oeis.org/A022553
Credit: @Solfanbtc

The entry comments: "Conjecturally, number of irreducible alternating Euler sums of depth `n`
and weight `3n`" (Broadhurst, *On the enumeration of irreducible k-fold Euler sums and their
roles in knot theory and field theory*, arXiv:hep-th/9604128, 1996).

## Conventions

* `A022553 n` is the number of binary Lyndon words with `n` letters of each kind: words
  `w` of length `2n` over `Bool` with exactly `n` letters `true`, strictly smaller
  (lexicographically, `false < true`) than each of their nontrivial rotations
  (`A022553 0 = 1`, the empty word). Lexicographic order on words of equal length is compared
  as the order of their values as binary numbers (`wordVal`).
* An alternating Euler sum is indexed by a list `s = [s₁, …, s_d]` of nonzero integers with
  `s₁ ≠ 1` (convergence):
  `ζ(s) = ∑_{n₁ > n₂ > ⋯ > n_d ≥ 1} ∏ᵢ sgn(sᵢ)^{nᵢ} / nᵢ^{|sᵢ|}`,
  of weight `∑ |sᵢ|` and depth `d`. The outer sum over `n₁` may converge only conditionally
  (when `s₁ = -1`), so the value is defined as the limit of the partial sums with `n₁ ≤ N`.
* "Irreducible of weight `w` and depth `d`" is read in the standard way (Broadhurst; Broadhurst
  and Kreimer): the number of irreducibles is the dimension over `ℚ` of the depth-`d` graded
  piece of the space of indecomposables, i.e.
  `dim_ℚ Z_{w,≤d} / (Z_{w,≤d-1} + (P_w ∩ Z_{w,≤d}))`,
  where `Z_{w,≤d}` is the `ℚ`-span of the alternating Euler sums of weight `w` and depth
  `≤ d`, and `P_w` is the `ℚ`-span of products `a * b` with `a`, `b` in the spans of all
  Euler sums of weights `w₁, w₂ ≥ 1`, `w₁ + w₂ = w`. Below the quotient is written as the
  quotient of `Z_{w,≤d}` by the preimage of `Z_{w,≤d-1} ⊔ P_w`, which is the same thing.
* The claim is stated for `n ≥ 1`: at `n = 0` (weight 0, depth 0) the comment has no content
  (there is no Euler sum of positive depth and weight 0).
-/

namespace OMA.S_oeis_a022553

/-- The word `w` of length `m` read as a binary number, first letter most significant. For
words of the same length this order is the lexicographic order (with `false < true`). -/
def wordVal {m : ℕ} (w : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, (w i).toNat * 2 ^ (m - 1 - (i : ℕ))

/-- The rotation of `w` by `k` positions: `i ↦ w (i + k mod m)`. -/
def rot {m : ℕ} (w : Fin m → Bool) (k : ℕ) : Fin m → Bool :=
  fun i => w ⟨((i : ℕ) + k) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- Number of binary Lyndon words of length `2n` with `n` letters of each type. -/
def A022553 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n) → Bool)).filter (fun w : Fin (2 * n) → Bool =>
    (Finset.univ.filter (fun i => w i = true)).card = n ∧
      ∀ k : ℕ, k < 2 * n → 0 < k → wordVal w < wordVal (rot w k))).card

/-- Partial sums `∑_{N ≥ n₁ > n₂ > ⋯ > n_d ≥ 1} ∏ᵢ sgn(sᵢ)^{nᵢ} / nᵢ^{|sᵢ|}`. -/
noncomputable def partialEuler : List ℤ → ℕ → ℝ
  | [], _ => 1
  | s :: rest, N =>
      ∑ m ∈ Finset.Icc 1 N,
        (if s < 0 then (-1 : ℝ) ^ m else 1) / (m : ℝ) ^ s.natAbs * partialEuler rest (m - 1)

/-- The alternating Euler sum `ζ(s₁, …, s_d)`, as the limit of the partial sums in `n₁`. -/
noncomputable def eulerSum (s : List ℤ) : ℝ :=
  Filter.limUnder Filter.atTop (fun N => partialEuler s N)

/-- Admissible (convergent) signed indices: all entries nonzero, first entry `≠ 1`. -/
def Admissible (s : List ℤ) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧ s.head? ≠ some 1

/-- Weight `∑ |sᵢ|`. -/
def weight (s : List ℤ) : ℕ := (s.map Int.natAbs).sum

/-- `Z_{w,≤d}`: the `ℚ`-span of alternating Euler sums of weight `w` and depth `≤ d`. -/
noncomputable def Z (w d : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ
    {x | ∃ s : List ℤ, Admissible s ∧ weight s = w ∧ s.length ≤ d ∧ x = eulerSum s}

/-- The `ℚ`-span of all alternating Euler sums of weight `w`. -/
noncomputable def ZW (w : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ {x | ∃ s : List ℤ, Admissible s ∧ weight s = w ∧ x = eulerSum s}

/-- `P_w`: the `ℚ`-span of products of Euler sums of positive weights adding up to `w`. -/
noncomputable def P (w : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ
    {x | ∃ w₁ w₂ : ℕ, 1 ≤ w₁ ∧ 1 ≤ w₂ ∧ w₁ + w₂ = w ∧
      ∃ a ∈ ZW w₁, ∃ b ∈ ZW w₂, x = a * b}

/-- Number of irreducible alternating Euler sums of weight `w` and depth `d ≥ 1`:
`dim_ℚ Z_{w,≤d} / (Z_{w,≤d-1} + P_w) ∩ Z_{w,≤d}`. -/
noncomputable def irreducibleCount (w d : ℕ) : ℕ :=
  Module.finrank ℚ ((Z w d) ⧸ (Z w (d - 1) ⊔ P w).comap (Z w d).subtype)

/-- Conjecture (OEIS A022553, after Broadhurst): for every `n ≥ 1`, the number of irreducible
alternating Euler sums of depth `n` and weight `3n` equals `A022553 n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → irreducibleCount (3 * n) n = A022553 n := by
  sorry

end OMA.S_oeis_a022553

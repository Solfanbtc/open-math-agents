import Mathlib

/-!
# A129817: Number of alternating fixed-point-free permutations on n letters.

Source: https://oeis.org/A129817 (conjecture by Vladimir Shevelev, Apr 29 2008; OEIS Foundation,
CC BY-SA 4.0). Related: A129815 (reverse alternating fixed-point-free permutations),
A000111 (Euler up/down numbers).
Credit: @Solfanbtc

Conjecture (OEIS, A129817): for n ≥ 3,
  A000111(2n)/a(2n) < e < A000111(2n)/A129815(2n),
so that A000111(2n)/a(2n) increases while A000111(2n)/A129815(2n) decreases (and both quotients
tend to e).

Formalization notes.
* Permutations of {1, ..., n} are modelled as `Equiv.Perm (Fin n)` (positions and values
  shifted down by one, which preserves fixed points and the relative order of values).
* "Alternating" in A129817 means down-up: σ(1) > σ(2) < σ(3) > ... (Emeric Deutsch's comment;
  example a(4) = 2 from 3142 and 2143). "Reverse alternating" in A129815 means up-down:
  σ(1) < σ(2) > σ(3) < ... (example 3412 and 2413).
* A000111(m) is the number of down-up permutations of m letters (for every m ≥ 0), so `euler m`
  below counts them directly. A python brute force over all permutations of up to 9 letters
  reproduces A000111, A129817 and A129815 with these conventions.
* All claims of the comment are stated, as a conjunction: the two inequalities for n ≥ 3, the
  monotonicity of the two quotients (taken on n ≥ 3, the range given in the comment; note that
  A000111(4)/A129815(4) = 5/2 < A000111(6)/A129815(6) = 61/22, so the decrease fails from
  n = 2 to n = 3), and the convergence of both quotients to e.
-/

namespace OMA.S_oeis_a129817

open Filter Topology

/-- Down-up: σ(0) > σ(1) < σ(2) > ... (0-indexed positions). -/
def IsDownUp {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → (i.val % 2 = 0 → σ j < σ i) ∧ (i.val % 2 = 1 → σ i < σ j)

/-- Up-down: σ(0) < σ(1) > σ(2) < ... (0-indexed positions). -/
def IsUpDown {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → (i.val % 2 = 0 → σ i < σ j) ∧ (i.val % 2 = 1 → σ j < σ i)

/-- No fixed point. -/
def IsFPF {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop := ∀ i, σ i ≠ i

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsDownUp σ) := by
  unfold IsDownUp; infer_instance
instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsUpDown σ) := by
  unfold IsUpDown; infer_instance
instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsFPF σ) := by
  unfold IsFPF; infer_instance

/-- A000111(n): number of down-up (alternating) permutations of n letters. -/
def euler (n : ℕ) : ℕ := (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => IsDownUp σ)).card

/-- A129817(n): number of alternating (down-up) fixed-point-free permutations of n letters. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => IsDownUp σ ∧ IsFPF σ)).card

/-- A129815(n): number of reverse alternating (up-down) fixed-point-free permutations. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => IsUpDown σ ∧ IsFPF σ)).card

/-- A000111(2n)/A129817(2n). -/
noncomputable def lower (n : ℕ) : ℝ := (euler (2 * n) : ℝ) / (a (2 * n) : ℝ)

/-- A000111(2n)/A129815(2n). -/
noncomputable def upper (n : ℕ) : ℝ := (euler (2 * n) : ℝ) / (b (2 * n) : ℝ)

theorem main :
    (∀ n : ℕ, 3 ≤ n → lower n < Real.exp 1 ∧ Real.exp 1 < upper n) ∧
    StrictMonoOn lower (Set.Ici 3) ∧ StrictAntiOn upper (Set.Ici 3) ∧
    Tendsto lower atTop (𝓝 (Real.exp 1)) ∧ Tendsto upper atTop (𝓝 (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a129817

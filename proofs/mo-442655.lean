import OMAStatements.S_mo_442655

open Matrix

namespace OMA.S_mo_442655.Proof

private lemma euclid_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ euclid x :=
  norm_nonneg _

private lemma euclid_sq {n : ℕ} (x : Fin n → ℂ) :
    (euclid x) ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 := by
  unfold euclid
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

private lemma eq_of_sq_eq_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  have h1 : Real.sqrt (a ^ 2) = Real.sqrt (b ^ 2) := congr_arg Real.sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at h1

private lemma le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  have h1 : Real.sqrt (a ^ 2) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hb] at h1
  exact le_trans (le_abs_self a) h1

private lemma euclid_eq_zero {n : ℕ} (x : Fin n → ℂ) : euclid x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsq : ∑ i : Fin n, ‖x i‖ ^ 2 = 0 := by
      rw [← euclid_sq, h, zero_pow two_ne_zero]
    ext i
    have hi : ‖x i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsq i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro rfl
    have hsq : (euclid (0 : Fin n → ℂ)) ^ 2 = 0 := by
      simp [euclid_sq]
    exact sq_eq_zero_iff.mp hsq

private lemma euclid_pos_of_ne_zero {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < euclid x :=
  lt_of_le_of_ne (euclid_nonneg x) (Ne.symm (mt (euclid_eq_zero x).mp hx))

private lemma euclid_smul {n : ℕ} (c : ℂ) (x : Fin n → ℂ) :
    euclid (c • x) = ‖c‖ * euclid x := by
  refine eq_of_sq_eq_sq (euclid_nonneg _) (mul_nonneg (norm_nonneg c) (euclid_nonneg x)) ?_
  rw [mul_pow, euclid_sq, euclid_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

private lemma euclid_star {n : ℕ} (x : Fin n → ℂ) :
    euclid (star x) = euclid x := by
  refine eq_of_sq_eq_sq (euclid_nonneg _) (euclid_nonneg _) ?_
  simp only [euclid_sq, Pi.star_def, norm_star]

private lemma euclid_sub_le {n : ℕ} (x y : Fin n → ℂ) :
    euclid (x - y) ≤ euclid x + euclid y := by
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) - WithLp.toLp 2 y‖ ≤
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ +
    ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖
  exact norm_sub_le _ _

private lemma complex_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

private lemma dotProduct_star_self {n : ℕ} (x : Fin n → ℂ) :
    dotProduct (star x) x = (((euclid x) ^ 2 : ℝ) : ℂ) := by
  rw [euclid_sq, dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [Pi.star_def] using complex_star_mul_self (x i)

private lemma euclid_mulVec_of_conjTranspose_mul_self {n : ℕ} (M : Mat n)
    (hM : Mᴴ * M = 1) (x : Fin n → ℂ) :
    euclid (M *ᵥ x) = euclid x := by
  have hdot : dotProduct (star (M *ᵥ x)) (M *ᵥ x) = dotProduct (star x) x := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hM,
      Matrix.vecMul_one]
  rw [dotProduct_star_self, dotProduct_star_self] at hdot
  exact eq_of_sq_eq_sq (euclid_nonneg _) (euclid_nonneg _) (Complex.ofReal_injective hdot)

private lemma euclid_unitary_mulVec {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℂ) :
    euclid ((U : Mat n) *ᵥ x) = euclid x :=
  euclid_mulVec_of_conjTranspose_mul_self (U : Mat n)
    (Matrix.mem_unitaryGroup_iff'.mp U.2) x

private lemma complex_parallelogram (a b : ℂ) :
    ‖a - b‖ ^ 2 + ‖a + b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

private lemma euclid_parallelogram {n : ℕ} (u v : Fin n → ℂ) :
    (euclid (u - v)) ^ 2 + (euclid (u + v)) ^ 2 = 2 * (euclid u) ^ 2 + 2 * (euclid v) ^ 2 := by
  simp only [euclid_sq]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [Pi.sub_apply, Pi.add_apply] using complex_parallelogram (u i) (v i)

-- Even case upper bound construction

private def swapFinFun {n : ℕ} (hn2 : n % 2 = 0) (i : Fin n) : Fin n :=
  if h : i.val % 2 = 0 then ⟨i.val + 1, by omega⟩ else ⟨i.val - 1, by omega⟩

private lemma swapFinFun_invol {n : ℕ} (hn2 : n % 2 = 0) (i : Fin n) :
    swapFinFun hn2 (swapFinFun hn2 i) = i := by
  ext
  unfold swapFinFun
  by_cases hi : i.val % 2 = 0
  · simp only [hi, ↓reduceDIte]
    have hne : ¬ (i.val + 1) % 2 = 0 := by omega
    simp only [hne, ↓reduceDIte]
    omega
  · simp only [hi, ↓reduceDIte]
    have hev : (i.val - 1) % 2 = 0 := by omega
    simp only [hev, ↓reduceDIte]
    omega

private def swapFin {n : ℕ} (hn2 : n % 2 = 0) : Fin n ≃ Fin n where
  toFun := swapFinFun hn2
  invFun := swapFinFun hn2
  left_inv := swapFinFun_invol hn2
  right_inv := swapFinFun_invol hn2

private lemma swapFin_swapFin {n : ℕ} (hn2 : n % 2 = 0) (i : Fin n) :
    swapFin hn2 (swapFin hn2 i) = i :=
  swapFinFun_invol hn2 i

private def sgnFin {n : ℕ} (i : Fin n) : ℂ :=
  if i.val % 2 = 0 then -1 else 1

private lemma star_sgnFin {n : ℕ} (i : Fin n) : star (sgnFin i) = sgnFin i := by
  unfold sgnFin
  split_ifs <;> simp

private lemma sgnFin_mul_self {n : ℕ} (i : Fin n) : sgnFin i * sgnFin i = 1 := by
  unfold sgnFin
  split_ifs <;> norm_num

private def skewMat {n : ℕ} (hn2 : n % 2 = 0) : Mat n :=
  Matrix.of fun i j => if j = swapFin hn2 i then sgnFin i else 0

private lemma skewMat_mem_unitary {n : ℕ} (hn2 : n % 2 = 0) :
    skewMat hn2 ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i k
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, skewMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (swapFin hn2 i)]
  · simp only [↓reduceIte]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, star_sgnFin, sgnFin_mul_self]
    · have hne : swapFin hn2 i ≠ swapFin hn2 k := fun h => hik ((swapFin hn2).injective h)
      simp only [hik, hne, ↓reduceIte, star_zero, mul_zero]
  · intro j _ hj
    simp only [hj, ↓reduceIte, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma skewMat_mulVec {n : ℕ} (hn2 : n % 2 = 0) (x : Fin n → ℂ) (i : Fin n) :
    (skewMat hn2 *ᵥ x) i = sgnFin i * x (swapFin hn2 i) := by
  simp only [Matrix.mulVec, dotProduct, skewMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (swapFin hn2 i)]
  · simp only [↓reduceIte]
  · intro j _ hj
    simp only [hj, ↓reduceIte, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma pair_norm_sq_even (a b : ℂ) :
    ‖a - (-1 : ℂ) * star b‖ ^ 2 + ‖b - (1 : ℂ) * star a‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma pair_norm_sq_odd (a b : ℂ) :
    ‖a - (1 : ℂ) * star b‖ ^ 2 + ‖b - (-1 : ℂ) * star a‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma sqrt_two_mem_radii {n : ℕ} (hn_even : Even n) :
    Real.sqrt 2 ∈ radii n := by
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hn_even
  refine ⟨Real.sqrt_nonneg 2, 1, ⟨skewMat hn2, skewMat_mem_unitary hn2⟩, ?_⟩
  intro x
  let y : Fin n → ℂ := ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) *ᵥ x - skewMat hn2 *ᵥ star x
  have hy_apply : ∀ i : Fin n, y i = x i - sgnFin i * star (x (swapFin hn2 i)) := by
    intro i
    show (((1 : Mat n) *ᵥ x) i - (skewMat hn2 *ᵥ star x) i) =
      x i - sgnFin i * star (x (swapFin hn2 i))
    rw [Matrix.one_mulVec, skewMat_mulVec]
    rfl
  have hpair : ∀ i : Fin n,
      ‖y i‖ ^ 2 + ‖y (swapFin hn2 i)‖ ^ 2 = 2 * ‖x i‖ ^ 2 + 2 * ‖x (swapFin hn2 i)‖ ^ 2 := by
    intro i
    rw [hy_apply i, hy_apply (swapFin hn2 i), swapFin_swapFin]
    by_cases hi : i.val % 2 = 0
    · have hsi : (swapFin hn2 i).val % 2 ≠ 0 := by
        simp only [swapFin, Equiv.coe_fn_mk, swapFinFun, hi, ↓reduceDIte]
        omega
      simp only [sgnFin, hi, hsi, ↓reduceIte]
      exact pair_norm_sq_even (x i) (x (swapFin hn2 i))
    · have hsi : (swapFin hn2 i).val % 2 = 0 := by
        simp only [swapFin, Equiv.coe_fn_mk, swapFinFun, hi, ↓reduceDIte]
        omega
      simp only [sgnFin, hi, hsi, ↓reduceIte]
      exact pair_norm_sq_odd (x i) (x (swapFin hn2 i))
  have hsum_y : ∑ i : Fin n, ‖y (swapFin hn2 i)‖ ^ 2 = ∑ i : Fin n, ‖y i‖ ^ 2 :=
    Equiv.sum_comp (swapFin hn2) (fun i => ‖y i‖ ^ 2)
  have hsum_x : ∑ i : Fin n, ‖x (swapFin hn2 i)‖ ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 :=
    Equiv.sum_comp (swapFin hn2) (fun i => ‖x i‖ ^ 2)
  have hsum_eq : 2 * ∑ i : Fin n, ‖y i‖ ^ 2 = 4 * ∑ i : Fin n, ‖x i‖ ^ 2 := by
    calc 2 * ∑ i : Fin n, ‖y i‖ ^ 2
        = (∑ i : Fin n, ‖y i‖ ^ 2) + (∑ i : Fin n, ‖y (swapFin hn2 i)‖ ^ 2) := by linarith
      _ = ∑ i : Fin n, (‖y i‖ ^ 2 + ‖y (swapFin hn2 i)‖ ^ 2) := (Finset.sum_add_distrib).symm
      _ = ∑ i : Fin n, (2 * ‖x i‖ ^ 2 + 2 * ‖x (swapFin hn2 i)‖ ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpair i
      _ = 2 * (∑ i : Fin n, ‖x i‖ ^ 2) + 2 * (∑ i : Fin n, ‖x (swapFin hn2 i)‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 4 * ∑ i : Fin n, ‖x i‖ ^ 2 := by linarith
  have hsq : (euclid y) ^ 2 = (Real.sqrt 2 * euclid x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), euclid_sq, euclid_sq]
    linarith
  exact le_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg 2) (euclid_nonneg x)) (le_of_eq hsq)

-- Universal lower bound sqrt 2

private lemma sqrt_two_le_of_mem_radii {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : r ∈ radii n) :
    Real.sqrt 2 ≤ r := by
  rcases hr with ⟨hr0, U, V, hUV⟩
  let x : Fin n → ℂ := fun _ => 1
  have hx_ne : x ≠ 0 := by
    intro h
    have h0 := congr_fun h ⟨0, hn⟩
    exact one_ne_zero h0
  have hx_pos : 0 < euclid x := euclid_pos_of_ne_zero hx_ne
  let u : Fin n → ℂ := (U : Mat n) *ᵥ x
  let v : Fin n → ℂ := (V : Mat n) *ᵥ star x
  have hu : euclid u = euclid x := euclid_unitary_mulVec U x
  have hv : euclid v = euclid x := by
    rw [euclid_unitary_mulVec V (star x), euclid_star]
  have h1 : euclid (u - v) ≤ r * euclid x := hUV x
  have h2 : euclid (u + v) ≤ r * euclid x := by
    have hI := hUV (Complex.I • x)
    have hstar : star (Complex.I • x) = (-Complex.I) • star x := by
      ext i
      simp only [Pi.star_def, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
        Complex.conj_I]
    have hlhs : (U : Mat n) *ᵥ (Complex.I • x) - (V : Mat n) *ᵥ star (Complex.I • x) =
        Complex.I • (u + v) := by
      rw [hstar, Matrix.mulVec_smul, Matrix.mulVec_smul]
      ext i
      simp only [u, v, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [hlhs, euclid_smul, euclid_smul, Complex.norm_I, one_mul, one_mul] at hI
    exact hI
  have hpara := euclid_parallelogram u v
  rw [hu, hv] at hpara
  have hsq1 : (euclid (u - v)) ^ 2 ≤ (r * euclid x) ^ 2 :=
    pow_le_pow_left₀ (euclid_nonneg _) h1 2
  have hsq2 : (euclid (u + v)) ^ 2 ≤ (r * euclid x) ^ 2 :=
    pow_le_pow_left₀ (euclid_nonneg _) h2 2
  have hr2 : 2 * (euclid x) ^ 2 ≤ r ^ 2 * (euclid x) ^ 2 := by
    rw [mul_pow] at hsq1 hsq2
    linarith
  have h2_le_r2 : 2 ≤ r ^ 2 :=
    le_of_mul_le_mul_right hr2 (sq_pos_of_pos hx_pos)
  have hsqrt : Real.sqrt 2 ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h2_le_r2
  rwa [Real.sqrt_sq hr0] at hsqrt

-- Odd case upper bound

private lemma two_mem_radii (n : ℕ) : (2 : ℝ) ∈ radii n := by
  refine ⟨by norm_num, 1, 1, ?_⟩
  intro x
  have h1 : ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) *ᵥ x = x := Matrix.one_mulVec x
  have h2 : ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) *ᵥ star x = star x :=
    Matrix.one_mulVec (star x)
  rw [h1, h2]
  calc euclid (x - star x) ≤ euclid x + euclid (star x) := euclid_sub_le x (star x)
    _ = 2 * euclid x := by rw [euclid_star]; ring

-- Odd case lower bound

private lemma map_starRingEnd_mulVec {n : ℕ} (M : Mat n) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ star x = star (M *ᵥ x) := by
  ext i
  change ∑ j, (starRingEnd ℂ) (M i j) * (starRingEnd ℂ) (x j) =
    (starRingEnd ℂ) (∑ j, M i j * x j)
  rw [map_sum]
  simp only [map_mul]

private lemma map_starRingEnd_eq_conjTranspose_transpose {n : ℕ} (M : Mat n) :
    M.map (starRingEnd ℂ) = Mᴴᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, starRingEnd_apply]

private lemma map_starRingEnd_map_starRingEnd {n : ℕ} (M : Mat n) :
    (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  ext i j
  simp only [Matrix.map_apply, starRingEnd_self_apply]

private lemma eval_charpoly_eq_det {n : ℕ} (A : Mat n) (z : ℂ) :
    A.charpoly.eval z = Matrix.det (z • (1 : Mat n) - A) := by
  unfold Matrix.charpoly
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix, Matrix.sub_apply,
    Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_C]
  split_ifs with h <;> simp [h]

private lemma two_le_of_mem_radii_odd {n : ℕ} (hn_odd : ¬ Even n) {r : ℝ} (hr : r ∈ radii n) :
    (2 : ℝ) ≤ r := by
  rcases hr with ⟨hr0, U, V, hUV⟩
  have hodd : Odd n := Nat.not_even_iff_odd.mp hn_odd
  have hn_pos : 0 < n := hodd.pos
  have hUU' : (U : Mat n)ᴴ * (U : Mat n) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hUU : (U : Mat n) * (U : Mat n)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hVV' : (V : Mat n)ᴴ * (V : Mat n) = 1 := Matrix.mem_unitaryGroup_iff'.mp V.2
  have hVV : (V : Mat n) * (V : Mat n)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.2
  let W : Mat n := (U : Mat n)ᴴ * (V : Mat n)
  have hWW' : Wᴴ * W = 1 := by
    calc Wᴴ * W = (V : Mat n)ᴴ * ((U : Mat n) * (U : Mat n)ᴴ) * (V : Mat n) := by
          simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hVV']
  have hWW : W * Wᴴ = 1 := by
    calc W * Wᴴ = (U : Mat n)ᴴ * ((V : Mat n) * (V : Mat n)ᴴ) * (U : Mat n) := by
          simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hVV, Matrix.mul_one, hUU']
  let Wbar : Mat n := W.map (starRingEnd ℂ)
  have hWbar_eq : Wbar = Wᴴᵀ := map_starRingEnd_eq_conjTranspose_transpose W
  have hWbar' : Wbarᴴ * Wbar = 1 := by
    have h1 : Wbarᴴ = Wᵀ := by
      ext i j
      simp only [Wbar, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply,
        starRingEnd_apply, star_star]
    rw [h1, hWbar_eq, ← Matrix.transpose_mul, hWW', Matrix.transpose_one]
  let A : Mat n := W * Wbar
  have hAA' : Aᴴ * A = 1 := by
    calc Aᴴ * A = Wbarᴴ * (Wᴴ * W) * Wbar := by
          simp only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hWW', Matrix.mul_one, hWbar']
  have hdetA : A.det = 1 := by
    calc A.det = W.det * Wbar.det := Matrix.det_mul W Wbar
      _ = W.det * Wᴴ.det := by rw [hWbar_eq, Matrix.det_transpose]
      _ = (W * Wᴴ).det := (Matrix.det_mul W Wᴴ).symm
      _ = 1 := by rw [hWW, Matrix.det_one]
  have hAbar : A.map (starRingEnd ℂ) = Wᴴ * A * W := by
    have h1 : A.map (starRingEnd ℂ) = Wbar * W := by
      dsimp only [A]
      rw [Matrix.map_mul, map_starRingEnd_map_starRingEnd]
    rw [h1]
    calc Wbar * W = (Wᴴ * W) * Wbar * W := by rw [hWW', Matrix.one_mul]
      _ = Wᴴ * A * W := by simp only [A, Matrix.mul_assoc]
  -- Define real function f(t) = Re(det(t*I - A))
  let f : ℝ → ℝ := fun t => (A.charpoly.eval (t : ℂ)).re
  have hreal : ∀ t : ℝ, starRingEnd ℂ (A.charpoly.eval (t : ℂ)) = A.charpoly.eval (t : ℂ) := by
    intro t
    rw [eval_charpoly_eq_det, RingHom.map_det]
    have hmap : ((t : ℂ) • (1 : Mat n) - A).map (starRingEnd ℂ) =
        Wᴴ * ((t : ℂ) • (1 : Mat n) - A) * W := by
      have hsub : ((t : ℂ) • (1 : Mat n) - A).map (starRingEnd ℂ) =
          (t : ℂ) • (1 : Mat n) - A.map (starRingEnd ℂ) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul, map_sub, map_mul, Complex.conj_ofReal]
        split_ifs <;> simp
      rw [hsub, hAbar]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hWW']
    change (((t : ℂ) • (1 : Mat n) - A).map (starRingEnd ℂ)).det =
      ((t : ℂ) • (1 : Mat n) - A).det
    rw [hmap, Matrix.det_mul, Matrix.det_mul]
    calc Wᴴ.det * ((t : ℂ) • (1 : Mat n) - A).det * W.det
        = (Wᴴ.det * W.det) * ((t : ℂ) • (1 : Mat n) - A).det := by ring
      _ = (Wᴴ * W).det * ((t : ℂ) • (1 : Mat n) - A).det := by rw [← Matrix.det_mul]
      _ = ((t : ℂ) • (1 : Mat n) - A).det := by rw [hWW', Matrix.det_one, one_mul]
  have hf_eq : ∀ t : ℝ, A.charpoly.eval (t : ℂ) = (f t : ℂ) := by
    intro t
    have him : (A.charpoly.eval (t : ℂ)).im = 0 := by
      have h := congr_arg Complex.im (hreal t)
      rw [Complex.conj_im] at h
      linarith
    exact Complex.ext rfl (by simp only [Complex.ofReal_im, him])
  have hf0 : f 0 = -1 := by
    have h0 : A.charpoly.eval (0 : ℂ) = -1 := by
      rw [eval_charpoly_eq_det, zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin,
        hodd.neg_one_pow, hdetA, mul_one]
    simp only [f, Complex.ofReal_zero, h0, Complex.neg_re, Complex.one_re]
  have hdeg : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmonic : A.charpoly.Monic := Matrix.charpoly_monic A
  have hf_expand : ∀ t : ℝ,
      f t = t ^ n + ∑ k ∈ Finset.range n, (A.charpoly.coeff k).re * t ^ k := by
    intro t
    have heval : A.charpoly.eval (t : ℂ) =
        ∑ k ∈ Finset.range (n + 1), A.charpoly.coeff k * (t : ℂ) ^ k := by
      rw [Polynomial.eval_eq_sum_range' (by omega : A.charpoly.natDegree < n + 1)]
    have hre : (A.charpoly.eval (t : ℂ)).re =
        ∑ k ∈ Finset.range (n + 1), (A.charpoly.coeff k).re * t ^ k := by
      rw [heval, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
    rw [show f t = (A.charpoly.eval (t : ℂ)).re from rfl, hre, Finset.sum_range_succ]
    have hlc : A.charpoly.coeff n = 1 := by
      have h := hmonic.leadingCoeff
      rw [Polynomial.leadingCoeff, hdeg] at h
      exact h
    rw [hlc, Complex.one_re, one_mul, add_comm]
  -- Find M > 0 with f M > 0
  let C : ℝ := ∑ k ∈ Finset.range n, |(A.charpoly.coeff k).re|
  let M : ℝ := max 1 (C + 1)
  have hM1 : 1 ≤ M := le_max_left 1 (C + 1)
  have hMC : C + 1 ≤ M := le_max_right 1 (C + 1)
  have hM0 : 0 ≤ M := by linarith
  have hfM : 0 < f M := by
    rw [hf_expand M]
    have htail : |∑ k ∈ Finset.range n, (A.charpoly.coeff k).re * M ^ k| ≤ C * M ^ (n - 1) := by
      calc |∑ k ∈ Finset.range n, (A.charpoly.coeff k).re * M ^ k|
          ≤ ∑ k ∈ Finset.range n, |(A.charpoly.coeff k).re * M ^ k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, |(A.charpoly.coeff k).re| * M ^ (n - 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_pow, abs_of_nonneg hM0]
            have hk_le : k ≤ n - 1 := by
              have := Finset.mem_range.mp hk
              omega
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hk_le) (abs_nonneg _)
        _ = C * M ^ (n - 1) := (Finset.sum_mul _ _ _).symm
    have hpow : M ^ n = M * M ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    have hMp : 0 < M ^ (n - 1) := pow_pos (by linarith) _
    have hneg : -(C * M ^ (n - 1)) ≤ ∑ k ∈ Finset.range n, (A.charpoly.coeff k).re * M ^ k :=
      (abs_le.mp htail).1
    have h1 : (C + 1) * M ^ (n - 1) ≤ M * M ^ (n - 1) :=
      mul_le_mul_of_nonneg_right hMC (le_of_lt hMp)
    linarith
  have hf_cont : Continuous f := by
    have h1 : Continuous (fun t : ℝ => A.charpoly.eval (t : ℂ)) :=
      A.charpoly.continuous.comp Complex.continuous_ofReal
    exact Complex.continuous_re.comp h1
  have h0_mem : (0 : ℝ) ∈ Set.Icc (f 0) (f M) := by
    rw [hf0]
    exact ⟨by norm_num, le_of_lt hfM⟩
  rcases intermediate_value_Icc hM0 hf_cont.continuousOn h0_mem with ⟨t, htIcc, hft⟩
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le htIcc.1 with rfl | hlt
    · linarith
    · exact hlt
  have hdet0 : Matrix.det ((t : ℂ) • (1 : Mat n) - A) = 0 := by
    rw [← eval_charpoly_eq_det, hf_eq t, hft, Complex.ofReal_zero]
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet0 with ⟨v, hv_ne, hAv0⟩
  have hAv : A *ᵥ v = (t : ℂ) • v := by
    have hsub : ((t : ℂ) • (1 : Mat n)) *ᵥ v - A *ᵥ v = 0 := by
      simpa only [Matrix.sub_mulVec] using hAv0
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hsub
    exact hsub.symm
  have ht_eq_one : t = 1 := by
    have he1 : euclid (A *ᵥ v) = euclid v := euclid_mulVec_of_conjTranspose_mul_self A hAA' v
    rw [hAv, euclid_smul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht_pos)] at he1
    have hv_ne0 : euclid v ≠ 0 := ne_of_gt (euclid_pos_of_ne_zero hv_ne)
    exact mul_right_cancel₀ hv_ne0 (by linarith)
  have hAv1 : A *ᵥ v = v := by
    rw [hAv, ht_eq_one, Complex.ofReal_one, one_smul]
  have hinv : W *ᵥ star (W *ᵥ star v) = v := by
    calc W *ᵥ star (W *ᵥ star v)
        = W *ᵥ (Wbar *ᵥ star (star v)) := by rw [← map_starRingEnd_mulVec]
      _ = (W * Wbar) *ᵥ v := by rw [star_star, Matrix.mulVec_mulVec]
      _ = v := hAv1
  -- Build x ≠ 0 with W *ᵥ star x = -x
  have hx_exists : ∃ x : Fin n → ℂ, x ≠ 0 ∧ W *ᵥ star x = -x := by
    by_cases hdiff : v - W *ᵥ star v ≠ 0
    · refine ⟨v - W *ᵥ star v, hdiff, ?_⟩
      rw [star_sub, Matrix.mulVec_sub, hinv, neg_sub]
    · have hfix : W *ᵥ star v = v := (sub_eq_zero.mp (not_ne_iff.mp hdiff)).symm
      refine ⟨Complex.I • v, smul_ne_zero Complex.I_ne_zero hv_ne, ?_⟩
      have hstar : star (Complex.I • v) = (-Complex.I) • star v := by
        ext i
        simp only [Pi.star_def, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
          Complex.conj_I]
      rw [hstar, Matrix.mulVec_smul, hfix, neg_smul]
  rcases hx_exists with ⟨x, hx_ne, hWx⟩
  have hVx : (V : Mat n) *ᵥ star x = -((U : Mat n) *ᵥ x) := by
    calc (V : Mat n) *ᵥ star x
        = ((U : Mat n) * (U : Mat n)ᴴ * (V : Mat n)) *ᵥ star x := by rw [hUU, Matrix.one_mul]
      _ = (U : Mat n) *ᵥ (W *ᵥ star x) := by rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (U : Mat n) *ᵥ (-x) := by rw [hWx]
      _ = -((U : Mat n) *ᵥ x) := Matrix.mulVec_neg _ _
  have hdiff : (U : Mat n) *ᵥ x - (V : Mat n) *ᵥ star x = (2 : ℂ) • ((U : Mat n) *ᵥ x) := by
    rw [hVx, sub_neg_eq_add, two_smul]
  have hbound := hUV x
  rw [hdiff, euclid_smul, euclid_unitary_mulVec] at hbound
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2] at hbound
  exact le_of_mul_le_mul_right hbound (euclid_pos_of_ne_zero hx_ne)

private theorem main_proved : ∀ n : ℕ, 0 < n →
    IsLeast (radii n) (if Even n then Real.sqrt 2 else 2) := by
  intro n hn
  by_cases heven : Even n
  · rw [if_pos heven]
    exact ⟨sqrt_two_mem_radii heven, fun r hr => sqrt_two_le_of_mem_radii hn hr⟩
  · rw [if_neg heven]
    exact ⟨two_mem_radii n, fun r hr => two_le_of_mem_radii_odd heven hr⟩

end OMA.S_mo_442655.Proof

theorem OMA.solution : type_of% @OMA.S_mo_442655.main :=
  OMA.S_mo_442655.Proof.main_proved

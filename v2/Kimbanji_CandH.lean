import Mathlib

/-!
# 후보 H 닫기: Lean 으로 닫히는 조각 (Trombo / Kimbanji, 2026-11-04)
순수 수학. 밀레니엄 문제와 무관. 로젠–메르텐스 극한 본체와 소수 정리는 Mathlib 에 없고 여기서도 증명하지 않는다.
여기서 증명하는 것은 유도 사슬의 «유한 대수» 조각뿐이다.
1. χ5 는 곱셈적이다 (mod 5 잔여류 표 검사).
2. 오일러 인자 대수: ζ_K 인자 = ζ 인자 · L 인자 = (1−x)⁻¹(1−χ x)⁻¹ 가
   분해(χ=1): ((1−x)²)⁻¹, 불활성(χ=−1): (1−x²)⁻¹, 분기(χ=0): (1−x)⁻¹ 이고,
   x = 1/p 에서 역수가 (1−1/p)², 1−1/p², 1−1/5 (p=5) 이다. 구체 소수 점검 포함.
3. κ = 2 ln φ/√5 대수: κ>0, e^(−g)/κ = √5 e^(−g)/(2 ln φ), ln(e^(−g)/κ) = −g − ln κ.
4. 뫼비우스: n≥2 에서 진약수 합 −μ(n) 와, A-분할 꼬리의 계수 Σ_{k≥2, jk=n} μ(j)/(jk) = −μ(n)/n.
5. H6 조립 대수: −g − lk = S − (g + lk + S).
-/

open Real

namespace KimbanjiCandH

/-- 이차 지표 χ5 : 1,4 → 1 ; 2,3 → −1 ; 0 → 0 -/
def chi5 (n : ℕ) : ℤ :=
  if n % 5 = 1 ∨ n % 5 = 4 then 1 else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0

theorem chi5_mul (a b : ℕ) : chi5 (a * b) = chi5 a * chi5 b := by
  have h : (a * b) % 5 = ((a % 5) * (b % 5)) % 5 := Nat.mul_mod _ _ _
  have ha : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have hb : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  unfold chi5
  rw [h]
  rcases ha with ha | ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb | hb <;>
    simp [ha, hb]

/-- ζ_K 의 한 소수 위 오일러 인자 (ζ 인자 × L 인자), x = p^(−s), c = χ(p). -/
noncomputable def eulerK (x : ℝ) (c : ℤ) : ℝ := (1 - x)⁻¹ * (1 - (c : ℝ) * x)⁻¹

theorem eulerK_split (x : ℝ) : eulerK x 1 = ((1 - x) ^ 2)⁻¹ := by
  unfold eulerK; push_cast; rw [one_mul, sq, mul_inv]

theorem eulerK_inert (x : ℝ) : eulerK x (-1) = (1 - x ^ 2)⁻¹ := by
  unfold eulerK; push_cast
  rw [← mul_inv]; congr 1; ring

theorem eulerK_ram (x : ℝ) : eulerK x 0 = (1 - x)⁻¹ := by
  unfold eulerK; simp

/-- x = 1/p 에서 역수: 분해 소수 (1−1/p)². -/
theorem local_split (p : ℝ) : (eulerK (1 / p) 1)⁻¹ = (1 - 1 / p) ^ 2 := by
  rw [eulerK_split, inv_inv]

/-- 불활성 소수: 1 − 1/p². -/
theorem local_inert (p : ℝ) : (eulerK (1 / p) (-1))⁻¹ = 1 - 1 / p ^ 2 := by
  rw [eulerK_inert, inv_inv]; field_simp

/-- 분기 소수: 1 − 1/p (p=5). -/
theorem local_ram (p : ℝ) : (eulerK (1 / p) 0)⁻¹ = 1 - 1 / p := by
  rw [eulerK_ram, inv_inv]

/-- 소수 p 의 노름 인자 곱 (식의 우변 꼴). -/
noncomputable def normFactor (p : ℕ) : ℝ :=
  if chi5 p = 1 then (1 - 1 / (p : ℝ)) ^ 2
  else if chi5 p = -1 then 1 - 1 / (p : ℝ) ^ 2
  else 1 - 1 / (p : ℝ)

/-- 한 소수 위의 ζ_K 오일러 인자의 역수 (s=1) 는 χ5(p) 로 고른 노름 인자와 같다. -/
theorem local_inv_eq_normFactor (p : ℕ) : (eulerK (1 / (p : ℝ)) (chi5 p))⁻¹ = normFactor p := by
  unfold normFactor
  by_cases h1 : chi5 p = 1
  · rw [if_pos h1, h1]; exact local_split _
  · by_cases h2 : chi5 p = -1
    · rw [if_neg h1, if_pos h2, h2]; exact local_inert _
    · have h0 : chi5 p = 0 := by
        unfold chi5 at h1 h2 ⊢
        split_ifs at h1 h2 ⊢ <;> simp_all
      rw [if_neg h1, if_neg h2, h0]; exact local_ram _

/-- 분류: p%5 ∈ {1,4} ⇒ χ=1 (분해) ; {2,3} ⇒ −1 (불활성) ; 0 ⇒ 0 (분기). -/
theorem chi5_split (p : ℕ) (h : p % 5 = 1 ∨ p % 5 = 4) : chi5 p = 1 := by
  unfold chi5; simp [h]

theorem chi5_inert (p : ℕ) (h : p % 5 = 2 ∨ p % 5 = 3) : chi5 p = -1 := by
  unfold chi5
  have : ¬ (p % 5 = 1 ∨ p % 5 = 4) := by omega
  simp [this, h]

theorem chi5_ram (p : ℕ) (h : p % 5 = 0) : chi5 p = 0 := by
  unfold chi5
  have : ¬ (p % 5 = 1 ∨ p % 5 = 4) := by omega
  have h' : ¬ (p % 5 = 2 ∨ p % 5 = 3) := by omega
  simp [this, h']

/-- 구체 소수 점검: 11,19 (분해), 2,3,7 (불활성), 5 (분기). -/
theorem normFactor_11 : normFactor 11 = (10 / 11) ^ 2 := by
  have : chi5 11 = 1 := chi5_split 11 (by decide)
  unfold normFactor; rw [if_pos this]; norm_num

theorem normFactor_2 : normFactor 2 = 3 / 4 := by
  have : chi5 2 = -1 := chi5_inert 2 (by decide)
  unfold normFactor; rw [if_neg (by omega), if_pos this]; norm_num

theorem normFactor_3 : normFactor 3 = 8 / 9 := by
  have : chi5 3 = -1 := chi5_inert 3 (by decide)
  unfold normFactor; rw [if_neg (by omega), if_pos this]; norm_num

theorem normFactor_5 : normFactor 5 = 4 / 5 := by
  have : chi5 5 = 0 := chi5_ram 5 (by decide)
  unfold normFactor; rw [if_neg (by omega), if_neg (by omega)]; norm_num

theorem normFactor_19 : normFactor 19 = (18 / 19) ^ 2 := by
  have : chi5 19 = 1 := chi5_split 19 (by decide)
  unfold normFactor; rw [if_pos this]; norm_num

theorem normFactor_7 : normFactor 7 = 48 / 49 := by
  have : chi5 7 = -1 := chi5_inert 7 (by decide)
  unfold normFactor; rw [if_neg (by omega), if_pos this]; norm_num

/-! ### κ 대수 -/

noncomputable abbrev phi : ℝ := Real.goldenRatio

theorem log_phi_pos : 0 < Real.log phi := Real.log_pos Real.one_lt_goldenRatio

/-- κ = 2 ln φ / √5 (Q(√5): h=1, R=ln φ, w=2, d=5 의 유수) -/
noncomputable def kappa : ℝ := 2 * Real.log phi / Real.sqrt 5

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have := log_phi_pos
  positivity

theorem kappa_sq : kappa ^ 2 = 4 * Real.log phi ^ 2 / 5 := by
  unfold kappa
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num

/-- e^(−g)/κ = √5 e^(−g) / (2 ln φ) -/
theorem const_eq (g : ℝ) : Real.exp (-g) / kappa = Real.sqrt 5 * Real.exp (-g) / (2 * Real.log phi) := by
  have h5 : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hl : Real.log phi ≠ 0 := log_phi_pos.ne'
  unfold kappa
  field_simp

theorem kappa_mul_const (g : ℝ) : kappa * (Real.exp (-g) / kappa) = Real.exp (-g) := by
  have := kappa_pos.ne'
  field_simp

/-- ln(e^(−g)/κ) = −g − ln κ : 로그 꼴에는 e 가 없다. -/
theorem log_const (g : ℝ) : Real.log (Real.exp (-g) / kappa) = -g - Real.log kappa := by
  rw [Real.log_div (Real.exp_pos _).ne' kappa_pos.ne', Real.log_exp]

/-- H6 조립 대수: M = g + lk + S 로 두면 S − M = −g − lk. -/
theorem assemble (g lk S : ℝ) : S - (g + lk + S) = -g - lk := by ring

/-! ### 뫼비우스 -/

theorem moebius_proper_divisors (n : ℕ) (hn : 2 ≤ n) :
    ∑ d ∈ n.divisors.erase n, (ArithmeticFunction.moebius d : ℤ) = - (ArithmeticFunction.moebius n : ℤ) := by
  have hmem : n ∈ n.divisors := by
    rw [Nat.mem_divisors]; exact ⟨dvd_refl n, by omega⟩
  have hsum : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply]
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
    exact ArithmeticFunction.one_apply_ne (by omega)
  have := Finset.sum_erase_add n.divisors (fun d => (ArithmeticFunction.moebius d : ℤ)) hmem
  linarith

/-- A-분할 꼬리 계수: (1/n) Σ_{j|n, j<n} μ(j) = −μ(n)/n  (n ≥ 2). -/
theorem tail_coeff (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ n.divisors.erase n, (ArithmeticFunction.moebius j : ℚ)) / n
      = -(ArithmeticFunction.moebius n : ℚ) / n := by
  have h := moebius_proper_divisors n hn
  have h' : (∑ j ∈ n.divisors.erase n, (ArithmeticFunction.moebius j : ℚ))
      = -(ArithmeticFunction.moebius n : ℚ) := by
    exact_mod_cast h
  rw [h']

end KimbanjiCandH

#print axioms KimbanjiCandH.chi5_mul
#print axioms KimbanjiCandH.local_inv_eq_normFactor
#print axioms KimbanjiCandH.normFactor_11
#print axioms KimbanjiCandH.normFactor_2
#print axioms KimbanjiCandH.normFactor_5
#print axioms KimbanjiCandH.kappa_pos
#print axioms KimbanjiCandH.const_eq
#print axioms KimbanjiCandH.log_const
#print axioms KimbanjiCandH.kappa_sq
#print axioms KimbanjiCandH.tail_coeff
#print axioms KimbanjiCandH.assemble

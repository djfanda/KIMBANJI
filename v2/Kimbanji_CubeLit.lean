import Mathlib

/-!
# 큐브 문헌 채움: Lean 으로 닫히는 대수 조각 (Trombo / Kimbanji, 2026-11-04)
순수 수학. 여기서 증명하는 것은 문헌 정리의 «대수 정합» 뿐이다.
Mathlib 에 없어 인용으로만 남기는 해석 정리: 가우스 디감마 정리 본체(ψ(p/5) 값),
라마누잔 상호 관계식 본체(로저스–라마누잔 연분수), 류수 공식, 자기에의 크로네커 극한 공식.
-/

open Real

namespace KimbanjiCubeLit

noncomputable abbrev phi : ℝ := Real.goldenRatio

lemma phi_pos : 0 < phi := Real.goldenRatio_pos
lemma phi_gt_one : 1 < phi := Real.one_lt_goldenRatio
lemma s5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)
lemma s5_sq : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
lemma s5_gt_two : 2 < √5 := by
  have h : (2:ℝ)^2 < 5 := by norm_num
  nlinarith [s5_sq, s5_pos]

/-- φ² = φ + 1 -/
theorem phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

/-- φ = (1+√5)/2 から √5 = 2φ − 1 -/
theorem sqrt5_eq : √5 = 2 * phi - 1 := by
  unfold phi; rw [Real.goldenRatio]; ring

/-- φ⁻¹ = φ − 1 -/
theorem inv_phi : phi⁻¹ = phi - 1 := by
  have h : phi * (phi - 1) = 1 := by nlinarith [phi_sq]
  exact inv_eq_of_mul_eq_one_right h

/-- φ + 1/φ = √5 -/
theorem phi_add_inv : phi + phi⁻¹ = √5 := by
  rw [inv_phi, sqrt5_eq]; ring

/-- √5 φ = (5+√5)/2 -/
theorem sqrt5_mul_phi : √5 * phi = (5 + √5) / 2 := by
  rw [sqrt5_eq]; nlinarith [phi_sq]

/-- cos(π/5) = φ/2 -/
theorem cos_pi_div_five_phi : Real.cos (π / 5) = phi / 2 := by
  rw [Real.cos_pi_div_five]; unfold phi; rw [Real.goldenRatio]; ring

/-- φ = 2 cos(π/5) -/
theorem phi_eq_two_cos : phi = 2 * Real.cos (π / 5) := by
  rw [cos_pi_div_five_phi]; ring

/-- cos(2π/5) = (√5 − 1)/4 = 1/(2φ) -/
theorem cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [s5_sq]

lemma sin_pi5_pos : 0 < Real.sin (π / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
lemma sin_2pi5_pos : 0 < Real.sin (2 * π / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

noncomputable def c1 : ℝ := Real.cos (π / 5) / Real.sin (π / 5)
noncomputable def c2 : ℝ := Real.cos (2 * π / 5) / Real.sin (2 * π / 5)

lemma c1_pos : 0 < c1 := by
  unfold c1; apply div_pos _ sin_pi5_pos
  rw [Real.cos_pi_div_five]; nlinarith [s5_pos]
lemma c2_pos : 0 < c2 := by
  unfold c2; apply div_pos _ sin_2pi5_pos
  rw [cos_two_pi_div_five]; nlinarith [s5_gt_two]

/-- cot²(π/5) = 1 + 2/√5 -/
theorem c1_sq : c1 ^ 2 = 1 + 2 / √5 := by
  unfold c1
  have hs := Real.sin_sq_add_cos_sq (π / 5)
  have hc := Real.cos_pi_div_five
  have hsp := sin_pi5_pos
  rw [div_pow, div_eq_iff (by positivity)]
  have : Real.sin (π / 5) ^ 2 = 1 - Real.cos (π / 5) ^ 2 := by linarith
  rw [this, hc]
  field_simp
  nlinarith [s5_sq, s5_pos]

/-- cot²(2π/5) = 1 − 2/√5 -/
theorem c2_sq : c2 ^ 2 = 1 - 2 / √5 := by
  unfold c2
  have hs := Real.sin_sq_add_cos_sq (2 * π / 5)
  have hsp := sin_2pi5_pos
  rw [div_pow, div_eq_iff (by positivity)]
  have : Real.sin (2 * π / 5) ^ 2 = 1 - Real.cos (2 * π / 5) ^ 2 := by linarith
  rw [this, cos_two_pi_div_five]
  field_simp
  nlinarith [s5_sq, s5_pos]

theorem c1_eq : c1 = √(1 + 2 / √5) := by
  rw [← c1_sq, Real.sqrt_sq c1_pos.le]
theorem c2_eq : c2 = √(1 - 2 / √5) := by
  rw [← c2_sq, Real.sqrt_sq c2_pos.le]

/-- cot(π/5) cot(2π/5) = 1/√5 -/
theorem c1_mul_c2 : c1 * c2 = 1 / √5 := by
  have h : (c1 * c2) ^ 2 = (1 / √5) ^ 2 := by
    rw [mul_pow, c1_sq, c2_sq]
    field_simp
    nlinarith [s5_sq]
  have hp : 0 < c1 * c2 := mul_pos c1_pos c2_pos
  have hq : 0 < 1 / √5 := by positivity
  nlinarith [sq_nonneg (c1 * c2 - 1 / √5), sq_nonneg (c1 * c2 + 1 / √5)]

/-! ## 가우스 디감마 q=5 의 실수형: 대수 정합 (ψ 값 자체는 인용) -/

noncomputable def g : ℝ := Real.eulerMascheroniConstant
noncomputable def L5 : ℝ := Real.log 5
noncomputable def Lp : ℝ := Real.log phi

/-- 조사 쪽 실수형 (φ 형태). ψ(p/5) 의 우변으로 «정의» 한다. 좌변 ψ 와의 일치는 인용(수치 150자리). -/
noncomputable def R1 : ℝ := -g - (π / 2) * c1 - (5 / 4) * L5 - (√5 / 2) * Lp
noncomputable def R2 : ℝ := -g - (π / 2) * c2 - (5 / 4) * L5 + (√5 / 2) * Lp
noncomputable def R3 : ℝ := -g + (π / 2) * c2 - (5 / 4) * L5 + (√5 / 2) * Lp
noncomputable def R4 : ℝ := -g + (π / 2) * c1 - (5 / 4) * L5 - (√5 / 2) * Lp

theorem R14_sum : R1 + R4 = -2 * g - (5 / 2) * L5 - √5 * Lp := by unfold R1 R4; ring
theorem R23_sum : R2 + R3 = -2 * g - (5 / 2) * L5 + √5 * Lp := by unfold R2 R3; ring
theorem R_total : R1 + R2 + R3 + R4 = -4 * g - 5 * L5 := by unfold R1 R2 R3 R4; ring
theorem R_refl1 : R4 - R1 = π * c1 := by unfold R1 R4; ring
theorem R_refl2 : R3 - R2 = π * c2 := by unfold R2 R3; ring
theorem R_diff : (R2 + R3) - (R1 + R4) = 2 * √5 * Lp := by unfold R1 R2 R3 R4; ring

/-! ## κ = 2 ln φ/√5 -/

theorem Lp_pos : 0 < Lp := Real.log_pos phi_gt_one

noncomputable def kappa : ℝ := 2 * Lp / √5

theorem kappa_pos : 0 < kappa := by unfold kappa; have := Lp_pos; have := s5_pos; positivity
theorem sqrt5_mul_kappa : √5 * kappa = 2 * Lp := by
  unfold kappa; field_simp
theorem kappa_sq : kappa ^ 2 = 4 * Lp ^ 2 / 5 := by
  unfold kappa; rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring

theorem log_kappa : Real.log kappa = Real.log 2 + Real.log Lp - Real.log 5 / 2 := by
  unfold kappa
  have h1 : (2 : ℝ) * Lp ≠ 0 := by have := Lp_pos; positivity
  rw [Real.log_div h1 s5_pos.ne', Real.log_mul (by norm_num) Lp_pos.ne', Real.log_sqrt (by norm_num)]

/-- γ_K := γ + ln κ ; e^(−γ_K) = e^(−γ)/κ = √5 e^(−γ)/(2 ln φ) -/
theorem exp_neg_gammaK : Real.exp (-(g + Real.log kappa)) = Real.exp (-g) / kappa := by
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log kappa), Real.exp_log kappa_pos]
  field_simp

theorem exp_neg_gammaK_closed :
    Real.exp (-(g + Real.log kappa)) = √5 * Real.exp (-g) / (2 * Lp) := by
  rw [exp_neg_gammaK]; unfold kappa
  have := Lp_pos; have := s5_pos
  field_simp

/-! ## 라마누잔 상호 관계식의 대수 (R 의 해석적 값은 인용) -/

/-- 상호 관계식이 α=β=π 에서 (φ+R)² = √5 φ = (5+√5)/2 를 주므로 R = √((5+√5)/2) − φ (φ+R>0 일 때). -/
theorem ramanujan_closed (R : ℝ) (hpos : 0 < phi + R) (h : (phi + R) * (phi + R) = √5 * phi) :
    R = √((5 + √5) / 2) - phi := by
  have h2 : (phi + R) ^ 2 = (5 + √5) / 2 := by rw [← sqrt5_mul_phi, sq]; exact h
  have : phi + R = √((5 + √5) / 2) := by
    rw [← h2, Real.sqrt_sq hpos.le]
  linarith

theorem sqrt_eq_sqrt_sqrt5_phi : √((5 + √5) / 2) = √(√5 * phi) := by rw [sqrt5_mul_phi]

/-- Kohli 식 (6) 꼴: (φ+x)(φ+y) = (φ + 1/φ) φ 는 √5 φ 와 같다. -/
theorem kohli_rhs : (phi + phi⁻¹) * phi = √5 * phi := by rw [phi_add_inv]

/-! ## 비네 + 지수급수: Σ F_n x^n/n! = (e^(φx) − e^(−x/φ))/√5 -/

theorem fib_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => (Nat.fib n : ℝ) * x ^ n / (n.factorial : ℝ))
      ((Real.exp (phi * x) - Real.exp (Real.goldenConj * x)) / √5) := by
  have h1 : HasSum (fun n : ℕ => (phi * x) ^ n / (n.factorial : ℝ)) (Real.exp (phi * x)) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (phi * x)
  have h2 : HasSum (fun n : ℕ => (Real.goldenConj * x) ^ n / (n.factorial : ℝ)) (Real.exp (Real.goldenConj * x)) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (Real.goldenConj * x)
  have h3 := (h1.sub h2).div_const (√5)
  convert h3 using 1
  funext n
  rw [Real.coe_fib_eq, mul_pow, mul_pow]
  ring

theorem conj_eq : Real.goldenConj = -phi⁻¹ := by
  rw [inv_phi]; unfold phi; rw [Real.goldenConj, Real.goldenRatio]; ring

/-- x = 1: Σ F_n/n! = (e^φ − e^(1−φ))/√5 -/
theorem fib_exp_one :
    HasSum (fun n : ℕ => (Nat.fib n : ℝ) / (n.factorial : ℝ))
      ((Real.exp phi - Real.exp (1 - phi)) / √5) := by
  have h := fib_exp_hasSum 1
  have e : Real.goldenConj * 1 = 1 - phi := by
    rw [mul_one]; unfold phi; rw [Real.goldenConj, Real.goldenRatio]; ring
  simpa [e] using h

end KimbanjiCubeLit

#print axioms KimbanjiCubeLit.cos_pi_div_five_phi
#print axioms KimbanjiCubeLit.c1_mul_c2
#print axioms KimbanjiCubeLit.R_diff
#print axioms KimbanjiCubeLit.exp_neg_gammaK_closed
#print axioms KimbanjiCubeLit.ramanujan_closed
#print axioms KimbanjiCubeLit.fib_exp_one

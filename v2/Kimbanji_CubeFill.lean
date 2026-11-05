import Mathlib

/-!
# 큐브 빈칸 공정 탐색: Lean 으로 닫히는 조각 (Trombo / Kimbanji, 2026-11-04)
순수 수학. 밀레니엄 문제와 무관.
여기서 증명하는 것은 감사표 판정의 «근거 조각» 뿐이다.
- sinh(ln x) = (x - 1/x)/2 : 밑에 무관한 대수식 (e 가 더미임을 보이는 근거: 감사 T10, T13).
- sinh(π · (ln φ / π)) = 1/2, cosh(ln φ) = √5/2 : 빈칸 (i,φ,γ) 의 W억지 후보에서 쓰는 값.
- exp(ix) = cos x + i sin x 는 임의 x 에 대한 항등식 (감사 T12 에서 1 이 더미임을 보이는 근거).
- exp(πi) = -1 (감사 T1).
- ψ(1/2) - ψ(1) = -2 ln 2 : π 와 γ 가 모두 사라지는 꼴 (빈칸 (π,γ,1) 의 ψ(1) 이름 바꿈이 재서술인 근거).
Mathlib 에 없는 것: 가우스 디감마 정리 본체, ln Γ(1+z) 의 ζ 급수, 소수 곱 극한(로젠).
-/

open Real

namespace KimbanjiCubeFill

noncomputable abbrev phi : ℝ := Real.goldenRatio

lemma phi_pos : 0 < phi := Real.goldenRatio_pos

lemma phi_mul_pred : phi * (phi - 1) = 1 := by
  nlinarith [Real.goldenRatio_sq]

lemma inv_phi : phi⁻¹ = phi - 1 := inv_eq_of_mul_eq_one_right phi_mul_pred

theorem phi_sub_inv : phi - phi⁻¹ = 1 := by
  rw [inv_phi]; ring

/-- sinh(ln x) = (x - 1/x)/2, x > 0. 밑 e 가 식에서 사라진다. -/
theorem sinh_log_eq (x : ℝ) (hx : 0 < x) : Real.sinh (Real.log x) = (x - x⁻¹) / 2 := by
  rw [Real.sinh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]

/-- cosh(ln x) = (x + 1/x)/2, x > 0. -/
theorem cosh_log_eq (x : ℝ) (hx : 0 < x) : Real.cosh (Real.log x) = (x + x⁻¹) / 2 := by
  rw [Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]

theorem sinh_log_phi : Real.sinh (Real.log phi) = 1 / 2 := by
  rw [sinh_log_eq phi phi_pos, phi_sub_inv]

theorem cosh_log_phi : Real.cosh (Real.log phi) = √5 / 2 := by
  rw [cosh_log_eq phi phi_pos, inv_phi]
  have h : phi = (1 + √5) / 2 := rfl
  rw [h]; ring

/-- y = ln φ / π 이면 sinh(π y) = 1/2. -/
theorem sinh_pi_mul_y : Real.sinh (π * (Real.log phi / π)) = 1 / 2 := by
  have h : π * (Real.log phi / π) = Real.log phi := by
    field_simp
  rw [h, sinh_log_phi]

/-- exp(ix) = cos x + i sin x 는 모든 복소수 x 에서 성립하는 일반 항등식. x = 1 은 그 한 점. -/
theorem exp_mul_I_general (x : ℂ) :
    Complex.exp (x * Complex.I) = Complex.cos x + Complex.sin x * Complex.I :=
  Complex.exp_mul_I x

theorem exp_one_mul_I :
    Complex.exp ((1 : ℂ) * Complex.I) = Complex.cos 1 + Complex.sin 1 * Complex.I :=
  exp_mul_I_general 1

/-- 오일러 항등식. -/
theorem euler_identity : Complex.exp ((π : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-- ψ(1/2) - ψ(1) = -2 ln 2. 양변에 π, γ 가 없다. -/
theorem digamma_half_sub_one :
    Complex.digamma (1 / 2) - Complex.digamma 1 = -2 * Complex.log 2 := by
  rw [Complex.digamma_one_half, Complex.digamma_one]; ring

/-- φ = (1 + ‖1+2i‖)/2 (감사 T15 의 재서술: 크기 치환). -/
theorem phi_eq_norm_form : phi = (1 + ‖(1 : ℂ) + 2 * Complex.I‖) / 2 := by
  have h : ‖(1 : ℂ) + 2 * Complex.I‖ = √5 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    norm_num
  rw [h]

#print axioms sinh_log_eq
#print axioms cosh_log_eq
#print axioms sinh_log_phi
#print axioms cosh_log_phi
#print axioms sinh_pi_mul_y
#print axioms exp_mul_I_general
#print axioms exp_one_mul_I
#print axioms euler_identity
#print axioms digamma_half_sub_one
#print axioms phi_eq_norm_form

end KimbanjiCubeFill

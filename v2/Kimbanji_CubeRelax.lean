import Mathlib

/-!
# 큐브 기준 완화·좁히기: Lean 으로 닫히는 조각 (Trombo / Kimbanji, 2026-11-04)
순수 수학. 밀레니엄 문제와 무관. 완화는 증명이 아니다: 여기서 증명하는 것은 단계 판정의 «근거 조각» 뿐이다.
- 2 sin(i ln φ) = i              : (i,φ) 쌍의 R1 식 (specialfunctionswiki 식)의 대수 근거. sinh(ln φ) = 1/2 에서 나온다.
- cos(π/5)/sin(π/5) + cos(4π/5)/sin(4π/5) = 0 : ψ(1/5) + ψ(4π/5 쪽) 합에서 cot 항이 상쇄되어 π 가 사라지는 근거
  (빈칸 (φ,γ,1), (e,φ,γ) 의 R1 후보 ψ(1/5)+ψ(4/5)).
- Σ_{d | n, d < n} μ(d) = −μ(n) (n ≥ 2) : 후보 H 유도 사슬의 뫼비우스 상쇄 (M_K 두 꼴이 같음을 보이는 대수).
- b^(log_b x) = x (b>0, b≠1, x>0) : exp 와 ln 을 같은 밑으로 바꿔도 참 → e 더미 시험(감사 T13, E13)의 근거.
Mathlib 에 없는 것: 로젠 정리 본체, 가우스 디감마 정리 본체, 전이 상수 Ein(1) − E1(1) = γ.
-/

open Real

namespace KimbanjiCubeRelax

noncomputable abbrev phi : ℝ := Real.goldenRatio

lemma phi_pos : 0 < phi := Real.goldenRatio_pos

lemma inv_phi : phi⁻¹ = phi - 1 := by
  have h : phi * (phi - 1) = 1 := by nlinarith [Real.goldenRatio_sq]
  exact inv_eq_of_mul_eq_one_right h

theorem sinh_log_phi : Real.sinh (Real.log phi) = 1 / 2 := by
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log phi_pos, inv_phi]; ring

/-- 2 sin(i ln φ) = i. -/
theorem two_sin_I_log_phi :
    2 * Complex.sin (Complex.I * (Real.log phi : ℂ)) = Complex.I := by
  have h1 : Complex.sin (Complex.I * (Real.log phi : ℂ)) = Complex.I * (Real.sinh (Real.log phi) : ℂ) := by
    rw [mul_comm, Complex.sin_mul_I, ← Complex.ofReal_sinh, mul_comm]
  rw [h1, sinh_log_phi]
  push_cast
  ring

/-- cot(π − x) = −cot x : ψ(x)+ψ(1−x) 에서 cot 항이 상쇄. -/
theorem cot_pi_sub_eq (x : ℝ) :
    Real.cos (π - x) / Real.sin (π - x) = -(Real.cos x / Real.sin x) := by
  rw [Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

theorem cot_cancel_fifth :
    Real.cos (π / 5) / Real.sin (π / 5) + Real.cos (4 * π / 5) / Real.sin (4 * π / 5) = 0 := by
  have h : 4 * π / 5 = π - π / 5 := by ring
  rw [h, cot_pi_sub_eq]; ring

/-- 뫼비우스 상쇄: n ≥ 2 이면 진약수에 대한 μ 의 합은 −μ(n). -/
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

/-- 밑 변경: b^(log_b x) = x (b>0, b≠1, x>0). exp 와 ln 을 같은 밑으로 바꿔도 참. -/
theorem rpow_logb_base_change (b x : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) (hx : 0 < x) :
    b ^ (Real.logb b x) = x := Real.rpow_logb hb hb1 hx

/-- 밑 변경을 거친 φ = b^(arsinh(1/2)/ln b) : e 가 사라지는 꼴. -/
theorem phi_base_change (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) :
    b ^ (Real.logb b phi) = phi := rpow_logb_base_change b phi hb hb1 phi_pos

end KimbanjiCubeRelax

#print axioms KimbanjiCubeRelax.sinh_log_phi
#print axioms KimbanjiCubeRelax.two_sin_I_log_phi
#print axioms KimbanjiCubeRelax.cot_pi_sub_eq
#print axioms KimbanjiCubeRelax.cot_cancel_fifth
#print axioms KimbanjiCubeRelax.moebius_proper_divisors
#print axioms KimbanjiCubeRelax.rpow_logb_base_change
#print axioms KimbanjiCubeRelax.phi_base_change

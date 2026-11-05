import Mathlib

/-!
# 푸리에 숨은 원 허브  (Trombo / Kimbanji, 2026-11-04)
순수 수학. 이 파일은 밀레니엄 문제와 무관하다.
Mathlib 의 기존 정리(바젤 · 라이프니츠 · 가우스)를 인용하고,
단위근 · 오일러 항등식 · Z/6 지표 · 피사노 주기를 직접 증명한다.
-/

open Real Filter Topology Finset

namespace KimbanjiFourierHub

/-! ## 1. 인용: 바젤(푸리에 파르세발 경유, Mathlib) -/
theorem basel : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two

/-! ## 2. 인용: 라이프니츠 -/
theorem leibniz :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) :=
  Real.tendsto_sum_pi_div_four

/-! ## 3. 인용: 가우스 적분 -/
theorem gauss : ∫ x : ℝ, Real.exp (-1 * x ^ 2) = √π := by
  have := integral_gaussian 1
  simpa using this

/-! ## 4. 사각파 푸리에 급수의 x = π/2 대입 = 라이프니츠 항 -/
theorem squarewave_term (k : ℕ) :
    Real.sin ((2 * k + 1) * (π / 2)) / (2 * k + 1) = (-1 : ℝ) ^ k / (2 * k + 1) := by
  have h : (2 * (k : ℝ) + 1) * (π / 2) = π / 2 + k * π := by ring
  rw [h, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  ring

theorem squarewave_partial_tendsto :
    Tendsto (fun n => ∑ k ∈ range n, Real.sin ((2 * k + 1) * (π / 2)) / (2 * k + 1))
      atTop (𝓝 (π / 4)) := by
  simp only [squarewave_term]
  exact leibniz

/-! ## 5. 오일러 항등식 -/
theorem euler_identity : Complex.exp (π * Complex.I) + 1 = 0 := by
  rw [Complex.exp_pi_mul_I]; ring

theorem full_turn : Complex.exp (2 * π * Complex.I) = 1 := Complex.exp_two_pi_mul_I

/-! ## 6. 6차 단위근 -/
noncomputable def zeta6 : ℂ := Complex.exp (2 * π * Complex.I / (6 : ℕ))

theorem zeta6_primitive : IsPrimitiveRoot zeta6 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem zeta6_pow_six : zeta6 ^ 6 = 1 := zeta6_primitive.pow_eq_one

theorem zeta6_sum_zero : ∑ i ∈ range 6, zeta6 ^ i = 0 :=
  zeta6_primitive.geom_sum_eq_zero (by norm_num)

theorem zeta6_norm : ‖zeta6‖ = 1 :=
  zeta6_primitive.norm'_eq_one (by norm_num)

theorem zeta6_pow_three : zeta6 ^ 3 = -1 := by
  have h := zeta6_primitive
  have h2 : (zeta6 ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact h.pow_eq_one
  have h3 : zeta6 ^ 3 ≠ 1 := by
    intro e; have := h.pow_eq_one_iff_dvd 3 |>.mp e; omega
  have : (zeta6 ^ 3 - 1) * (zeta6 ^ 3 + 1) = 0 := by ring_nf; ring_nf at h2; rw [h2]; ring
  rcases mul_eq_zero.mp this with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) h3
  · exact eq_neg_of_add_eq_zero_left h4

/-! ## 7. Z/6 의 지표: k ↦ zeta6^k 는 준동형 (덧셈 → 곱셈) -/
noncomputable def chi6 (k : ZMod 6) : ℂ := zeta6 ^ k.val

theorem chi6_add (a b : ZMod 6) : chi6 (a + b) = chi6 a * chi6 b := by
  unfold chi6
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ zeta6_pow_six).symm

theorem chi6_zero : chi6 0 = 1 := by simp [chi6]

theorem chi6_period (k : ℕ) : zeta6 ^ (k + 6) = zeta6 ^ k := by
  rw [pow_add, zeta6_pow_six, mul_one]

/-! ## 8. 황금비 φ = 2cos(π/5) (5차 단위근의 실수부 두 배) -/
theorem phi_two_cos : Real.goldenRatio = 2 * Real.cos (π / 5) := by
  rw [Real.cos_pi_div_five, Real.goldenRatio]; ring

/-! ## 9. 피사노 주기 mod 6 = 24 -/
theorem pisano6_returns : Nat.fib 24 % 6 = 0 ∧ Nat.fib 25 % 6 = 1 := by decide

theorem pisano6_minimal :
    ∀ n < 24, 0 < n → ¬ (Nat.fib n % 6 = 0 ∧ Nat.fib (n + 1) % 6 = 1) := by decide

/-! ## 10. 임계선 조건: |1 - 1/ρ| = 1  <=>  Re ρ = 1/2  (ρ ≠ 0) -/
theorem critical_line_circle (ρ : ℂ) (h : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hn : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have e : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [e, norm_div, div_eq_one_iff_eq hn]
  have a : ‖ρ - 1‖ ^ 2 = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have b : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  constructor
  · intro e1
    have : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [e1]
    rw [a, b] at this
    nlinarith
  · intro e1
    have : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
      rw [a, b, e1]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

end KimbanjiFourierHub

#print axioms KimbanjiFourierHub.basel
#print axioms KimbanjiFourierHub.leibniz
#print axioms KimbanjiFourierHub.gauss
#print axioms KimbanjiFourierHub.squarewave_term
#print axioms KimbanjiFourierHub.squarewave_partial_tendsto
#print axioms KimbanjiFourierHub.euler_identity
#print axioms KimbanjiFourierHub.full_turn
#print axioms KimbanjiFourierHub.zeta6_primitive
#print axioms KimbanjiFourierHub.zeta6_pow_six
#print axioms KimbanjiFourierHub.zeta6_sum_zero
#print axioms KimbanjiFourierHub.zeta6_norm
#print axioms KimbanjiFourierHub.zeta6_pow_three
#print axioms KimbanjiFourierHub.chi6_add
#print axioms KimbanjiFourierHub.chi6_zero
#print axioms KimbanjiFourierHub.chi6_period
#print axioms KimbanjiFourierHub.phi_two_cos
#print axioms KimbanjiFourierHub.pisano6_returns
#print axioms KimbanjiFourierHub.pisano6_minimal
#print axioms KimbanjiFourierHub.critical_line_circle

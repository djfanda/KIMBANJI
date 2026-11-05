import Mathlib

/-!
# 단일항 상태의 상관 · CHSH · 호프 매개화 · concurrence  (Trombo / Kimbanji, 2026-11-04)
순수 수학(2x2 복소 행렬과 벡터). 물리 실험의 주장이 아니다. 밀레니엄 문제와 무관하다.
-/

open Real

namespace KimbanjiEntangle

/-- xz 평면 축 n(θ) = cos θ σz + sin θ σx  -/
noncomputable def sig (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ); (Real.sin θ : ℂ), -(Real.cos θ : ℂ)]

/-- 단일항 (|01> - |10>)/√2 -/
noncomputable def singlet : Fin 2 × Fin 2 → ℂ := fun p =>
  if p = (0, 1) then 1 / ((√2 : ℝ) : ℂ) else if p = (1, 0) then -(1 / ((√2 : ℝ) : ℂ)) else 0

/-- <ψ| A ⊗ B |ψ> -/
noncomputable def expect (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  star singlet ⬝ᵥ ((Matrix.kroneckerMap (· * ·) A B).mulVec singlet)

lemma sqrt2_sq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow]; simp

lemma sqrt2_ne : ((√2 : ℝ) : ℂ) ≠ 0 := by
  have : (√2 : ℝ) ≠ 0 := by positivity
  exact_mod_cast this

theorem singlet_correlation (a b : ℝ) :
    expect (sig a) (sig b) = ((-(Real.cos (a - b)) : ℝ) : ℂ) := by
  have h2 := sqrt2_sq
  have h0 := sqrt2_ne
  unfold expect
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, singlet,
    Matrix.kroneckerMap_apply, sig]
  have hi : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← pow_two, h2]; norm_num
  push_cast
  rw [Complex.cos_sub]
  linear_combination (-2 * (Complex.cos a * Complex.cos b + Complex.sin a * Complex.sin b)) * hi

/-! CHSH -/
noncomputable def E (θ : ℝ) : ℝ := -Real.cos θ

theorem E_eq (a b : ℝ) : expect (sig a) (sig b) = (E (a - b) : ℂ) := singlet_correlation a b

theorem chsh_value :
    E (0 - π / 4) - E (0 - 3 * π / 4) + E (π / 2 - π / 4) + E (π / 2 - 3 * π / 4)
      = -(2 * √2) := by
  have h1 : Real.cos (0 - π / 4) = √2 / 2 := by
    rw [zero_sub, Real.cos_neg, Real.cos_pi_div_four]
  have h2 : Real.cos (0 - 3 * π / 4) = -(√2 / 2) := by
    have : (0 : ℝ) - 3 * π / 4 = -(π - π / 4) := by ring
    rw [this, Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four]
  have h3 : Real.cos (π / 2 - π / 4) = √2 / 2 := by
    have : π / 2 - π / 4 = π / 4 := by ring
    rw [this, Real.cos_pi_div_four]
  have h4 : Real.cos (π / 2 - 3 * π / 4) = √2 / 2 := by
    have : π / 2 - 3 * π / 4 = -(π / 4) := by ring
    rw [this, Real.cos_neg, Real.cos_pi_div_four]
  unfold E
  rw [h1, h2, h3, h4]; ring

theorem chsh_abs : |E (0 - π / 4) - E (0 - 3 * π / 4) + E (π / 2 - π / 4) + E (π / 2 - 3 * π / 4)|
    = 2 * √2 := by
  rw [chsh_value, abs_neg, abs_of_nonneg (by positivity)]

/-- 고전 숨은변수(무작위 축) 직선 모형 L(θ) = -1 + 2θ/π (0 ≤ θ ≤ π). 같은 네 각에서 |S| = 2. -/
noncomputable def L (θ : ℝ) : ℝ := -1 + 2 * |θ| / π

theorem classical_chsh :
    L (0 - π / 4) - L (0 - 3 * π / 4) + L (π / 2 - π / 4) + L (π / 2 - 3 * π / 4) = -2 := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  have hpp := Real.pi_pos
  unfold L
  rw [show (0:ℝ) - π / 4 = -(π / 4) by ring, abs_neg, abs_of_pos (by positivity),
    show (0:ℝ) - 3 * π / 4 = -(3 * π / 4) by ring, abs_neg, abs_of_pos (by positivity),
    show π / 2 - π / 4 = π / 4 by ring, abs_of_pos (by positivity),
    show π / 2 - 3 * π / 4 = -(π / 4) by ring, abs_neg, abs_of_pos (by positivity)]
  field_simp
  ring

theorem two_lt_two_sqrt_two : (2 : ℝ) < 2 * √2 := by
  have : (1 : ℝ) < √2 := by
    rw [show (1:ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! 호프 매개화: (cos(θ/2), e^{iφ} sin(θ/2)) 는 단위 벡터, 전체 위상 e^{iγ} 곱해도 단위 -/
theorem hopf_unit (θ φ γ : ℝ) :
    ‖Complex.exp (γ * Complex.I) * (Real.cos (θ / 2) : ℂ)‖ ^ 2 +
    ‖Complex.exp (γ * Complex.I) * (Complex.exp (φ * Complex.I) * (Real.sin (θ / 2) : ℂ))‖ ^ 2
      = 1 := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Complex.norm_real]
  simp only [one_mul, Real.norm_eq_abs, sq_abs]
  exact Real.cos_sq_add_sin_sq _

/-! concurrence C = 2|ab| (a|00> + b|11>, |a|^2+|b|^2=1) -/
noncomputable def conc (a b : ℂ) : ℝ := 2 * ‖a‖ * ‖b‖

theorem conc_le_one (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : conc a b ≤ 1 := by
  unfold conc; nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem conc_zero_iff (a b : ℂ) : conc a b = 0 ↔ a = 0 ∨ b = 0 := by
  unfold conc
  constructor
  · intro h
    have : ‖a‖ * ‖b‖ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; exact norm_eq_zero.mp h
    · right; exact norm_eq_zero.mp h
  · rintro (h | h) <;> simp [h]

theorem conc_max (a b : ℂ) (h : ‖a‖ = ‖b‖) (h2 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : conc a b = 1 := by
  unfold conc; rw [← h] at h2 ⊢; nlinarith

end KimbanjiEntangle

#print axioms KimbanjiEntangle.singlet_correlation
#print axioms KimbanjiEntangle.chsh_value
#print axioms KimbanjiEntangle.chsh_abs
#print axioms KimbanjiEntangle.classical_chsh
#print axioms KimbanjiEntangle.two_lt_two_sqrt_two
#print axioms KimbanjiEntangle.hopf_unit
#print axioms KimbanjiEntangle.conc_le_one
#print axioms KimbanjiEntangle.conc_zero_iff
#print axioms KimbanjiEntangle.conc_max

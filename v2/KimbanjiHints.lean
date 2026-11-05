import Mathlib
open Complex
-- 황금비 p (p^2 = p+1) 와 허수단위: (p^3 + i)^2 = 2 p^3 (2 + i)
theorem phi_cube_I (p : ℝ) (h : p^2 = p + 1) :
    ((p:ℂ)^3 + I)^2 = 2 * (p:ℂ)^3 * (2 + I) := by
  have hC : (p:ℂ)^2 = (p:ℂ) + 1 := by exact_mod_cast h
  have hI : I^2 = -1 := Complex.I_sq
  linear_combination ((p:ℂ)^4 + (p:ℂ)^3 + 2*(p:ℂ)^2 - (p:ℂ) + 1) * hC + hI
theorem phi_cube (p : ℝ) (h : p^2 = p + 1) : p^3 = 2*p + 1 := by nlinarith [h]
theorem phi_six (p : ℝ) (h : p^2 = p + 1) : p^6 = 8*p + 5 := by nlinarith [h, phi_cube p h]
-- 더미 시험: i 를 1 로 바꾸면 거짓 (p>0)
theorem phi_cube_one_false (p : ℝ) (h : p^2 = p + 1) : (p^3 + 1)^2 ≠ 2 * p^3 * (2 + 1) := by
  have h3 := phi_cube p h; have h6 := phi_six p h
  intro H; nlinarith [H, h3, h6]
-- 피보나치 다항식(함수체 황금비) : u^2 = T u + 1 이면 u * (T - u) = -1  (노름 −1)
theorem fibpoly_norm (T u : ℝ) (h : u^2 = T*u + 1) : u * (T - u) = -1 := by nlinarith [h]
-- 조화수 H_n 의 한 걸음 (Mathlib harmonic_succ 인용)
theorem harmonic_step (n : ℕ) : harmonic (n+1) = harmonic n + (↑(n+1):ℚ)⁻¹ := harmonic_succ n

import Mathlib
/-!
# 안(유한체)의 리만 가설 — 쌍고리 곡면 y² = x⁶ + a x³ + 1 의 정수 판정
실 Weil 다항식 t² − s t + P (s = −a₁, P = a₂ − 2p) 의 두 근 β 가 β² ≤ 4p 를 만족하면
L 다항식의 네 근이 모두 |α| = √p 위에 있다(베유 정리의 그 경우). 점 수 N₁, N₂ 는 정확 열거와
PARI hyperellcharpoly 로 두 번 셈(불일치 0). 여기서는 그 정수에서 판정이 성립함을 증명한다.
-/

/-- 일반 판정: D = s² − 4P = q², M = 16p − s² − D ≥ 0, 4s²D ≤ M² 이면 두 근 (s ± q)/2 의 제곱이 4p 이하. -/
theorem inside_RH_criterion (s P p q : ℝ) (_hq : 0 ≤ q) (hqD : q^2 = s^2 - 4*P)
    (hM : 0 ≤ 16*p - s^2 - (s^2 - 4*P))
    (h : 4*s^2*(s^2 - 4*P) ≤ (16*p - s^2 - (s^2 - 4*P))^2) :
    ((s + q)/2)^2 ≤ 4*p ∧ ((s - q)/2)^2 ≤ 4*p := by
  have key : (2*s*q)^2 ≤ (16*p - s^2 - (s^2 - 4*P))^2 := by
    have e : (2*s*q)^2 = 4*s^2*q^2 := by ring
    rw [e, hqD]; exact h
  have h1 : 2*s*q ≤ 16*p - s^2 - (s^2 - 4*P) := by
    by_contra hc0; have hc := lt_of_not_ge hc0
    have hpos : 0 < (2*s*q - (16*p - s^2 - (s^2 - 4*P))) * (2*s*q + (16*p - s^2 - (s^2 - 4*P))) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [key, hpos]
  have h2 : -(2*s*q) ≤ 16*p - s^2 - (s^2 - 4*P) := by
    by_contra hc0; have hc := lt_of_not_ge hc0
    have hpos : 0 < (-(2*s*q) - (16*p - s^2 - (s^2 - 4*P))) * (-(2*s*q) + (16*p - s^2 - (s^2 - 4*P))) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [key, hpos]
  constructor
  · have e : ((s + q)/2)^2 = (s^2 + 2*s*q + q^2)/4 := by ring
    rw [e, hqD]; linarith [h1]
  · have e : ((s - q)/2)^2 = (s^2 - 2*s*q + q^2)/4 := by ring
    rw [e, hqD]; linarith [h2]

/-- a = 1, p = 7: N₁ = 10, N₂ = 76, s = -2, P = 1, D = 0 = 0². -/
theorem inside_RH_a1_p7 : (((-2:ℝ) + 0)/2)^2 ≤ 4*7 ∧ (((-2:ℝ) - 0)/2)^2 ≤ 4*7 :=
  inside_RH_criterion (-2) (1) 7 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 1, p = 11: N₁ = 12, N₂ = 148, s = 0, P = -9, D = 36 = 6². -/
theorem inside_RH_a1_p11 : (((0:ℝ) + 6)/2)^2 ≤ 4*11 ∧ (((0:ℝ) - 6)/2)^2 ≤ 4*11 :=
  inside_RH_criterion (0) (-9) 11 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 1, p = 13: N₁ = 16, N₂ = 220, s = -2, P = 1, D = 0 = 0². -/
theorem inside_RH_a1_p13 : (((-2:ℝ) + 0)/2)^2 ≤ 4*13 ∧ (((-2:ℝ) - 0)/2)^2 ≤ 4*13 :=
  inside_RH_criterion (-2) (1) 13 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 1, p = 17: N₁ = 18, N₂ = 286, s = 0, P = -36, D = 144 = 12². -/
theorem inside_RH_a1_p17 : (((0:ℝ) + 12)/2)^2 ≤ 4*17 ∧ (((0:ℝ) - 12)/2)^2 ≤ 4*17 :=
  inside_RH_criterion (0) (-36) 17 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 1, p = 19: N₁ = 28, N₂ = 406, s = -8, P = 16, D = 0 = 0². -/
theorem inside_RH_a1_p19 : (((-8:ℝ) + 0)/2)^2 ≤ 4*19 ∧ (((-8:ℝ) - 0)/2)^2 ≤ 4*19 :=
  inside_RH_criterion (-8) (16) 19 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 1, p = 23: N₁ = 24, N₂ = 604, s = 0, P = -9, D = 36 = 6². -/
theorem inside_RH_a1_p23 : (((0:ℝ) + 6)/2)^2 ≤ 4*23 ∧ (((0:ℝ) - 6)/2)^2 ≤ 4*23 :=
  inside_RH_criterion (0) (-9) 23 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 44, p = 11: N₁ = 12, N₂ = 166, s = 0, P = 0, D = 0 = 0². -/
theorem inside_RH_a44_p11 : (((0:ℝ) + 0)/2)^2 ≤ 4*11 ∧ (((0:ℝ) - 0)/2)^2 ≤ 4*11 :=
  inside_RH_criterion (0) (0) 11 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 44, p = 13: N₁ = 22, N₂ = 190, s = -8, P = 16, D = 0 = 0². -/
theorem inside_RH_a44_p13 : (((-8:ℝ) + 0)/2)^2 ≤ 4*13 ∧ (((-8:ℝ) - 0)/2)^2 ≤ 4*13 :=
  inside_RH_criterion (-8) (16) 13 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 44, p = 17: N₁ = 18, N₂ = 340, s = 0, P = -9, D = 36 = 6². -/
theorem inside_RH_a44_p17 : (((0:ℝ) + 6)/2)^2 ≤ 4*17 ∧ (((0:ℝ) - 6)/2)^2 ≤ 4*17 :=
  inside_RH_criterion (0) (-9) 17 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = 44, p = 19: N₁ = 16, N₂ = 430, s = 4, P = 4, D = 0 = 0². -/
theorem inside_RH_a44_p19 : (((4:ℝ) + 0)/2)^2 ≤ 4*19 ∧ (((4:ℝ) - 0)/2)^2 ≤ 4*19 :=
  inside_RH_criterion (4) (4) 19 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 7: N₁ = 4, N₂ = 70, s = 4, P = 4, D = 0 = 0². -/
theorem inside_RH_am45_p7 : (((4:ℝ) + 0)/2)^2 ≤ 4*7 ∧ (((4:ℝ) - 0)/2)^2 ≤ 4*7 :=
  inside_RH_criterion (4) (4) 7 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 11: N₁ = 12, N₂ = 148, s = 0, P = -9, D = 36 = 6². -/
theorem inside_RH_am45_p11 : (((0:ℝ) + 6)/2)^2 ≤ 4*11 ∧ (((0:ℝ) - 6)/2)^2 ≤ 4*11 :=
  inside_RH_criterion (0) (-9) 11 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 13: N₁ = 22, N₂ = 190, s = -8, P = 16, D = 0 = 0². -/
theorem inside_RH_am45_p13 : (((-8:ℝ) + 0)/2)^2 ≤ 4*13 ∧ (((-8:ℝ) - 0)/2)^2 ≤ 4*13 :=
  inside_RH_criterion (-8) (16) 13 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 17: N₁ = 18, N₂ = 358, s = 0, P = 0, D = 0 = 0². -/
theorem inside_RH_am45_p17 : (((0:ℝ) + 0)/2)^2 ≤ 4*17 ∧ (((0:ℝ) - 0)/2)^2 ≤ 4*17 :=
  inside_RH_criterion (0) (0) 17 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 19: N₁ = 34, N₂ = 340, s = -14, P = 49, D = 0 = 0². -/
theorem inside_RH_am45_p19 : (((-14:ℝ) + 0)/2)^2 ≤ 4*19 ∧ (((-14:ℝ) - 0)/2)^2 ≤ 4*19 :=
  inside_RH_criterion (-14) (49) 19 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- a = -45, p = 23: N₁ = 24, N₂ = 604, s = 0, P = -9, D = 36 = 6². -/
theorem inside_RH_am45_p23 : (((0:ℝ) + 6)/2)^2 ≤ 4*23 ∧ (((0:ℝ) - 6)/2)^2 ≤ 4*23 :=
  inside_RH_criterion (0) (-9) 23 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms inside_RH_criterion
#print axioms inside_RH_am45_p19

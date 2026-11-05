import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! 달걀 CRT 사영: 가능분만. 정수 조각(omega/decide)과 실수 대수(c^2+s^2=1 가정). -/

namespace KimbanjiEggCRT

/-- 그림자: (n mod 2, n mod 3, n mod 5, n mod 7). -/
def shadow (n : Nat) : Nat × Nat × Nat × Nat := (n % 2, n % 3, n % 5, n % 7)

/-- 0..209 에서 그림자는 단사 (CRT 구체; 2*3*5*7 = 210). -/
theorem shadow_inj (a b : Nat) (ha : a < 210) (hb : b < 210)
    (h : shadow a = shadow b) : a = b := by
  simp only [shadow, Prod.mk.injEq] at h
  omega

/-- 일반 CRT 판 (서로소 두 수): Nat.ModEq 로. -/
theorem crt_two (a b m n : Nat) (hmn : Nat.Coprime m n)
    (h1 : Nat.ModEq m a b) (h2 : Nat.ModEq n a b) : Nat.ModEq (m * n) a b :=
  (Nat.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨h1, h2⟩

/-- 범위가 210 을 넘으면 단사가 깨짐: 0 과 210. -/
theorem shadow_period : shadow 0 = shadow 210 := by decide

/-- 르장드르 기호(소수 p, 정수 a): 0, 1, -1. -/
def leg (p a : Nat) : Int :=
  if a % p = 0 then 0
  else if (List.range p).any (fun x => x * x % p == a % p) then 1 else -1

/-- F13 의 부호표 a = 0..12. -/
theorem leg13_table :
    (List.range 13).map (leg 13) = [0,1,-1,1,1,-1,-1,-1,-1,1,1,-1,1] := by decide

/-- 이차잉여는 정확히 6개: 1,3,4,9,10,12. -/
theorem leg13_residues :
    ((List.range 13).filter (fun a => leg 13 a = 1)) = [1,3,4,9,10,12] := by decide

/-- 이차 지표의 곱셈성 (F13 전수). -/
theorem leg13_mult : ∀ a : Fin 13, ∀ b : Fin 13,
    leg 13 (a.val * b.val) = leg 13 a.val * leg 13 b.val := by decide

/-- 스테레오 사영 x = c/(1-s) (c^2+s^2=1, s≠1): x^2 = (1+s)/(1-s). -/
theorem stereo_sq (c s : ℝ) (h : c^2 + s^2 = 1) (hs : s ≠ 1) :
    (c / (1 - s))^2 = (1 + s) / (1 - s) := by
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  field_simp
  nlinarith [h]

/-- 뒤집기: s≠±1 이면 x(θ)·x(−θ) = 1, 여기서 x(−θ) = c/(1+s). -/
theorem stereo_flip (c s : ℝ) (h : c^2 + s^2 = 1) (hs : s ≠ 1) (hs' : s ≠ -1) :
    (c / (1 - s)) * (c / (1 + s)) = 1 := by
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have h2 : (1 + s) ≠ 0 := fun e => hs' (by linarith)
  have h3 : c^2 = (1 - s) * (1 + s) := by nlinarith [h]
  field_simp
  exact h3

/-- 엡실론 판: θ = π/2 − ε 일 때 c = sin ε, s = cos ε, x = (1+s)... 대수식 c/(1-s)
    는 s→1 에서 분모가 0 에 접근 (|x| 가 커짐)의 정확 항등: x·(1−s) = c. -/
theorem stereo_mul (c s : ℝ) (hs : s ≠ 1) : (c / (1 - s)) * (1 - s) = c := by
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  field_simp

end KimbanjiEggCRT


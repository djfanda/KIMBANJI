import Mathlib
/-! 진법 정리 · 닫힌 행 정리의 유한 조각 — 린 4 (2026-11-05). 모두 decide (native_decide · sorry · axiom 없음). -/
namespace Kimbanji.Digit
open Finset

/-- 비등방 2 차 노름 형식: GF(3)² 에서 0 에서만 0. -/
def N2 (u : Fin 2 → ZMod 3) : ZMod 3 := u 0 ^ 2 + u 1 ^ 2
theorem N2_eq_zero_iff : ∀ u : Fin 2 → ZMod 3, N2 u = 0 ↔ u = 0 := by decide

/-- 3 차 노름형 형식 N₃ = u₁² + u₂² + u₃² + u₁u₂u₃: GF(3)³ 에서 0 에서만 0. -/
def N3 (u : Fin 3 → ZMod 3) : ZMod 3 := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 0 * u 1 * u 2
theorem N3_eq_zero_iff : ∀ u : Fin 3 → ZMod 3, N3 u = 0 ↔ u = 0 := by decide

/-- 상수항 0 인 GF(2) 차수 ≤ 2 세 변수 다항식은 OR₃ 이 될 수 없다 (계수 64 가지 전수). -/
def deg2poly (c : Fin 6 → ZMod 2) (y : Fin 3 → Bool) : ZMod 2 :=
  let b : Fin 3 → ZMod 2 := fun i => if y i then 1 else 0
  c 0 * b 0 + c 1 * b 1 + c 2 * b 2 + c 3 * b 0 * b 1 + c 4 * b 0 * b 2 + c 5 * b 1 * b 2
theorem or3_not_degree_two :
    ∀ c : Fin 6 → ZMod 2, ¬ (∀ y : Fin 3 → Bool, y ≠ (fun _ => false) → deg2poly c y = 1) := by decide

/-- 차수 1, n = 5: Σ x_i (법 6) 은 0 에서만 0 — d₆*(5) ≤ 1. -/
def wt {n : ℕ} (x : Fin n → Bool) : ℕ := (univ.filter fun i => x i = true).card
theorem witness5 : ∀ x : Fin 5 → Bool, ((wt x : ZMod 6) = 0 ↔ x = fun _ => false) := by decide

/-- 차수 2, n = 10 (자리 둘). 다항식은 두 블록(앞 다섯 · 뒤 다섯)의 무게 w₁, w₂ ∈ {0..5} 에만 의존한다:
    P₂ = w₁ + w₂ + w₁w₂ (법 2) = OR(두 짝홀), P₃ = w₁² + w₂² (법 3). x ≠ 0 ⇔ (w₁, w₂) ≠ (0, 0) 이므로
    아래가 d₆*(10) ≤ 2 의 검증이다. -/
def P2w (w1 w2 : Fin 6) : ZMod 2 := (w1.val : ZMod 2) + (w2.val : ZMod 2) + (w1.val : ZMod 2) * (w2.val : ZMod 2)
def P3w (w1 w2 : Fin 6) : ZMod 3 := (w1.val : ZMod 3) ^ 2 + (w2.val : ZMod 3) ^ 2
theorem witness10 : ∀ w1 w2 : Fin 6, ((P2w w1 w2 = 0 ∧ P3w w1 w2 = 0) ↔ (w1 = 0 ∧ w2 = 0)) := by decide

/-- 차수 3, n = 15 (자리 셋): 세 블록 무게 w₁, w₂, w₃ ∈ {0..5}. P₂ = 1 − Π(1 − w_j) (법 2),
    P₃ = N₃(w₁, w₂, w₃) (법 3). 동시에 0 인 것은 (0,0,0) 뿐 — d₆*(15) ≤ 3. -/
def P2w3 (a b c : Fin 6) : ZMod 2 := 1 - (1 - (a.val : ZMod 2)) * (1 - (b.val : ZMod 2)) * (1 - (c.val : ZMod 2))
def P3w3 (a b c : Fin 6) : ZMod 3 :=
  (a.val : ZMod 3) ^ 2 + (b.val : ZMod 3) ^ 2 + (c.val : ZMod 3) ^ 2 + (a.val : ZMod 3) * (b.val : ZMod 3) * (c.val : ZMod 3)
theorem witness15 : ∀ a b c : Fin 6, ((P2w3 a b c = 0 ∧ P3w3 a b c = 0) ↔ (a = 0 ∧ b = 0 ∧ c = 0)) := by decide

end Kimbanji.Digit
#print axioms Kimbanji.Digit.N2_eq_zero_iff
#print axioms Kimbanji.Digit.N3_eq_zero_iff
#print axioms Kimbanji.Digit.or3_not_degree_two
#print axioms Kimbanji.Digit.witness5
#print axioms Kimbanji.Digit.witness10
#print axioms Kimbanji.Digit.witness15

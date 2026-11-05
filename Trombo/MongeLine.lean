/-
몽주의 직선 — 원 셋의 닮음 중심 셋은 한 직선 위에 (린 4 코어 · 모든 정수 · 동차 좌표)

원 i 의 중심 cᵢ = (xᵢ, yᵢ) · 반지름 rᵢ. 두 원 i, j 의 바깥 닮음 중심(두 바깥 공통접선이 만나는 점)은
  Eᵢⱼ = (rⱼ cᵢ − rᵢ cⱼ) / (rⱼ − rᵢ)
이고, 안쪽 닮음 중심(안쪽 공통접선이 만나는 점)은
  Iᵢⱼ = (rⱼ cᵢ + rᵢ cⱼ) / (rⱼ + rᵢ)
이다. 분모를 셋째 좌표로 두는 동차 좌표 (rⱼxᵢ − rᵢxⱼ : rⱼyᵢ − rᵢyⱼ : rⱼ − rᵢ) 에서 세 점이 한 직선 위에 있다는 것은
3 × 3 행렬식이 0 이라는 것과 같다. 아래는 그 행렬식이 «모든» 정수 값에서 0 임을 보인다 (다항 항등식 · grind).
  · monge_external : 바깥 닮음 중심 E₁₂ · E₁₃ · E₂₃ 은 한 직선 위 (몽주 1798 · 고전 정리)
  · monge_mixed : 바깥 하나와 안쪽 둘 E₁₂ · I₁₃ · I₂₃ 도 한 직선 위
  · 시범 : 무작위로 고른 정수 원 셋에서 행렬식이 0

저자의 읽기 (수학 주장 아님) : 두 출발점에서 만든 피자 조각 셋의 만나는 점이 한 직선 = «제타선».
이 직선은 원 셋의 기하에서 오는 몽주의 직선이며, 리만 제타 함수의 임계선과 수학적으로 같은 것은 아니다.
-/
namespace MongeLine

/-- 3 × 3 행렬식 -/
def det3 (a b c d e f g h i : Int) : Int :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- 바깥 닮음 중심 (동차) -/
def ext (x₁ y₁ r₁ x₂ y₂ r₂ : Int) : Int × Int × Int := (r₂ * x₁ - r₁ * x₂, r₂ * y₁ - r₁ * y₂, r₂ - r₁)
/-- 안쪽 닮음 중심 (동차) -/
def int (x₁ y₁ r₁ x₂ y₂ r₂ : Int) : Int × Int × Int := (r₂ * x₁ + r₁ * x₂, r₂ * y₁ + r₁ * y₂, r₂ + r₁)

def coll (P Q R : Int × Int × Int) : Int :=
  det3 P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2 R.1 R.2.1 R.2.2

/-- 몽주의 정리 (바깥) : 원 셋의 바깥 닮음 중심 셋의 동차 좌표 행렬식은 언제나 0 — 한 직선 위 -/
theorem monge_external (x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ : Int) :
    coll (ext x₁ y₁ r₁ x₂ y₂ r₂) (ext x₁ y₁ r₁ x₃ y₃ r₃) (ext x₂ y₂ r₂ x₃ y₃ r₃) = 0 := by
  simp only [coll, ext, det3]
  grind

/-- 몽주의 정리 (섞음) : 바깥 E₁₂ 와 안쪽 I₁₃ · I₂₃ 도 한 직선 위 -/
theorem monge_mixed (x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ : Int) :
    coll (ext x₁ y₁ r₁ x₂ y₂ r₂) (int x₁ y₁ r₁ x₃ y₃ r₃) (int x₂ y₂ r₂ x₃ y₃ r₃) = 0 := by
  simp only [coll, ext, int, det3]
  grind

/-- 시범 : 무작위 정수 원 셋 — 중심 (0, 0) · (7, 1) · (3, 6), 반지름 1 · 2 · 4 -/
theorem demo_random :
    coll (ext 0 0 1 7 1 2) (ext 0 0 1 3 6 4) (ext 7 1 2 3 6 4) = 0 ∧
    (ext 0 0 1 7 1 2).2.2 ≠ 0 ∧ (ext 0 0 1 3 6 4).2.2 ≠ 0 ∧ (ext 7 1 2 3 6 4).2.2 ≠ 0 := by decide

/-- 대조 : 닮음 중심이 아닌 아무 세 점은 한 직선 위가 아닐 수 있음 (행렬식 ≠ 0) -/
theorem control_not_collinear : coll (0, 0, 1) (1, 0, 1) (0, 1, 1) ≠ 0 := by decide

end MongeLine

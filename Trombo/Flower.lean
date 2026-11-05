/-
꽃 — 원 일곱 (가운데 하나 + 둘레 여섯) 안의 도형 모두와 태극이 도는 자리 (린 4 코어만 · Mathlib 없음)

삼각 격자 (아이젠슈타인) 좌표 : 점 (a, b) = a·e₁ + b·e₂ (e₁ = (1, 0) · e₂ = (½, √3/2)).
  길이² = a² + ab + b² · 두 배 내적 = 2aa' + 2bb' + ab' + a'b · 넓이 = 신발끈 합 × √3/4 (작은 정삼각형 하나 = 1).
원의 중심 : 0 = (0, 0) · V0 … V5 = (1, 0) · (0, 1) · (−1, 1) · (−1, 0) · (0, −1) · (1, −1) — 이웃한 원 사이는 1.
· 넓이 (작은 정삼각형 단위 · 육각형 = 6) : 작은 정삼각형 1 · 120° 삼각형 1 · 마름모 (정육면체 면 · 사각뿔의 밑면) 2 ·
  큰 정삼각형 3 · 사다리꼴 3 · 직사각형 1 × √3 은 4 · 오각형 (집 꼴 = 직사각형 + 삼각형) 5 · 육망성의 가운데 육각형 2 ·
  육망성 4 · 이웃 원이 맞닿는 점의 육각형 9/2 · 가운데 원과 맞닿는 점의 육각형 3/2 — 곧은 도형의 넓이는 모두 √3/4 의 유리수 배.
· 각 : 직사각형의 변² 1 과 3 · 대각선² 4 (지름 2) · 오각형의 각 90° · 120° · 120° · 120° · 90°.
· 태극이 도는 자리 : 60° 돌림 (a, b) ↦ (−b, a + b) 는 정수 행렬 (대각합 1 · 행렬식 1 · 차수 6) 이고 원 중심 일곱을
  자기들끼리 보낸다 (가운데는 그대로) — 여섯 겹은 원의 중심.
  삼각형 무게중심 (e₁ + e₂)/3 둘레 120° 돌림 (a, b) ↦ (1 − a − b, a) 는 격자를 격자로 · 차수 3 · 0 → V0 → V1 → 0 — 세 겹은 삼각형 자리.
  맞닿는 점 e₁/2 둘레 180° 돌림 (a, b) ↦ (1 − a, −b) 는 0 ↔ V0 — 두 겹은 맞닿는 점.
  다섯 겹은 격자에 자리가 없다 (Crystal.no_five) — 다섯은 가운데 한 점에서만, 되풀이되지 않는다.

검증 : lake build (Trombo.Crystal 을 불러 쓴다)
-/
import Trombo.Crystal

namespace Trombo.Flower

abbrev Pt := Int × Int

def O : Pt := (0, 0)
def V : Nat → Pt
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 1)
  | 3 => (-1, 0)
  | 4 => (0, -1)
  | _ => (1, -1)

def norm (p : Pt) : Int := p.1 * p.1 + p.1 * p.2 + p.2 * p.2
def sub (p q : Pt) : Pt := (p.1 - q.1, p.2 - q.2)
def dot2 (u v : Pt) : Int := 2 * u.1 * v.1 + 2 * u.2 * v.2 + u.1 * v.2 + v.1 * u.2

/-- 신발끈 합 (닫힌 다각형) -/
def shoe (P : List Pt) : Int :=
  ((List.range P.length).map fun i =>
    let p := P.getD i (0, 0)
    let q := P.getD ((i + 1) % P.length) (0, 0)
    p.1 * q.2 - q.1 * p.2).foldl (· + ·) 0

def hexagon : List Pt := [V 0, V 1, V 2, V 3, V 4, V 5]
def smallTri : List Pt := [O, V 0, V 1]
def wideTri : List Pt := [V 0, V 1, V 2]
def rhombus : List Pt := [O, V 0, V 1, V 2]
def bigTri : List Pt := [V 0, V 2, V 4]
def trapezoid : List Pt := [V 0, V 1, V 2, V 3]
def rectangle : List Pt := [V 0, V 1, V 3, V 4]
def pentagon : List Pt := [V 0, V 1, V 2, V 3, V 4]
/-- 육망성의 가운데 육각형 (×3) · 이웃 원이 맞닿는 점의 육각형 (×2) · 가운데 원과 맞닿는 점의 육각형 (×2) -/
def starCore3 : List Pt := [(1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]
def touchOuter2 : List Pt := [(1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]
def touchInner2 : List Pt := hexagon

/-- ★ 넓이 (√3/4 단위) : 6 · 1 · 1 · 2 · 3 · 3 · 4 · 5 · 2 · 9/2 · 3/2 — 육망성 = 큰 삼각형 둘 − 가운데 = 4 -/
theorem areas :
    shoe hexagon = 6 ∧ shoe smallTri = 1 ∧ shoe wideTri = 1 ∧ shoe rhombus = 2 ∧ shoe bigTri = 3 ∧
    shoe trapezoid = 3 ∧ shoe rectangle = 4 ∧ shoe pentagon = 5 ∧
    shoe starCore3 = 18 ∧ shoe touchOuter2 = 18 ∧ shoe touchInner2 = 6 ∧
    (2 * shoe bigTri) * 9 - shoe starCore3 = 4 * 9 := by
  decide

/-- 넓이의 맞춤 : 마름모 셋 (정육면체의 보이는 면 · 사각뿔 셋의 밑면) 의 넓이 = 육각형 · 오각형 = 직사각형 + 120° 삼각형 · 육각형 = 직사각형 + 삼각형 둘 (넓이가 같다는 문장 — 겹침 없이 채운다는 것은 그림) -/
theorem pieces :
    3 * shoe rhombus = shoe hexagon ∧ shoe pentagon = shoe rectangle + shoe wideTri ∧
    shoe hexagon = shoe rectangle + 2 * shoe wideTri ∧ shoe hexagon = 6 * shoe smallTri := by
  decide

/-- 길이와 각 : 직사각형의 변² 1 · 3 · 대각선² 4 · 오각형의 각 90° (두 배 내적 0) · 120° (두 배 내적 −1, 길이 1 · 1) -/
theorem lengths_angles :
    norm (sub (V 1) (V 0)) = 1 ∧ norm (sub (V 3) (V 1)) = 3 ∧ norm (sub (V 3) (V 0)) = 4 ∧
    dot2 (sub (V 4) (V 0)) (sub (V 1) (V 0)) = 0 ∧ dot2 (sub (V 0) (V 4)) (sub (V 3) (V 4)) = 0 ∧
    dot2 (sub (V 0) (V 1)) (sub (V 2) (V 1)) = -1 ∧ dot2 (sub (V 1) (V 2)) (sub (V 3) (V 2)) = -1 ∧
    dot2 (sub (V 2) (V 3)) (sub (V 4) (V 3)) = -1 ∧
    norm (sub (V 0) O) = 1 ∧ norm (sub (V 2) (V 0)) = 3 := by
  decide

/-! ## 태극이 도는 자리 -/

def r60 (p : Pt) : Pt := (-p.2, p.1 + p.2)
def r120c (p : Pt) : Pt := (1 - p.1 - p.2, p.1)
def r180m (p : Pt) : Pt := (1 - p.1, -p.2)

/-- 60° 돌림의 정수 행렬 : 대각합 1 · 행렬식 1 · 차수 6 (Crystal 의 바일 상자 q = 1 칸의 a = 1) -/
def R60 : Crystal.M2 := ⟨0, -1, 1, 1⟩

theorem six_fold :
    (List.range 6).all (fun k => r60 (V k) == V ((k + 1) % 6)) = true ∧ r60 O = O ∧
    (List.range 13).all (fun i => (List.range 13).all fun j =>
      norm (r60 ((i : Int) - 6, (j : Int) - 6)) == norm ((i : Int) - 6, (j : Int) - 6)) = true ∧
    Crystal.M2.tr R60 = 1 ∧ Crystal.M2.det R60 = 1 ∧ Crystal.M2.pw R60 6 = Crystal.M2.one ∧
    Crystal.M2.pw R60 2 ≠ Crystal.M2.one ∧ Crystal.M2.pw R60 3 ≠ Crystal.M2.one := by
  decide

/-- 세 겹 (삼각형 자리) : 0 → V0 → V1 → 0 · 세 번이면 제자리 · 길이를 지킨다 -/
theorem three_fold :
    r120c O = V 0 ∧ r120c (V 0) = V 1 ∧ r120c (V 1) = O ∧
    (List.range 13).all (fun i => (List.range 13).all fun j =>
      let p : Pt := ((i : Int) - 6, (j : Int) - 6)
      r120c (r120c (r120c p)) == p &&
      (List.range 13).all fun k => (List.range 13).all fun l =>
        let q : Pt := ((k : Int) - 6, (l : Int) - 6)
        norm (sub (r120c p) (r120c q)) == norm (sub p q)) = true := by
  decide +kernel

/-- 두 겹 (맞닿는 점) : 0 ↔ V0 · 두 번이면 제자리 -/
theorem two_fold :
    r180m O = V 0 ∧ r180m (V 0) = O ∧
    (List.range 13).all (fun i => (List.range 13).all fun j =>
      let p : Pt := ((i : Int) - 6, (j : Int) - 6)
      r180m (r180m p) == p) = true := by
  decide

/-- ★ 다섯 겹은 격자에 자리가 없다 : 격자를 지키는 일차 돌림 (정수 행렬) 이 다섯 번에 제자리면 처음부터 제자리 -/
theorem no_five_seat (A : Crystal.M2) (h : Crystal.M2.pw A 5 = Crystal.M2.one) : A = Crystal.M2.one :=
  Crystal.no_five A h

/-! ## 모든 점에서 (창 13 × 13 이 아니라) -/

/-- 60° 돌림 r60 은 정수 행렬 R60 의 작용 그 자체 -/
theorem r60_is_R60 (p : Pt) : r60 p = (R60.a * p.1 + R60.b * p.2, R60.c * p.1 + R60.d * p.2) := by
  cases p; simp [r60, R60]

/-- ★ 세 돌림은 모든 점에서 길이를 지키고, 각각 6 · 3 · 2 번에 제자리 -/
theorem turns_everywhere :
    (∀ p q : Pt, norm (sub (r60 p) (r60 q)) = norm (sub p q)) ∧
    (∀ p q : Pt, norm (sub (r120c p) (r120c q)) = norm (sub p q)) ∧
    (∀ p q : Pt, norm (sub (r180m p) (r180m q)) = norm (sub p q)) ∧
    (∀ p : Pt, r60 (r60 (r60 (r60 (r60 (r60 p))))) = p) ∧
    (∀ p : Pt, r120c (r120c (r120c p)) = p) ∧ (∀ p : Pt, r180m (r180m p) = p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q; cases p; cases q; simp only [norm, sub, r60]; grind
  · intro p q; cases p; cases q; simp only [norm, sub, r120c]; grind
  · intro p q; cases p; cases q; simp only [norm, sub, r180m]; grind
  · intro p; cases p; simp only [r60, Prod.mk.injEq]; constructor <;> grind
  · intro p; cases p; simp only [r120c, Prod.mk.injEq]; constructor <;> grind
  · intro p; cases p; simp only [r180m, Prod.mk.injEq]; constructor <;> grind

/-- 배율을 푼 넓이 : 가운데 육각형 18 = 9 × 2 · 맞닿는 점의 육각형 18 = 4 × 9/2 · 6 = 4 × 3/2 (같은 모양의 육각형을 배율 3 · 2 · 2 로 적은 것) -/
theorem scaled_areas :
    shoe starCore3 = 9 * 2 ∧ 2 * shoe touchOuter2 = 4 * 9 ∧ 2 * shoe touchInner2 = 4 * 3 := by decide

/-- 오각형의 120° 각을 이루는 변의 길이는 모두 1 -/
theorem pentagon_unit_sides :
    norm (sub (V 1) (V 0)) = 1 ∧ norm (sub (V 2) (V 1)) = 1 ∧ norm (sub (V 3) (V 2)) = 1 ∧
    norm (sub (V 4) (V 3)) = 1 ∧ norm (sub (V 0) (V 4)) = 3 := by decide

/-- 두 육각형의 좌표 : 맞닿는 점 육각형 (×2) 의 꼭짓점은 V k + V (k + 1) (이웃 원 중심의 가운데 × 2) 이고,
  육망성 가운데 육각형 (×3) 의 꼭짓점도 같은 V k + V (k + 1) 로 두 큰 삼각형의 변 V(k − 1)V(k + 1) · V(k)V(k + 2) 위에 있다
  — 그래서 가운데 육각형은 맞닿는 점 육각형의 2/3 배 (넓이 2 = 9/2 × 4/9) -/
theorem core_and_contacts :
    touchOuter2 = (List.range 6).map (fun k => ((V k).1 + (V ((k + 1) % 6)).1, (V k).2 + (V ((k + 1) % 6)).2)) ∧
    starCore3 = touchOuter2 ∧
    (List.range 6).all (fun k =>
      let P := starCore3.getD k (0, 0)
      let A := V ((k + 5) % 6)
      let B := V ((k + 1) % 6)
      let C := V k
      let D := V ((k + 2) % 6)
      (3 * B.1 - 3 * A.1) * (P.2 - 3 * A.2) - (3 * B.2 - 3 * A.2) * (P.1 - 3 * A.1) == 0 &&
      (3 * D.1 - 3 * C.1) * (P.2 - 3 * C.2) - (3 * D.2 - 3 * C.2) * (P.1 - 3 * C.1) == 0) = true := by
  decide

end Trombo.Flower

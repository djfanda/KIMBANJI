/-
  알갱이 — 최소 1 · 최대 1 · 넓이 ½ · 부피 ⅓ · ⅙ · 겉넓이 6n² · 경계는 반 · 루트는 알갱이 비가 아니다 · 빛 일곱
  (린 4 v4.34.0 코어 · Mathlib 없음 · import 없음)

  알갱이 하나를 1 로 둔다. 길이는 알갱이 n 개, 넓이는 n², 부피는 n³ 이다.
  1. 넓이 — 계단 삼각형 T(n) = 1 + 2 + … + n. 2T(n) = n² + n : 정사각형의 반에 대각선 n 이 더 붙는다.
     계단 둘이 정사각형 : T(n) + T(n + 1) = (n + 1)². 비 T(n)/n² = (n + 1)/(2n) 은 ½ 보다 크고 1 이하이며,
     1 은 n = 1 에서만 — 최소 1 과 최대 1 이 같은 자리다.
  2. 부피 — 사각뿔 P(n) = 1² + … + n² 와 사면체 Te(n) = T(1) + … + T(n).
     6P(n) = 2n³ + 3n² + n (비 > ⅓) · 6Te(n) = n³ + 3n² + 2n (비 > ⅙).
     정육면체 = 사각뿔 셋 + 삼각형 셋 + 대각선 : (n + 1)³ = 3P(n) + 3T(n) + (n + 1).
     정육면체 = 사면체 여섯 + 삼각형 여섯 + 대각선 : (n + 2)³ = 6Te(n) + 6T(n + 1) + (n + 2).
     케플러 : 한 변이 2m 인 큐브의 면 위 사각뿔(꼭짓점은 가운데)의 알갱이 4P(m) 는 Te(2m) 과 같다.
  3. 겉넓이 — 알갱이 (n + 1)³ 개의 면 6(n + 1)³ 가운데 드러난 것 6(n + 1)², 맞붙어 숨은 것 6(n + 1)²n.
     껍질 : (m + 2)³ = m³ + 6m² + 12m + 8 (속 · 면 · 모서리 · 꼭짓점).
  4. 경계는 반 — 가장 작은 격자 삼각형의 넓이는 ½, 정사면체 꼴은 ⅙ (행렬식은 0 이 아닌 정수).
     픽 : 2(넓이) = 2(속 알갱이) + (경계 알갱이) − 2 — 꼭짓점이 0 … 3 인 모든 격자 삼각형에서.
     에르하르트 : 알갱이 수 = 부피 · n³ + (겉넓이의 반) · n² + … + 1, n ↦ −n 은 속과 겉을 바꾼다.
     리브 : 꼭짓점 넷 말고는 알갱이가 없는 사면체의 부피가 r/6 — 3 차원 부피는 한 번의 셈으로 정해지지 않는다.
  5. 루트 — a² = 2b² · a² = 3b² 은 자연수 해가 없다(무한 내림). 알갱이 비 x/y 는 √2 에 «1» 까지만 다가간다 :
     x² − 2y² = ±1 (펠). (x − y√2)(x + y√2) = ±1 — 유한 마이너스 × 유한 플러스. F₇ 에서는 3² = 2, F₃ 에는 √2 가 없고
     F₉ = F₃[i] 에서 i² = 2.
  6. 빛 일곱 — F₈ = F₂[x]/(x³ + x + 1) 에서 α = x 의 거듭제곱 α¹ … α⁷ 이 0 아닌 일곱 원소를 모두 돌고 α⁷ = 1.
     색 부호 R = 1 · G = 2 · Y = 3 · B = 4 · M = 5 · C = 6 · W = 7 로 읽으면 G → B → Y → C → W → M → R.
  7. 크라머(1750)의 악마의 곡선 y²(y² − a²) = x²(x² − b²) — 가운데 매듭에서 두 직선이 엇갈리고, x ↔ y · a ↔ b 가
     8 과 ∞ 를 바꾸며, a = b 에서 엑스(y = ±x)와 원(x² + y² = a²)으로 갈라진다. 크라머의 역설 : 점 n(n + 3)/2 대 n².
  8. 원 안의 육각형 — 변 = 반지름 · 둘레 = 지름 셋 · 넓이 3√3/2 (π 없음). 아르키메데스의 √3 의 테 1351/780 은
     펠 사다리의 여섯째(1351² − 3 · 780² = 1), 265/153 은 −2 사다리의 다섯째.
  9. 홀수의 합 1 + 3 + … + (2n − 1) = n² — 까닭 일곱 : 귀납 · 그노몬(ㄱ 자) · 두 삼각형 · 짝짓기 · 넓이 · 루트 ·
     홀수 줄을 가운데에서 접어 정사각형을 정확히 한 번씩 채우기(3 을 4 로). 무한히 커지는 삼각형을 n 으로 닫는다.

  확인 : decide · decide +kernel(유한 전수) · grind(환 등식) · omega(선형) · 귀납(모든 n)
  돌리기 : lean 알갱이.lean
-/

namespace Trombo.Grain

/-! ## 0. 알갱이 셈 -/

/-- 계단 삼각형의 알갱이 T(n) = 1 + 2 + … + n -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-- 계단 사각뿔의 알갱이 P(n) = 1² + 2² + … + n² -/
def pyr : Nat → Nat
  | 0 => 0
  | n + 1 => pyr n + (n + 1) * (n + 1)

/-- 계단 사면체의 알갱이 Te(n) = T(1) + … + T(n) -/
def tet : Nat → Nat
  | 0 => 0
  | n + 1 => tet n + tri (n + 1)

/-! ## 1. 넓이 — 계단 둘이 정사각형 -/

theorem tri_closed (n : Nat) : 2 * tri n = n * n + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tri]; grind

/-- 계단 둘이 정사각형 하나 : T(n) + T(n + 1) = (n + 1)² -/
theorem two_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) * (n + 1) := by
  have h1 := tri_closed n
  have h2 := tri_closed (n + 1)
  grind

/-- 정사각형 = 열린 삼각형 둘 + 대각선 -/
theorem square_split (n : Nat) : (n + 1) * (n + 1) = 2 * tri n + (n + 1) := by
  have := tri_closed n; grind

/-- 분자와 분모 : 2n · T(n) = n² (n + 1), 곧 T(n)/n² = (n + 1)/(2n) -/
theorem tri_ratio (n : Nat) : 2 * n * tri n = n * n * (n + 1) := by
  have := tri_closed n; grind

/-- 비는 ½ 보다 크다(n ≥ 1) -/
theorem tri_lower (n : Nat) (h : 1 ≤ n) : n * n < 2 * tri n := by
  have := tri_closed n; omega

/-- 비는 1 이하 -/
theorem tri_upper (n : Nat) : tri n ≤ n * n := by
  have := tri_closed n
  have : n ≤ n * n := Nat.le_mul_self n
  omega

/-- 비가 1 인 것은 알갱이 하나일 때뿐 — 최소 1 과 최대 1 -/
theorem tri_one_iff (n : Nat) (h : 1 ≤ n) : tri n = n * n ↔ n = 1 := by
  have h1 := tri_closed n
  constructor
  · intro e
    have : n * n = n := by omega
    rcases n with _ | _ | k
    · omega
    · rfl
    · exfalso
      have : (k + 2) * (k + 2) = (k + 2) * (k + 1) + (k + 2) := by grind
      grind
  · rintro rfl; rfl

/-- 넘침은 대각선 n — 경계의 알갱이 -/
theorem tri_excess (n : Nat) : 2 * tri n - n * n = n := by
  have := tri_closed n; omega

/-! ## 2. 부피 — 사각뿔 셋 · 사면체 여섯 -/

theorem pyr_closed (n : Nat) : 6 * pyr n = 2 * (n * n * n) + 3 * (n * n) + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pyr]; grind

theorem tet_closed (n : Nat) : 6 * tet n = n * n * n + 3 * (n * n) + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tet]
    have h := tri_closed (n + 1)
    grind

/-- 분자 꼴 : 6P(n) = n(n + 1)(2n + 1) · 6Te(n) = n(n + 1)(n + 2) -/
theorem pyr_tet_factored (n : Nat) :
    6 * pyr n = n * (n + 1) * (2 * n + 1) ∧ 6 * tet n = n * (n + 1) * (n + 2) := by
  have h1 := pyr_closed n
  have h2 := tet_closed n
  constructor <;> grind

/-- 사각뿔의 비는 ⅓ 보다 크다(n ≥ 1) -/
theorem pyr_lower (n : Nat) (h : 1 ≤ n) : n * n * n < 3 * pyr n := by
  have := pyr_closed n
  have : 1 ≤ n * n := Nat.mul_le_mul h h
  omega

/-- 사각뿔의 비는 1 이하 -/
theorem pyr_upper (n : Nat) : pyr n ≤ n * n * n := by
  have h := pyr_closed n
  have h1 : n ≤ n * n := Nat.le_mul_self n
  have h2 : n * n ≤ n * n * n := by
    rcases n with _ | k
    · simp
    · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
  omega

/-- 사면체의 비는 ⅙ 보다 크다(n ≥ 1) -/
theorem tet_lower (n : Nat) (h : 1 ≤ n) : n * n * n < 6 * tet n := by
  have := tet_closed n; omega

/-- 사면체의 비는 1 이하 -/
theorem tet_upper (n : Nat) : tet n ≤ n * n * n := by
  have h := tet_closed n
  have h1 : n ≤ n * n := Nat.le_mul_self n
  have h2 : n * n ≤ n * n * n := by
    rcases n with _ | k
    · simp
    · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
  omega

/-- 알갱이 하나에서는 모두 1 — 시작 1 -/
theorem one_grain : tri 1 = 1 ∧ pyr 1 = 1 ∧ tet 1 = 1 := ⟨rfl, rfl, rfl⟩

/-- 정육면체 = 사각뿔 셋(꼭짓점 하나에 모임) + 삼각형 셋(두 좌표가 같음) + 대각선 -/
theorem cube_three_pyramids (n : Nat) :
    (n + 1) * (n + 1) * (n + 1) = 3 * pyr n + 3 * tri n + (n + 1) := by
  have h1 := pyr_closed n
  have h2 := tri_closed n
  grind

/-- 정육면체 = 사면체 여섯(좌표의 순서) + 삼각형 여섯 + 대각선 -/
theorem cube_six_tetrahedra (n : Nat) :
    (n + 2) * (n + 2) * (n + 2) = 6 * tet n + 6 * tri (n + 1) + (n + 2) := by
  have h1 := tet_closed n
  have h2 := tri_closed (n + 1)
  grind

/-- 케플러 : 한 변 2m 인 큐브의 면 위 사각뿔(꼭짓점은 가운데)의 알갱이 = Te(2m) -/
theorem face_pyramid (m : Nat) : 4 * pyr m = tet (2 * m) := by
  have h1 := pyr_closed m
  have h2 := tet_closed (2 * m)
  have : 6 * (4 * pyr m) = 6 * tet (2 * m) := by grind
  omega

/-- 여섯 사각뿔 = 큐브 (2m)³ + 경계 넘침 3(2m)² + 2(2m) -/
theorem kepler_six (m : Nat) :
    6 * (4 * pyr m) = (2 * m) * (2 * m) * (2 * m) + 3 * ((2 * m) * (2 * m)) + 2 * (2 * m) := by
  rw [face_pyramid]; exact tet_closed (2 * m)

/-! ### 알갱이를 하나하나 세어 맞대기 -/

/-- n × n × n 큐브의 알갱이 (i, j, k) 가운데 p 를 만족하는 것의 수 -/
def countCube (n : Nat) (p : Nat → Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun a i => (List.range n).foldl (fun b j =>
    (List.range n).foldl (fun c k => if p i j k then c + 1 else c) b) a) 0

/-- z 가 혼자 가장 큼 = 사각뿔 P(n − 1) · 둘이 같이 가장 큼 = 삼각형 3T(n − 1) · 셋이 같음 = n (n = 1 … 7) -/
theorem max_split_counts :
    (List.range 7).all (fun m => let n := m + 1;
      countCube n (fun i j k => decide (i < k ∧ j < k)) == pyr (n - 1) &&
      countCube n (fun i j k => decide ((i = j ∧ k < i) ∨ (i = k ∧ j < i) ∨ (j = k ∧ i < j))) == 3 * tri (n - 1) &&
      countCube n (fun i j k => decide (i = j ∧ j = k)) == n) = true := by decide +kernel

/-- 좌표가 i < j < k 인 방 하나 = Te(n − 2) (n = 2 … 7) -/
theorem chamber_counts :
    (List.range 6).all (fun m => let n := m + 2;
      countCube n (fun i j k => decide (i < j ∧ j < k)) == tet (n - 2)) = true := by decide +kernel

/-! ## 3. 겉넓이 — 드러난 면과 숨은 면 · 껍질 -/

/-- 알갱이 (n + 1)³ 개의 면 6(n + 1)³ = 드러난 면 6(n + 1)² + 숨은 면(맞닿은 짝 3(n + 1)²n 마다 둘) -/
theorem exposed_faces (n : Nat) :
    6 * ((n + 1) * (n + 1)) + 2 * (3 * ((n + 1) * (n + 1)) * n) = 6 * ((n + 1) * (n + 1) * (n + 1)) := by
  grind

/-- 평면 : 알갱이 (n + 1)² 개의 변 4(n + 1)² = 둘레 4(n + 1) + 숨은 변(맞닿은 짝 2(n + 1)n 마다 둘) -/
theorem exposed_edges (n : Nat) :
    4 * (n + 1) + 2 * (2 * (n + 1) * n) = 4 * ((n + 1) * (n + 1)) := by grind

/-- 껍질 : (m + 2)³ = 속 m³ + 면 6m² + 모서리 12m + 꼭짓점 8 -/
theorem shell (m : Nat) :
    (m + 2) * (m + 2) * (m + 2) = m * m * m + 6 * (m * m) + 12 * m + 8 := by grind

/-- 큐브 알갱이를 경계 좌표의 수(0 · 1 · 2 · 3)로 갈라 세면 (n − 2)³ · 6(n − 2)² · 12(n − 2) · 8 (n = 2 … 7) -/
theorem shell_counts :
    (List.range 6).all (fun m => let n := m + 2;
      let e := fun (i : Nat) => if i = 0 ∨ i = n - 1 then 1 else 0;
      countCube n (fun i j k => e i + e j + e k == 0) == m * m * m &&
      countCube n (fun i j k => e i + e j + e k == 1) == 6 * (m * m) &&
      countCube n (fun i j k => e i + e j + e k == 2) == 12 * m &&
      countCube n (fun i j k => e i + e j + e k == 3) == 8) = true := by decide +kernel

/-! ## 4. 경계는 반 — 가장 작은 삼각형 · 픽 · 에르하르트 · 리브 -/

/-- 격자 삼각형의 넓이의 두 배는 정수 행렬식 — 0 이 아니면 크기 1 이상, 곧 넓이 ≥ ½ -/
theorem min_triangle (a b c d : Int) (h : a * d - b * c ≠ 0) :
    1 ≤ a * d - b * c ∨ a * d - b * c ≤ -1 := by omega

/-- 격자 사면체의 부피의 여섯 배도 정수 행렬식 — 0 이 아니면 크기 1 이상, 곧 부피 ≥ ⅙ -/
theorem min_tetrahedron (a b c d e f g h i : Int)
    (hd : a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g) ≠ 0) :
    1 ≤ a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g) ∨
    a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g) ≤ -1 := by omega

/-- 픽 — 한 변 n + 1 인 정사각형 : 2(넓이) = 2(속 n²) + (경계 4(n + 1)) − 2 -/
theorem pick_square (n : Nat) : 2 * ((n + 1) * (n + 1)) + 2 = 2 * (n * n) + 4 * (n + 1) := by grind

/-- 픽 — 두 변이 n 인 직각 삼각형 : 넓이 n²/2 · 경계 3n · 속 (n − 1)(n − 2)/2 -/
theorem pick_right_triangle (n : Int) : n * n = (n - 1) * (n - 2) + 3 * n - 2 := by grind

/-- 세 점이 이루는 방향(두 배 넓이의 부호) -/
def orient (p q r : Int × Int) : Int := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def box3 : List (Int × Int) :=
  (List.range 4).flatMap (fun (x : Nat) => (List.range 4).map (fun (y : Nat) => ((x : Int), (y : Int))))

def latticeOnEdge (p q : Int × Int) : Nat := Nat.gcd (q.1 - p.1).natAbs (q.2 - p.2).natAbs

def interiorCount (a b c : Int × Int) : Nat :=
  box3.countP (fun p =>
    let o1 := orient a b p; let o2 := orient b c p; let o3 := orient c a p
    (decide (0 < o1) && decide (0 < o2) && decide (0 < o3)) || (decide (o1 < 0) && decide (o2 < 0) && decide (o3 < 0)))

def pickOK (a b c : Int × Int) : Bool :=
  let A2 := (orient a b c).natAbs
  A2 == 0 || A2 + 2 == 2 * interiorCount a b c + (latticeOnEdge a b + latticeOnEdge b c + latticeOnEdge c a)

/-- 픽 : 꼭짓점이 {0, 1, 2, 3}² 인 모든 격자 삼각형(560 개)에서 2(넓이) = 2(속) + (경계) − 2 -/
theorem pick_all_small :
    (box3.all fun a => box3.all fun b => box3.all fun c => pickOK a b c) = true := by decide +kernel

/-- 에르하르트 — 표준 삼각형 nΔ 의 알갱이 (n + 1)(n + 2)/2 와 속 (n − 1)(n − 2)/2 (n = 0 … 8) -/
def triPts (n : Nat) : Nat := (List.range (n + 1)).foldl (fun a x => a + (List.range (n + 1)).countP (fun y => x + y ≤ n)) 0
def triInt (n : Nat) : Nat := (List.range (n + 1)).foldl (fun a x => a + (List.range (n + 1)).countP (fun y => 1 ≤ x && 1 ≤ y && x + y + 1 ≤ n)) 0

theorem ehrhart_triangle_counts :
    (List.range 9).all (fun n => 2 * triPts n == (n + 1) * (n + 2) && 2 * triInt n == (n - 1) * (n - 2)) = true := by
  decide +kernel

/-- 표준 사면체 nT 의 알갱이 (n + 1)(n + 2)(n + 3)/6 와 속 (n − 1)(n − 2)(n − 3)/6 (n = 0 … 7) -/
def tetPts (n : Nat) : Nat := countCube (n + 1) (fun x y z => decide (x + y + z ≤ n))
def tetInt (n : Nat) : Nat := countCube (n + 1) (fun x y z => decide (1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x + y + z + 1 ≤ n))

theorem ehrhart_tetrahedron_counts :
    (List.range 8).all (fun n => 6 * tetPts n == (n + 1) * (n + 2) * (n + 3) &&
      6 * tetInt n == (n - 1) * (n - 2) * (n - 3)) = true := by decide +kernel

/-- 다항식 읽기 : 2L(n) = n² + 3n + 2 (넓이 ½ · 둘레의 반 3/2 · 1) · 6L(n) = n³ + 6n² + 11n + 6 (부피 ⅙ · … · 1)
    · 큐브 (n + 1)³ = n³ + 3n² + 3n + 1 (부피 1 · 겉넓이의 반 3 · … · 1) -/
theorem ehrhart_polynomials (n : Int) :
    (n + 1) * (n + 2) = n * n + 3 * n + 2 ∧
    (n + 1) * (n + 2) * (n + 3) = n * n * n + 6 * (n * n) + 11 * n + 6 ∧
    (n + 1) * (n + 1) * (n + 1) = n * n * n + 3 * (n * n) + 3 * n + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- 맞거울 n ↦ −n 이 겉(닫힌)과 속(열린)을 바꾼다 : L(−n) = (−1)^d · (속의 알갱이) -/
theorem ehrhart_reciprocity (n : Int) :
    (-n + 1) * (-n + 2) = (n - 1) * (n - 2) ∧
    -((-n + 1) * (-n + 2) * (-n + 3)) = (n - 1) * (n - 2) * (n - 3) ∧
    -((-n + 1) * (-n + 1) * (-n + 1)) = (n - 1) * (n - 1) * (n - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- 리브의 사면체 (0,0,0) · (1,0,0) · (0,1,0) · (1,1,r) : 부피의 여섯 배는 r -/
theorem reeve_volume (r : Int) :
    1 * (1 * r - 0 * 1) - 0 * (0 * r - 0 * 1) + 0 * (0 * 1 - 1 * 1) = r := by grind

/-- 리브 사면체 안의 알갱이 : z ≥ 0 · z ≤ rx · z ≤ ry · rx + ry − z ≤ r -/
def reevePts (r : Nat) : Nat :=
  countCube (r + 1) (fun x y z => decide (x ≤ 1 ∧ y ≤ 1 ∧ z ≤ r * x ∧ z ≤ r * y ∧ r * x + r * y ≤ r + z))

/-- r = 1 … 8 에서 알갱이는 꼭짓점 넷뿐 — 부피 r/6 은 알갱이 수로 정해지지 않는다 -/
theorem reeve_four_points : (List.range 8).all (fun m => reevePts (m + 1) == 4) = true := by decide +kernel

/-! ## 5. 루트는 알갱이 비가 아니다 -/

/-- 제곱의 홀짝 : a 가 홀수면 a² 도 홀수 -/
theorem sq_mod_two (a : Nat) : (a * a) % 2 = (a % 2) := by
  have h := Nat.mod_two_eq_zero_or_one a
  rcases h with h | h
  · rw [Nat.mul_mod, h]
  · rw [Nat.mul_mod, h]

/-- a² = 2b² 은 b > 0 인 자연수 해가 없다 (무한 내림) — √2 는 알갱이의 비가 아니다 -/
theorem no_sqrt_two : ∀ (b a : Nat), 0 < b → a * a ≠ 2 * (b * b)
  | b, a, hb, h => by
    have ha : a % 2 = 0 := by
      have := sq_mod_two a
      omega
    obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
    have h2 : b * b = 2 * (c * c) := by
      have : 2 * c * (2 * c) = 4 * (c * c) := by grind
      omega
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0
        have hb0 : b * b = 0 := by simpa using h2
        have : 1 * 1 ≤ b * b := Nat.mul_le_mul hb hb
        omega
      · exact h0
    have hcb : c < b := by
      apply Nat.lt_of_not_le
      intro hle
      have h3 : b * b ≤ c * c := Nat.mul_le_mul hle hle
      have h4 : 1 * 1 ≤ c * c := Nat.mul_le_mul hc hc
      omega
    exact no_sqrt_two c b hc h2
termination_by b => b

/-- 제곱을 3 으로 나눈 나머지는 0 또는 1 -/
theorem sq_mod_three (a : Nat) : (a * a) % 3 = 0 ↔ a % 3 = 0 := by
  have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [Nat.mul_mod, h] <;> simp

/-- a² = 3b² 도 b > 0 인 자연수 해가 없다 — √3 도 알갱이의 비가 아니다 -/
theorem no_sqrt_three : ∀ (b a : Nat), 0 < b → a * a ≠ 3 * (b * b)
  | b, a, hb, h => by
    have ha : a % 3 = 0 := by
      have := (sq_mod_three a).mp (by omega)
      exact this
    obtain ⟨c, rfl⟩ : ∃ c, a = 3 * c := ⟨a / 3, by omega⟩
    have h2 : b * b = 3 * (c * c) := by
      have : 3 * c * (3 * c) = 9 * (c * c) := by grind
      omega
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0
        have hb0 : b * b = 0 := by simpa using h2
        have : 1 * 1 ≤ b * b := Nat.mul_le_mul hb hb
        omega
      · exact h0
    have hcb : c < b := by
      apply Nat.lt_of_not_le
      intro hle
      have h3 : b * b ≤ c * c := Nat.mul_le_mul hle hle
      have h4 : 1 * 1 ≤ c * c := Nat.mul_le_mul hc hc
      omega
    exact no_sqrt_three c b hc h2
termination_by b => b

/-- 한 변이 n 인 정사각형의 대각선은 알갱이 길이가 아니다 : m² = 2n² 인 m 은 없다(n ≥ 1) -/
theorem diagonal_not_grain (n m : Nat) (h : 1 ≤ n) : m * m ≠ 2 * (n * n) := no_sqrt_two n m h

/-- 경계는 1 : b ≠ 0 이면 a² − 2b² 은 0 이 아니라서 크기가 1 이상 -/
theorem defect_two (a b : Nat) (hb : 0 < b) :
    1 ≤ (a * a : Int) - 2 * (b * b) ∨ (a * a : Int) - 2 * (b * b) ≤ -1 := by
  have := no_sqrt_two b a hb
  omega

/-- 펠 사다리 (x, y) ↦ (x + 2y, x + y) : (1, 1) · (3, 2) · (7, 5) · (17, 12) · (41, 29) · (99, 70) · … -/
def pell2 : Nat → Int × Int
  | 0 => (1, 1)
  | k + 1 => let p := pell2 k; (p.1 + 2 * p.2, p.1 + p.2)

/-- 펠의 한 걸음은 x² − 2y² 의 부호를 바꾼다 -/
theorem pell2_step (k : Nat) :
    (pell2 (k + 1)).1 * (pell2 (k + 1)).1 - 2 * ((pell2 (k + 1)).2 * (pell2 (k + 1)).2) =
      -((pell2 k).1 * (pell2 k).1 - 2 * ((pell2 k).2 * (pell2 k).2)) := by
  simp only [pell2]; grind

/-- 펠 : x² − 2y² 은 −1 · +1 이 번갈아 — 알갱이 비는 √2 에 «1» 까지 다가간다(모든 단에서) -/
theorem pell2_norm (j : Nat) :
    (pell2 (2 * j)).1 * (pell2 (2 * j)).1 - 2 * ((pell2 (2 * j)).2 * (pell2 (2 * j)).2) = -1 ∧
    (pell2 (2 * j + 1)).1 * (pell2 (2 * j + 1)).1 - 2 * ((pell2 (2 * j + 1)).2 * (pell2 (2 * j + 1)).2) = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have s1 := pell2_step (2 * j + 1)
    have s2 := pell2_step (2 * j + 1 + 1)
    rw [e1]
    constructor
    · rw [s1, ih.2]
    · rw [s2, s1, ih.2]; omega

theorem pell2_first : (List.range 6).map pell2 = [(1, 1), (3, 2), (7, 5), (17, 12), (41, 29), (99, 70)] := by decide

/-- 유한 마이너스 × 유한 플러스 : (x − y√2)(x + y√2) = x² − 2y² (a + b√2 를 짝 (a, b) 로) -/
def mul2 (p q : Int × Int) : Int × Int := (p.1 * q.1 + 2 * p.2 * q.2, p.1 * q.2 + p.2 * q.1)
def norm2 (p : Int × Int) : Int := p.1 * p.1 - 2 * (p.2 * p.2)

theorem minus_times_plus (x y : Int) : mul2 (x, -y) (x, y) = (norm2 (x, y), 0) := by
  simp only [mul2, norm2]; grind

/-- (√2 − 1)(√2 + 1) = 1 · (2 − √3)(2 + √3) = 1 -/
theorem unit_root_two : mul2 (-1, 1) (1, 1) = (1, 0) := by decide

def mul3 (p q : Int × Int) : Int × Int := (p.1 * q.1 + 3 * p.2 * q.2, p.1 * q.2 + p.2 * q.1)
theorem unit_root_three : mul3 (2, -1) (2, 1) = (1, 0) := by decide

/-- 노름은 곱을 지킨다 : N(pq) = N(p) N(q) -/
theorem norm2_mul (p q : Int × Int) : norm2 (mul2 p q) = norm2 p * norm2 q := by
  simp only [mul2, norm2]; grind

/-- √3 의 펠 (x, y) ↦ (2x + 3y, x + 2y) : x² − 3y² = 1 이 모든 단에서 -/
def pell3 : Nat → Int × Int
  | 0 => (2, 1)
  | k + 1 => let p := pell3 k; (2 * p.1 + 3 * p.2, p.1 + 2 * p.2)

theorem pell3_norm (k : Nat) : (pell3 k).1 * (pell3 k).1 - 3 * ((pell3 k).2 * (pell3 k).2) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pell3]; grind

theorem pell3_first : (List.range 4).map pell3 = [(2, 1), (7, 4), (26, 15), (97, 56)] := by decide

/-- 유한체에서는 간첩이 아니다 : F₇ 에서 3² = 4² = 2 · F₃ 에는 √2 가 없다 -/
theorem sqrt_two_F7 : (3 * 3) % 7 = 2 ∧ (4 * 4) % 7 = 2 := by decide
theorem no_sqrt_two_F3 : (List.range 3).all (fun x => (x * x) % 3 != 2) = true := by decide

/-- F₉ = F₃[i] (i² = −1) 에서 i² = 2 — √2 = i -/
def mul9 (p q : Nat × Nat) : Nat × Nat := ((p.1 * q.1 + 2 * (p.2 * q.2)) % 3, (p.1 * q.2 + p.2 * q.1) % 3)
theorem sqrt_two_F9 : mul9 (0, 1) (0, 1) = (2, 0) := by decide

/-- 홀수 소수 p < 200 에서 √2 가 F_p 에 있을 조건은 p ≡ ±1 (mod 8) -/
def primesTo200 : List Nat :=
  (List.range 200).filter (fun p => 3 ≤ p && (List.range p).all (fun d => d < 2 || d * d > p || p % d != 0))

theorem sqrt_two_mod_eight :
    primesTo200.all (fun p => ((List.range p).any (fun x => (x * x) % p == 2)) == (p % 8 == 1 || p % 8 == 7)) = true := by
  decide +kernel

/-- 5 ≤ p < 200 에서 √3 이 F_p 에 있을 조건은 p ≡ ±1 (mod 12) -/
theorem sqrt_three_mod_twelve :
    (primesTo200.filter (5 ≤ ·)).all (fun p => ((List.range p).any (fun x => (x * x) % p == 3)) == (p % 12 == 1 || p % 12 == 11)) = true := by
  decide +kernel

/-! ## 6. 빛 일곱 — F₈ 에서 하나가 일곱을 돈다 -/

/-- F₂ 위 다항식 곱(자리올림 없는 곱) — 3 비트끼리 -/
def clmul (a b : Nat) : Nat :=
  (if b % 2 = 1 then a else 0) ^^^ (if (b / 2) % 2 = 1 then a * 2 else 0) ^^^ (if (b / 4) % 2 = 1 then a * 4 else 0)

/-- x³ + x + 1 (= 1011₂ = 11) 로 줄임 -/
def red8 (c : Nat) : Nat :=
  let c := if (c / 16) % 2 = 1 then c ^^^ 22 else c
  if (c / 8) % 2 = 1 then c ^^^ 11 else c

def mul8 (a b : Nat) : Nat := red8 (clmul a b)

def pow8 (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => mul8 (pow8 a k) a

/-- α = x (= 2 = G) 의 거듭제곱 α¹ … α⁷ = G · B · Y · C · W · M · R (2 · 4 · 3 · 6 · 7 · 5 · 1) -/
theorem light_cycle : (List.range 7).map (fun k => pow8 2 (k + 1)) = [2, 4, 3, 6, 7, 5, 1] := by decide

/-- 일곱 빛이 모두 나온다 — 0 아닌 원소 일곱이 하나의 빛의 거듭제곱 -/
theorem light_all_seven :
    (List.range 7).all (fun v => ((List.range 7).map (fun k => pow8 2 (k + 1))).contains (v + 1)) = true := by decide

/-- 시작 1 · 끝 1 : α⁰ = α⁷ = 1 이고 그 사이 α¹ … α⁶ 은 1 이 아니다 -/
theorem start_end_one : pow8 2 0 = 1 ∧ pow8 2 7 = 1 ∧ (List.range 6).all (fun k => pow8 2 (k + 1) != 1) = true := by
  decide

/-- 1 속의 단위 일곱 : 0 아닌 일곱 원소는 모두 역원이 있다(분모와 분자를 바꿀 수 있다) -/
theorem seven_units : (List.range 7).all (fun a => (List.range 7).any (fun b => mul8 (a + 1) (b + 1) == 1)) = true := by
  decide

/-- 제곱(프로베니우스)의 궤도 : {G, B, C} · {Y, M, W} · {R} — 1 + 3 + 3 = 7 -/
theorem frobenius_orbits :
    mul8 2 2 = 4 ∧ mul8 4 4 = 6 ∧ mul8 6 6 = 2 ∧ mul8 3 3 = 5 ∧ mul8 5 5 = 7 ∧ mul8 7 7 = 3 ∧ mul8 1 1 = 1 := by
  decide


/-! ## 7. 크라머(1750) — 악마의 곡선과 역설 -/

/-- 악마의 곡선 y²(y² − a²) = x²(x² − b²) 의 왼쪽 − 오른쪽 -/
def devil (a b x y : Int) : Int := y * y * (y * y - a * a) - x * x * (x * x - b * b)

/-- 축 위의 다섯 점 (0, 0) · (±b, 0) · (0, ±a) -/
theorem devil_axes (a b : Int) :
    devil a b 0 0 = 0 ∧ devil a b b 0 = 0 ∧ devil a b (-b) 0 = 0 ∧ devil a b 0 a = 0 ∧ devil a b 0 (-a) = 0 := by
  simp only [devil]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- 가운데 매듭(코어) : 2 차 부분 b²x² − a²y² = (bx − ay)(bx + ay) — 두 직선 y = ±(b/a)x 가 엇갈린다 -/
theorem devil_node (a b x y : Int) :
    devil a b x y = (b * x - a * y) * (b * x + a * y) + (y * y * (y * y) - x * x * (x * x)) := by
  simp only [devil]; grind

/-- 거울 : x ↦ −x · y ↦ −y 에서 그대로, x ↔ y 와 a ↔ b 를 함께 바꾸면 부호만 바뀐다(8 ↔ ∞) -/
theorem devil_mirror (a b x y : Int) :
    devil a b (-x) y = devil a b x y ∧ devil a b x (-y) = devil a b x y ∧ devil b a y x = -(devil a b x y) := by
  simp only [devil]; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- a = b 에서 갈라진다 : 악마의 곡선 = 엑스(y = x · y = −x) × 원(x² + y² = a²) -/
theorem devil_split (a x y : Int) : devil a a x y = (y - x) * (y + x) * (x * x + y * y - a * a) := by
  simp only [devil]; grind

/-- 크라머의 역설 — 차수 n 곡선을 정하는 점 n(n + 3)/2 은 단항식(삼각형 nΔ 의 알갱이) 수 − 1,
    두 곡선이 만나는 점은 n² (정사각형). 2n² − n(n + 3) = n(n − 3) : n = 3 에서만 같다(9 = 9) -/
theorem cramer_paradox (n : Int) : (n + 1) * (n + 2) - 2 = n * (n + 3) ∧ 2 * (n * n) - n * (n + 3) = n * (n - 3) := by
  constructor <;> grind

theorem cramer_small :
    (List.range 9).all (fun n => 2 * (triPts n - 1) == n * (n + 3)) = true ∧ 3 * 3 = 3 * (3 + 3) / 2 ∧ 4 * 4 = 4 * (4 + 3) / 2 + 2 := by
  refine ⟨by decide +kernel, by decide, by decide⟩


/-! ## 8. 원 안의 육각형 — 6 과 π · 아르키메데스의 √3 은 펠 -/

/-- 반지름 1 인 원 안의 정육각형 : 이웃한 두 꼭짓점 (1, 0) · (½, √3/2) 사이의 거리² = ¼ + ¾ = 1 — 변 = 반지름.
    네 배로 적으면 (2 − 1)² + 3 = 4 -/
theorem hexagon_side_is_radius : (2 - 1) * (2 - 1) + 3 = 2 * 2 := by decide

/-- 둘레 6r = 지름 셋 — 원의 둘레 2πr 보다 짧다(π > 3 · 전언) · 넓이 6 × (√3/4) = 3√3/2 (π 가 없다) -/
theorem hexagon_perimeter (r : Nat) : 6 * r = 3 * (2 * r) := by omega

/-- 육각형 = 마름모 셋(정삼각형 둘씩) = 정삼각형 여섯 — 정육면체를 대각선으로 본 그림자의 보이는 면 셋 -/
theorem hexagon_three_rhombi : 6 = 3 * 2 := by decide

/-- 바깥 육각형(원이 안에) 의 둘레는 4√3 r, 2√3 > 3 은 12 > 9 — 3 < π < 2√3 (아르키메데스의 출발 · 전언) -/
theorem archimedes_start : 3 * 3 < 3 * (2 * 2) := by decide

/-- 아르키메데스가 쓴 √3 의 두 테 1351/780 > √3 > 265/153 은 펠 사다리 위의 두 점 :
    1351² − 3 · 780² = 1 (pell3 의 여섯째) · 265² − 3 · 153² = −2 -/
theorem archimedes_sqrt3 :
    pell3 5 = (1351, 780) ∧ (1351 : Int) * 1351 - 3 * (780 * 780) = 1 ∧ (265 : Int) * 265 - 3 * (153 * 153) = -2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- −2 사다리 (1, 1) → (5, 3) → (19, 11) → (71, 41) → (265, 153) — 같은 걸음 (x, y) ↦ (2x + 3y, x + 2y) -/
def pell3m : Nat → Int × Int
  | 0 => (1, 1)
  | k + 1 => let p := pell3m k; (2 * p.1 + 3 * p.2, p.1 + 2 * p.2)

theorem pell3m_norm (k : Nat) : (pell3m k).1 * (pell3m k).1 - 3 * ((pell3m k).2 * (pell3m k).2) = -2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pell3m]; grind

theorem pell3m_fifth : pell3m 4 = (265, 153) := by decide


/-! ## 9. 홀수의 합은 n² — 무한히 커지는 삼각형을 정사각형으로 접어 n 으로 닫는다 -/

/-- 홀수 1 + 3 + 5 + … + (2n − 1) -/
def oddSum : Nat → Nat
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

/-- 까닭 ① 귀납 : n² + (2n + 1) = (n + 1)² — 모든 n 에서 닫힌다 -/
theorem odd_sum_square (n : Nat) : oddSum n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [oddSum]; grind

/-- 까닭 ② 그노몬(ㄱ 자 · 긴 알갱이) : (k + 1)² = k² + (2k + 1) — 정사각형에 홀수 줄 하나를 ㄱ 자로 두르면 다음 정사각형 -/
theorem gnomon (k : Nat) : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by grind

/-- 까닭 ③ 두 삼각형 : 2k + 1 = k + (k + 1) 이라 홀수의 합 = T(n) + T(n + 1) = (n + 1)² -/
theorem odd_sum_two_triangles (n : Nat) : oddSum (n + 1) = tri n + tri (n + 1) := by
  have h1 := odd_sum_square (n + 1)
  have h2 := two_triangles n
  omega

/-- 까닭 ④ 짝짓기(첫째 + 끝 = 2n) : 2 × (홀수의 합) = n × 2n -/
theorem odd_sum_pairing (n : Nat) : 2 * oddSum n = n * (2 * n) := by
  have := odd_sum_square n; grind

/-- 까닭 ⑤ 넓이 : 홀수 줄을 가운데 맞춰 쌓은 삼각형(밑변 2n · 높이 n)의 넓이 ½ · 2n · n = n² 와 알갱이 수가 같다 -/
theorem odd_triangle_area (n : Nat) : (2 * n * n) / 2 = oddSum n := by
  rw [odd_sum_square]
  have : 2 * n * n = 2 * (n * n) := by grind
  rw [this, Nat.mul_div_cancel_left _ (by decide)]

/-- 까닭 ⑥ 루트가 알갱이가 된다 : 홀수를 쌓으면 넓이가 n², 한 변(√ 넓이)이 자연수 n -/
theorem odd_sum_root (n : Nat) : ∃ m, m * m = oddSum n ∧ m = n := ⟨n, (odd_sum_square n).symm, rfl⟩

/-- 홀수 삼각형의 알갱이 : k 째 줄(k < n)에 2k + 1 개 -/
def oddTri (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun k => (List.range (2 * k + 1)).map (fun j => (k, j)))

/-- 3 을 4 로 : k 째 줄을 가운데 알갱이에서 접어 ㄱ 자로 — 왼쪽 반은 (k, j), 오른쪽 반은 (j − k − 1, k) -/
def fold (p : Nat × Nat) : Nat × Nat := if p.2 ≤ p.1 then (p.1, p.2) else (p.2 - p.1 - 1, p.1)

def squareGrains (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun a => (List.range n).map (fun b => (a, b)))

/-- 까닭 ⑦ 하나하나 접기 : n = 0 … 12 에서 접은 알갱이가 n × n 정사각형의 칸을 정확히 한 번씩 채운다 -/
theorem fold_fills_square :
    (List.range 13).all (fun n =>
      (oddTri n).length == n * n &&
      (squareGrains n).all (fun c => (oddTri n).countP (fun p => fold p == c) == 1)) = true := by
  decide +kernel

/-- 다이아몬드 : 정사각형을 45° 돌려 대각선 줄로 세면 1, 2, …, n, …, 2, 1 — 합은 T(n) + T(n − 1) = n² -/
theorem diamond (n : Nat) : tri n + tri (n + 1) = (n + 1) * (n + 1) := two_triangles n

end Trombo.Grain

#print axioms Trombo.Grain.tri_closed
#print axioms Trombo.Grain.tri_one_iff
#print axioms Trombo.Grain.cube_six_tetrahedra
#print axioms Trombo.Grain.max_split_counts
#print axioms Trombo.Grain.pick_all_small
#print axioms Trombo.Grain.reeve_four_points
#print axioms Trombo.Grain.no_sqrt_two
#print axioms Trombo.Grain.no_sqrt_three
#print axioms Trombo.Grain.pell2_norm
#print axioms Trombo.Grain.sqrt_two_mod_eight
#print axioms Trombo.Grain.light_cycle
#print axioms Trombo.Grain.devil_split
#print axioms Trombo.Grain.cramer_small
#print axioms Trombo.Grain.archimedes_sqrt3
#print axioms Trombo.Grain.pell3m_norm
#print axioms Trombo.Grain.odd_sum_square
#print axioms Trombo.Grain.fold_fills_square

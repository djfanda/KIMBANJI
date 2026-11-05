/-
바닥 모퉁이 — 접점 하나 · 세 점 미 · 비 · 애 · 세 바닥 · 직각 피라미드 · 좌우 회전 · 전기장 (린 4 코어 · 정수 좌표만)

모서리 2 인 정육면체 {±1}³ 를 지축 n = (1, 1, 1) 으로 세운다. 땅에 닿는 접점 g = (−1, −1, −1).
저자가 이름 붙인 세 점 : 미 = (1, −1, −1) · 비 = (−1, 1, −1) · 애 = (−1, −1, 1) (g 에서 모서리 하나씩 · 높이 −1 의 세모).

  1. 세 바닥 : g 에서 만나는 정육면체의 세 면은 평면 x = −1 · y = −1 · z = −1 — 법선이 서로 수직. 바닥은 하나가 아니라 셋.
  2. 직각 피라미드 : g 와 미 · 비 · 애 는 g 에서 세 모서리가 서로 수직인 사면체 (직삼면 모퉁이).
     데 구아의 정리 (3 차원 피타고라스) : 빗면 넓이² = 세 직각 면 넓이² 의 합 — 모든 정수 다리 a · b · c 에서 (커널 · 다항 항등식),
     여기서는 (2√3)² = 2² + 2² + 2² = 12.
  3. 부피 1 : 4 : 1 : 아래 모퉁이 피라미드 4/3 · 가운데 8 개 삼각형의 몸 (엇갈린 세모 기둥 · 찌그러진 정팔면체) 16/3 · 위 모퉁이 4/3.
     가운데 몸 : 꼭짓점 6 · 모서리 12 · 면 8 (정삼각형 둘 + 직각이등변 여섯) · 오일러 2.
  4. 좌우 회전 : 지축과 g 를 그대로 두는 좌표 바꾸기는 여섯 — 미 · 비 · 애 의 여섯 가지 줄 세우기를 모두 만든다.
     셋은 회전 (120° · 240° · 제자리 · 행렬식 +1), 셋은 거울 (행렬식 −1). 미 → 비 → 애 의 방향은 det = +8, 거꾸로는 −8 (오른손 · 왼손).
  5. 전기장 : 정육면체의 회전 24 가지는 여섯 면을 모두 서로 옮긴다 → 가운데 전하 q 의 선속은 면마다 q/6, 세 바닥에 q/2 (가우스 · 대칭 · 전언).
     접점 g 에 전하를 두면 g 에서 나온 장은 세 바닥 면 위에서 면과 나란하다 (면 위 모든 점 p 에서 (p − g)·법선 = 0) → 세 바닥의 선속 0.
     g 를 꼭짓점으로 나누어 가지는 정육면체는 여덟 (팔분공간) → 이 정육면체 전체로는 q/8, 먼 세 면에 q/24 씩 (전언 · 대칭).

저자의 읽기 (수학 주장 아님) : 바닥은 꽂혀 닿기만 하는 접지, 세 점 미 · 비 · 애 , 전기장과 좌우 회전. 이 파일은 좌표와 셈만 판정한다.
-/
namespace CubeFloor

abbrev V := Int × Int × Int
def dot (u v : V) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
def sub (u v : V) : V := (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)
def cross (u v : V) : V := (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)
def det3 (u v w : V) : Int := dot u (cross v w)

def n : V := (1, 1, 1)
def g : V := (-1, -1, -1)
def mi : V := (1, -1, -1)
def bi : V := (-1, 1, -1)
def ae : V := (-1, -1, 1)
def cube : List V := [(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)]

/-! ## 1. 세 바닥 -/

/-- g 에서 만나는 면 셋 (좌표 하나가 −1) 의 법선 (−1,0,0) · (0,−1,0) · (0,0,−1) 은 서로 수직, 면마다 꼭짓점 넷 · g 를 품음 -/
theorem three_floors :
    ([((-1 : Int), (0 : Int), (0 : Int)), (0, -1, 0), (0, 0, -1)] : List V).all (fun a =>
      ([((-1 : Int), (0 : Int), (0 : Int)), (0, -1, 0), (0, 0, -1)] : List V).all (fun b => a == b || dot a b == 0)) = true ∧
    (cube.filter (·.1 == -1)).length = 4 ∧ (cube.filter (·.2.1 == -1)).length = 4 ∧ (cube.filter (·.2.2 == -1)).length = 4 ∧
    (cube.filter (fun v => v.1 == -1 && v.2.1 == -1 && v.2.2 == -1)) = [g] := by decide

/-- 세 점 미 · 비 · 애 : 높이 −1 · g 와 모서리 하나 (거리² 4) · 서로는 거리² 8 (정삼각형) · 미 는 바닥 y · z 위, 비 는 x · z, 애 는 x · y -/
theorem three_points :
    [mi, bi, ae].map (dot n) = [-1, -1, -1] ∧ [mi, bi, ae].map (fun p => dot (sub p g) (sub p g)) = [4, 4, 4] ∧
    dot (sub mi bi) (sub mi bi) = 8 ∧ dot (sub bi ae) (sub bi ae) = 8 ∧ dot (sub ae mi) (sub ae mi) = 8 ∧
    (mi.2.1 == -1 && mi.2.2 == -1 && bi.1 == -1 && bi.2.2 == -1 && ae.1 == -1 && ae.2.1 == -1) = true := by decide

/-! ## 2. 직각 피라미드와 데 구아의 정리 -/

/-- g 에서 세 모서리가 서로 수직 -/
theorem right_corner :
    dot (sub mi g) (sub bi g) = 0 ∧ dot (sub bi g) (sub ae g) = 0 ∧ dot (sub ae g) (sub mi g) = 0 := by decide

/-- 데 구아 (모든 정수 다리 a · b · c) : 꼭짓점 (a,0,0) · (0,b,0) · (0,0,c) 의 빗면에서
    |(B − A) × (C − A)|² = (ab)² + (bc)² + (ca)²  — 곧 빗면 넓이² = 세 직각 면 넓이² 의 합 -/
theorem de_gua (a b c : Int) :
    let X := cross (sub (0, b, 0) (a, 0, 0)) (sub (0, 0, c) (a, 0, 0))
    dot X X = (a * b) * (a * b) + (b * c) * (b * c) + (c * a) * (c * a) := by
  simp only [cross, sub, dot]
  grind

/-- 미 · 비 · 애 빗면 : |×|² = 48 → 넓이² = 12 = 2² + 2² + 2² (넓이 2√3 · 직각 면 넓이 2 씩) -/
theorem de_gua_here :
    dot (cross (sub bi mi) (sub ae mi)) (cross (sub bi mi) (sub ae mi)) = 48 ∧ 48 = 4 * 12 ∧ 12 = 2 * 2 + 2 * 2 + 2 * 2 := by decide

/-! ## 3. 부피 1 : 4 : 1 과 가운데 몸 -/

/-- 모퉁이 피라미드 부피 = |det| / 6 = 8/6 = 4/3 · 위 모퉁이도 같음 · 가운데 = 8 − 8/3 = 16/3 (세 배 하면 4 : 16 : 4 = 1 : 4 : 1) -/
theorem volumes_141 :
    det3 (sub mi g) (sub bi g) (sub ae g) = 8 ∧
    det3 (sub (-1, 1, 1) (1, 1, 1)) (sub (1, -1, 1) (1, 1, 1)) (sub (1, 1, -1) (1, 1, 1)) = -8 ∧
    3 * 8 - 4 - 4 = (16 : Int) ∧ 4 + 16 + 4 = 3 * (8 : Int) ∧ (4 * 4 = 16) := by decide

def mid : List V := cube.filter (fun v => dot n v == 1 || dot n v == -1)

/-- 가운데 몸의 면 : 정육면체 면마다 극을 뺀 세 점 (직각이등변 · 변² 4, 4, 8) 여섯 + 위아래 정삼각형 (변² 8) 둘 = 여덟 -/
def faceTris : List (List V) :=
  [cube.filter (fun v => v.1 == 1 && v != (1, 1, 1)), cube.filter (fun v => v.2.1 == 1 && v != (1, 1, 1)),
   cube.filter (fun v => v.2.2 == 1 && v != (1, 1, 1)), cube.filter (fun v => v.1 == -1 && v != g),
   cube.filter (fun v => v.2.1 == -1 && v != g), cube.filter (fun v => v.2.2 == -1 && v != g)]
def sides2 (t : List V) : List Int :=
  match t with
  | [a, b, c] => [dot (sub a b) (sub a b), dot (sub b c) (sub b c), dot (sub c a) (sub c a)]
  | _ => []
def sorted3 : List Int → List Int
  | [a, b, c] =>
    let l := if a ≤ b then [a, b] else [b, a]
    match l with
    | [x, y] => if c ≤ x then [c, x, y] else if c ≤ y then [x, c, y] else [x, y, c]
    | _ => []
  | _ => []

theorem middle_body :
    mid.length = 6 ∧ faceTris.all (fun t => t.length == 3 && t.all (mid.contains ·)) = true ∧
    faceTris.all (fun t => sorted3 (sides2 t) == [4, 4, 8]) = true ∧
    sorted3 (sides2 [mi, bi, ae]) = [8, 8, 8] ∧
    sorted3 (sides2 [(1, 1, -1), (1, -1, 1), (-1, 1, 1)]) = [8, 8, 8] ∧
    (6 : Int) - 12 + (faceTris.length + 2) = 2 := by decide

/-! ## 4. 좌우 회전 -/

/-- 좌표 바꾸기 여섯 (σ, 부호 = 행렬식) -/
def perms : List ((V → V) × Int) :=
  [(fun v => v, 1), (fun v => (v.2.1, v.2.2, v.1), 1), (fun v => (v.2.2, v.1, v.2.1), 1),
   (fun v => (v.2.1, v.1, v.2.2), -1), (fun v => (v.1, v.2.2, v.2.1), -1), (fun v => (v.2.2, v.2.1, v.1), -1)]

/-- 여섯 모두 지축과 g 를 그대로 두고 미 · 비 · 애 를 서로 옮기며, 만드는 줄 세우기 여섯이 모두 다름 -/
theorem six_symmetries :
    perms.all (fun p => p.1 n == n && p.1 g == g) = true ∧
    perms.all (fun p => [mi, bi, ae].all (fun q => [mi, bi, ae].contains (p.1 q))) = true ∧
    (perms.map (fun p => [mi, bi, ae].map p.1)).length = 6 ∧
    ((perms.map (fun p => [mi, bi, ae].map p.1)).all fun a =>
      ((perms.map (fun p => [mi, bi, ae].map p.1)).filter (· == a)).length == 1) = true := by decide

/-- 회전 셋 (행렬식 +1) 은 방향 미 → 비 → 애 를 지키고 (det +8), 거울 셋 (행렬식 −1) 은 뒤집는다 (det −8) — 오른손 · 왼손 -/
theorem left_right :
    perms.all (fun p => det3 (sub (p.1 mi) g) (sub (p.1 bi) g) (sub (p.1 ae) g) == 8 * p.2) = true ∧
    det3 (sub mi g) (sub ae g) (sub bi g) = -8 ∧ (perms.filter (·.2 == 1)).length = 3 ∧ (perms.filter (·.2 == -1)).length = 3 := by decide

/-- 120° 회전 R : 미 → 비 → 애 → 미, 세 번이면 제자리 -/
def R (v : V) : V := (v.2.2, v.1, v.2.1)
theorem rotate_three :
    R mi = bi ∧ R bi = ae ∧ R ae = mi ∧ cube.all (fun v => R (R (R v)) == v) = true ∧ R n = n ∧ R g = g := by decide

/-! ## 5. 전기장 -/

/-- 부호 있는 좌표 바꾸기 48 가지 가운데 행렬식 +1 인 회전 24 가지 -/
def signed : List ((V → V) × Int) :=
  perms.flatMap fun p =>
    ([((1 : Int), (1 : Int), (1 : Int)), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)] : List V).map
      fun s => (fun v => let w := p.1 v; (s.1 * w.1, s.2.1 * w.2.1, s.2.2 * w.2.2), p.2 * s.1 * s.2.1 * s.2.2)
def rotations : List (V → V) := (signed.filter (·.2 == 1)).map (·.1)

def dedup (l : List V) : List V := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
def faceCenters : List V := [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- 회전 24 가지가 한 면 (1, 0, 0) 을 여섯 면 모두로 옮김 → 가운데 전하의 선속은 면마다 같다 (q/6 · 가우스와 대칭은 전언) -/
theorem faces_transitive :
    signed.length = 48 ∧ rotations.length = 24 ∧
    (dedup (rotations.map (· (1, 0, 0)))).length = 6 ∧ (rotations.map (· (1, 0, 0))).all (faceCenters.contains ·) = true ∧
    (rotations.all fun r => r (0, 0, 0) == (0, 0, 0)) = true := by decide

/-- 접점 g 의 전하 : 세 바닥 면 위의 어느 점 p 에서도 (p − g) 는 그 면과 나란함 (법선 성분 0) → 세 바닥의 선속 0 -/
theorem floor_field_tangent (y z : Int) :
    dot (sub (-1, y, z) g) (-1, 0, 0) = 0 ∧ dot (sub (y, -1, z) g) (0, -1, 0) = 0 ∧ dot (sub (y, z, -1) g) (0, 0, -1) = 0 := by
  simp only [sub, dot, g]
  omega

/-- g 를 꼭짓점으로 나누어 가지는 정육면체는 여덟 (g 둘레 팔분공간) — 가운데가 g ± (1, 1, 1) 꼴인 여덟 · 서로 다름 -/
theorem eight_octants :
    (dedup (([((1 : Int), (1 : Int), (1 : Int)), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)] : List V).map
      fun s => (g.1 + s.1, g.2.1 + s.2.1, g.2.2 + s.2.2))).length = 8 ∧
    (1 : Int) * 24 = 8 * 3 := by decide

end CubeFloor

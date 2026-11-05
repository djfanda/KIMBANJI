/-
지축 — 정육면체를 몸 대각선 (1, 1, 1) 으로 세우면 (린 4 코어 · 정수 좌표만)

정육면체 꼭짓점 {±1}³ = T⁺ ∪ T⁻ (TwoTetra 와 같은 두 정사면체). 지축 n = (1, 1, 1).
  · 높이 n·v : T⁺ 는 {3, −1, −1, −1}, T⁻ 는 {−3, 1, 1, 1} — 층이 1 · 3 · 3 · 1 로 위에서부터 + · − · + · − 번갈아 (와따가따)
  · 층 높이 3, 1, −1, −3 은 같은 간격 2 — 몸 대각선이 셋으로 똑같이 나뉨
  · 지축 위에 놓인 꼭짓점은 꼭 둘 : 꼭대기 (1, 1, 1) ∈ T⁺ 과 바닥 (−1, −1, −1) ∈ T⁻ — 바닥은 한 점이 아니라 ± 짝의 반쪽
  · 지축을 따라 내려다보면 (3v − (n·v) n 으로 사영) 여덟 꼭짓점이 일곱 자리 : 가운데 한 자리에 꼭대기와 바닥이 겹치고,
    둘레 여섯이 정육각형 (거리² 24 · 이웃끼리 60°) — 이웃한 둘은 언제나 서로 다른 정사면체
  · 길이² : 모서리 4 · 면 대각선 8 (= 정사면체 모서리 · √8 = 2√2 은 은비의 대각선) · 몸 대각선 12
  · 뚜껑과 바닥 : 꼭대기의 극 평면 위에 T⁻ 세 점, 바닥의 극 평면 위에 T⁺ 세 점 — 거리 √3 ↔ 1/√3 (분자와 분모가 바뀜)
  · 모래시계 증폭 : 안쪽 면 → 가운데 점 O → 바깥 면, 세 배로 커지고 뒤집힘 (배율 x² = 3) · 허리 L0 은 위아래 두 점이 합쳐진 정육각형
  · 각 : 지축과 모서리 cos² = 1/3 (54.74°) · 지축과 정사면체 모서리 cos² = 2/3 (35.26°) · 중심에서 두 꼭짓점 cos = −1/3 (109.47°)

저자의 읽기 (수학 주장 아님) : 은 (2 : 2 정사각) = 지축 = 정육면체, 그 안의 두 정사면체 사이 = 저자가 부르는 «리만 큐브».
위에서 보면 바닥이 꼭대기 뒤에 숨어 한 점처럼 보이지만, 실제로는 + 와 − 두 점이다. 이 파일은 좌표 사실만 판정한다.
-/
namespace CubeAxis

abbrev V := Int × Int × Int
def dot (u v : V) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
def sub (u v : V) : V := (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)
def cross (u v : V) : V := (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

def n : V := (1, 1, 1)
def Tp : List V := [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
def Tm : List V := Tp.map (fun v => (-v.1, -v.2.1, -v.2.2))
def cube : List V := Tp ++ Tm

/-- 높이 : T⁺ 와 T⁻ 의 층 -/
theorem heights : Tp.map (dot n) = [3, -1, -1, -1] ∧ Tm.map (dot n) = [-3, 1, 1, 1] := by decide

/-- 층 1 · 3 · 3 · 1 (위에서부터 + · − · + · −) · 간격 2 로 같음 -/
theorem layers :
    ([3, 1, -1, -3].map fun h => (cube.filter (fun v => dot n v == h)).length) = [1, 3, 3, 1] ∧
    (Tp.filter (fun v => dot n v == 3)).length = 1 ∧ (Tm.filter (fun v => dot n v == 1)).length = 3 ∧
    (Tp.filter (fun v => dot n v == -1)).length = 3 ∧ (Tm.filter (fun v => dot n v == -3)).length = 1 ∧
    (3 - 1 = 2 ∧ 1 - (-1) = 2 ∧ -1 - (-3) = (2 : Int)) := by decide

/-- 지축 위의 꼭짓점은 꼭 둘 : 꼭대기 (T⁺) 와 바닥 (T⁻) -/
theorem axis_two_points :
    cube.filter (fun v => cross n v == (0, 0, 0)) = [(1, 1, 1), (-1, -1, -1)] ∧
    Tp.contains (1, 1, 1) = true ∧ Tm.contains (-1, -1, -1) = true := by decide

/-- 지축을 따라 내려다본 자리 (3 배로 키운 정수 사영) -/
def proj (v : V) : V := (3 * v.1 - dot n v, 3 * v.2.1 - dot n v, 3 * v.2.2 - dot n v)

def dedup (l : List V) : List V := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- 여덟 꼭짓점이 일곱 자리 · 가운데 자리에 꼭대기와 바닥이 겹침 -/
theorem seven_spots :
    (dedup (cube.map proj)).length = 7 ∧ proj (1, 1, 1) = (0, 0, 0) ∧ proj (-1, -1, -1) = (0, 0, 0) ∧
    (cube.filter (fun v => proj v == (0, 0, 0))).length = 2 := by decide

def ring : List V := (dedup (cube.map proj)).filter (· != (0, 0, 0))

/-- 둘레 여섯은 정육각형 : 모두 거리² 24 · 서로의 내적은 12 (60°) · −12 (120°) · −24 (180°) 뿐, 60° 이웃은 각자 둘 -/
theorem hexagon :
    ring.length = 6 ∧ ring.all (fun p => dot p p == 24) = true ∧
    ring.all (fun p => ring.all (fun q => p == q || dot p q == 12 || dot p q == -12 || dot p q == -24)) = true ∧
    ring.all (fun p => (ring.filter (fun q => dot p q == 12)).length == 2) = true := by decide

/-- 60° 로 이웃한 둘은 언제나 서로 다른 정사면체 (위에서 보면 + · − 가 번갈아 돎) -/
theorem hexagon_alternates :
    (Tp.all fun u => Tp.all fun v => u == v || dot n u == 3 || dot n v == 3 || dot (proj u) (proj v) != 12) = true ∧
    (Tm.all fun u => Tm.all fun v => u == v || dot n u == -3 || dot n v == -3 || dot (proj u) (proj v) != 12) = true := by decide

/-- 길이² : 모서리 4 · 면 대각선 8 (정사면체 모서리) · 몸 대각선 12 -/
theorem lengths :
    dot (sub (1, 1, 1) (1, 1, -1)) (sub (1, 1, 1) (1, 1, -1)) = 4 ∧
    dot (sub (1, 1, 1) (1, -1, -1)) (sub (1, 1, 1) (1, -1, -1)) = 8 ∧
    dot (sub (1, 1, 1) (-1, -1, -1)) (sub (1, 1, 1) (-1, -1, -1)) = 12 := by decide

/-- 각 (제곱 꼴로 정수 확인) : 지축과 모서리 cos² = 1/3 · 지축과 정사면체 모서리 cos² = 2/3 · 중심에서 두 꼭짓점 cos = −1/3 -/
theorem angles :
    3 * (dot n (0, 0, 2)) ^ 2 = 1 * (dot n n * dot (0, 0, 2) (0, 0, 2)) ∧
    3 * (dot n (0, 2, 2)) ^ 2 = 2 * (dot n n * dot (0, 2, 2) (0, 2, 2)) ∧
    3 * dot (1, 1, 1) (1, -1, -1) = -1 * dot (1, 1, 1) (1, 1, 1) := by decide

/-- 뚜껑과 바닥 = 분자와 분모가 바뀜 : 꼭대기 (1, 1, 1) 의 극 평면 (단위 구에 대한 쌍대) n·v = 1 위에는
    T⁻ 의 세 꼭짓점이 정확히 놓이고, 바닥 (−1, −1, −1) 의 극 평면 n·v = −1 위에는 T⁺ 의 세 꼭짓점이 놓인다.
    거리로 재면 바깥 층 3/√3 = √3, 안쪽 층 1/√3 — 둘의 곱 3 · 1 / |n|² = 1 (뒤집기 x ↔ 1/x).
    그래서 네 층은 √3 · 1/√3 · −1/√3 · −√3 = x · 1/x · −1/x · −x. -/
theorem lid_floor_reciprocal :
    cube.filter (fun v => dot (1, 1, 1) v == 1) = Tm.filter (fun v => dot n v == 1) ∧
    (cube.filter (fun v => dot (1, 1, 1) v == 1)).length = 3 ∧
    cube.filter (fun v => dot (-1, -1, -1) v == 1) = Tp.filter (fun v => dot n v == -1) ∧
    (cube.filter (fun v => dot (-1, -1, -1) v == 1)).length = 3 ∧
    3 * 1 = dot n n := by decide

def scale (k : Int) (v : V) : V := (k * v.1, k * v.2.1, k * v.2.2)
def add (u v : V) : V := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)
def sameSet (a b : List V) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- 모래시계 증폭 : 안쪽 면 (높이 ±1) 의 세 점이 가운데 한 점 O 를 지나 (v ↦ −3v) 바깥 높이 ∓3 의 면으로 나가며
    세 배로 커지고 뒤집힌다 — 안쪽 T⁻ 면은 3·(T⁺ 아래 면) 으로, 안쪽 T⁺ 면은 3·(T⁻ 위 면) 으로.
    배율 3 = √3 ÷ (1/√3) = x ÷ (1/x) = x² (면 → 점 → 면) -/
theorem hourglass_amplify :
    sameSet ((Tm.filter (fun v => dot n v == 1)).map (scale (-3))) ((Tp.filter (fun v => dot n v == -1)).map (scale 3)) = true ∧
    ((Tm.filter (fun v => dot n v == 1)).map (scale (-3))).all (fun w => dot n w == -3) = true ∧
    sameSet ((Tp.filter (fun v => dot n v == -1)).map (scale (-3))) ((Tm.filter (fun v => dot n v == 1)).map (scale 3)) = true ∧
    ((Tp.filter (fun v => dot n v == -1)).map (scale (-3))).all (fun w => dot n w == 3) = true := by decide

/-- 높이 0 (L0) 의 허리 : 위 면 (T⁻ · 높이 1) 의 한 점과 아래 면 (T⁺ · 높이 −1) 의 한 점이 정육면체 모서리로 이어진 짝은 꼭 여섯,
    그 가운데 (두 배 좌표 u + v) 는 모두 높이 0 · 서로 다르며 (±2, ∓2, 0) 꼴 여섯 = 정육각형. 둘이 합쳐져 하나가 나옴 (입력 둘 → L0 출력). -/
def waist : List V :=
  (Tm.filter (fun v => dot n v == 1)).flatMap fun v =>
    ((Tp.filter (fun u => dot n u == -1)).filter (fun u => dot (sub u v) (sub u v) == 4)).map (add v)

theorem waist_hexagon :
    waist.length = 6 ∧ (dedup waist).length = 6 ∧ waist.all (fun w => dot n w == 0) = true ∧
    sameSet waist [(2, -2, 0), (-2, 2, 0), (2, 0, -2), (-2, 0, 2), (0, 2, -2), (0, -2, 2)] = true ∧
    waist.all (fun w => dot w w == 8) = true := by decide

/-- 두 점이 L0 으로 모였다가 위아래로 퍼짐 : 꼭대기 (+) 와 바닥 (−) 의 가운데는 O (높이 0 · L0).
    O 에서 위로 퍼진 면 = 꼭대기에서 나가는 정육면체 모서리 셋의 가운데 (두 배 좌표 (2, 2, 0) · (2, 0, 2) · (0, 2, 2), 높이 2),
    아래로 퍼진 면 = 그 반대 (높이 −2). 이 둘이 모래시계 (TwoTetra 의 Hp · Hm) 의 위 면 · 아래 면 —
    O 와 위 면이 정사면체 하나, O 와 아래 면이 정사면체 하나 (모서리² 2). 흐름 t · T⁺ (t = 1 → 0 → −1) 은 T⁺ 를 O 로 모았다가 T⁻ 로 펼친다. -/
def topEdgeMids : List V := (cube.filter (fun v => dot (sub (1, 1, 1) v) (sub (1, 1, 1) v) == 4)).map (add (1, 1, 1))
def botEdgeMids : List V := (cube.filter (fun v => dot (sub (-1, -1, -1) v) (sub (-1, -1, -1) v) == 4)).map (add (-1, -1, -1))

theorem poles_meet_and_spread :
    add (1, 1, 1) (-1, -1, -1) = (0, 0, 0) ∧
    sameSet topEdgeMids [(2, 2, 0), (2, 0, 2), (0, 2, 2)] = true ∧ topEdgeMids.all (fun w => dot n w == 4) = true ∧
    sameSet botEdgeMids [(-2, -2, 0), (-2, 0, -2), (0, -2, -2)] = true ∧ botEdgeMids.all (fun w => dot n w == -4) = true ∧
    ([(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)] : List V).all (fun u =>
      ([(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)] : List V).all (fun v => u == v || dot (sub u v) (sub u v) == 2)) = true ∧
    sameSet (Tp.map (scale (-1))) Tm = true ∧ (Tp.map (scale 0)).all (· == (0, 0, 0)) = true := by decide

/-- 정육면체의 모서리 (거리² 4 인 꼭짓점 짝) -/
def cubeEdges : List (V × V) :=
  cube.flatMap fun u => (cube.filter (fun v => dot (sub u v) (sub u v) == 4 && dot n u > dot n v)).map (fun v => (u, v))
/-- 정육면체의 면 : 좌표 하나가 ±1 로 고정된 네 점 -/
def cubeFaces : List (List V) :=
  [cube.filter (·.1 == 1), cube.filter (·.1 == -1), cube.filter (·.2.1 == 1), cube.filter (·.2.1 == -1),
   cube.filter (·.2.2 == 1), cube.filter (·.2.2 == -1)]

/-- 두 모퉁이가 모여 부피 : 위 모퉁이 (점 1 · 선 3 · 면 3) 와 아래 모퉁이 (점 1 · 선 3 · 면 3) 사이에
    가운데 띠 (점 6 · 선 6 — 모두 L0 을 가로지름) 를 더하면 정육면체 점 8 · 선 12 · 면 6 · 부피 1.
    8 · 12 · 6 · 1 은 (2 + t)³ 의 계수 (선분 하나 = 점 2 · 선 1 의 세제곱), 네모 하나는 (2 + t)² = 4 · 4 · 1.
    오일러 : 8 − 12 + 6 − 1 = 1 (공). 층 1 · 3 · 3 · 1 은 (1 + t)³ 의 계수. -/
theorem two_corners_make_cube :
    cubeEdges.length = 12 ∧
    (cubeEdges.filter (fun e => dot n e.1 == 3)).length = 3 ∧
    (cubeEdges.filter (fun e => dot n e.1 == 1 && dot n e.2 == -1)).length = 6 ∧
    (cubeEdges.filter (fun e => dot n e.2 == -3)).length = 3 ∧
    cubeFaces.all (fun f => f.length == 4) = true ∧
    (cubeFaces.filter (·.contains (1, 1, 1))).length = 3 ∧
    (cubeFaces.filter (·.contains (-1, -1, -1))).length = 3 ∧
    (cubeFaces.filter (fun f => f.contains (1, 1, 1) && f.contains (-1, -1, -1))).length = 0 ∧
    (8 : Int) - 12 + 6 - 1 = 1 ∧
    [2 ^ 3, 3 * 2 ^ 2, 3 * 2, 1] = [8, 12, 6, 1] ∧ [2 ^ 2, 2 * 2, 1] = [4, 4, 1] := by decide

/-- 작은 큐브 → O → 큰 큐브 (v ↦ −3v) : 점 · 선 · 면 · 부피의 수는 그대로 (8 · 12 · 6 · 1),
    크기는 길이 3 배 · 넓이 9 배 · 부피 27 배 = 3⁰ · 3¹ · 3² · 3³ (모서리² 4 → 36) -/
theorem small_to_big :
    (dedup (cube.map (scale (-3)))).length = 8 ∧
    sameSet (cube.map (scale (-3))) (cube.map (scale 3)) = true ∧
    dot (sub (scale 3 (1, 1, 1)) (scale 3 (1, 1, -1))) (sub (scale 3 (1, 1, 1)) (scale 3 (1, 1, -1))) = 9 * 4 ∧
    [3 ^ 0, 3 ^ 1, 3 ^ 2, 3 ^ 3] = [1, 3, 9, 27] := by decide

/-! ## 바닥의 넓이 — 지축에 수직인 단면 (모서리 2 인 정육면체 · 높이 h = n·v 는 −3 … 3)

단면 넓이 = (√3/2) · c(h) :
  · |h| ≤ 1 : 큰 세모 (꼭짓점에서 자란 것) 에서 모퉁이 세모 셋을 뺀 것 → c(h) = (h + 3)² − 3(h + 1)² = 6 − 2h² (정육각형)
  · 1 ≤ |h| ≤ 3 : 세모 → c(h) = (3 − |h|)²
그래서 꼭대기 · 바닥 (h = ±3) 은 넓이 0 (점), 안쪽 층 (h = ±1) 은 2√3 (세모), 허리 L0 (h = 0) 은 3√3 (정육각형 · 가장 넓음).
위에서 본 그림자 (바닥에 비친 정육면체) 는 4√3 — 아래 모퉁이의 세 면 (넓이 4 씩, 지축과 cos = 1/√3) 이 마름모 셋으로 그림자를 빈틈없이 덮고,
위 모퉁이의 세 면도 같은 그림자를 다른 마름모 셋으로 덮는다. 세모 : 허리 : 그림자 = 2√3 : 3√3 : 4√3 = 2 : 3 : 4. -/

/-- 단면 계수 c(h) (넓이 = (√3/2) · c) -/
def sec (h : Int) : Int := if h.natAbs ≤ 1 then 6 - 2 * h * h else (3 - (h.natAbs : Int)) * (3 - (h.natAbs : Int))

/-- 안쪽 공식 : 큰 세모 − 모퉁이 세모 셋 = 6 − 2h² (모든 정수 h) -/
theorem hexagon_formula (h : Int) : (h + 3) * (h + 3) - 3 * ((h + 1) * (h + 1)) = 6 - 2 * h * h := by grind

/-- 층마다 넓이 계수 : 바닥 0 · 세모 4 · 허리 6 · 세모 4 · 뚜껑 0 (넓이 0 · 2√3 · 3√3 · 2√3 · 0), 두 공식은 |h| = 1 에서 이어짐 -/
theorem floor_profile :
    [-3, -2, -1, 0, 1, 2, 3].map sec = [0, 1, 4, 6, 4, 1, 0] ∧ 6 - 2 * 1 * 1 = (3 - 1) * (3 - 1) := by decide

/-- 단면의 모양 : 높이 0 은 모서리 여섯을 자름 (정육각형), 높이 ±2 는 셋 (세모) -/
theorem floor_shapes :
    (cubeEdges.filter (fun e => dot n e.1 > 0 && dot n e.2 < 0)).length = 6 ∧
    (cubeEdges.filter (fun e => dot n e.1 > 2 && dot n e.2 < 2)).length = 3 ∧
    (cubeEdges.filter (fun e => dot n e.1 > -2 && dot n e.2 < -2)).length = 3 := by decide

/-- 단면을 쌓으면 부피 8 : ∫ c dh = (12 − 4/3) + 2 · 8/3 = 16, 부피 = (√3/2) · 16 · (1/√3) = 8 -/
theorem slices_volume :
    -- 세 배 한 정수로 : 3 · [6h − 2h³/3]₋₁¹ = 36 − 4 = 32 · 3 · [−(3 − h)³/3]₁³ = 8 · 32 + 2 · 8 = 48 = 3 · 16 · 16 / 2 = 8
    (18 * 1 - 2 * 1) - (18 * (-1) - 2 * (-1)) = (32 : Int) ∧ 0 - (-(3 - 1) ^ 3) = (8 : Int) ∧
    32 + 2 * 8 = 3 * (16 : Int) ∧ 16 = 2 * (8 : Int) := by decide

/-- 바닥은 닿기만 함 : 지축 방향으로 가장 낮은 높이 −3 에 놓인 것은 점 하나뿐 (단면 넓이 0) — 바닥 면이 아니라 접점 -/
theorem floor_touches :
    cube.filter (fun v => dot n v == -3) = [(-1, -1, -1)] ∧ sec (-3) = 0 ∧ sec 3 = 0 ∧
    (cube.all fun v => decide (-3 ≤ dot n v)) = true := by decide

/-- 그림자 4√3 : 아래 모퉁이 세 면 넓이 4 + 4 + 4 = 12, 지축과 cos = 1/√3 → 12/√3 = 4√3 = (√3/2) · 8 (12 · 2 = 8 · 3).
    세 면의 바깥 법선 (−1,0,0) · (0,−1,0) · (0,0,−1) 은 모두 지축과 같은 각 (n·법선 = −1). 위 모퉁이도 같음 (+1).
    세모 : 허리 : 그림자 계수 4 : 6 : 8 = 2 : 3 : 4 -/
theorem floor_shadow :
    ([((-1 : Int), (0 : Int), (0 : Int)), (0, -1, 0), (0, 0, -1)] : List V).all (fun m => dot n m == -1) = true ∧
    ([((1 : Int), (0 : Int), (0 : Int)), (0, 1, 0), (0, 0, 1)] : List V).all (fun m => dot n m == 1) = true ∧
    (12 * 2 = 8 * 3) ∧ [sec 1, sec 0, 8] = [4, 6, 8] ∧ (4 * 3 = 6 * 2 ∧ 6 * 4 = 8 * 3) := by decide

end CubeAxis

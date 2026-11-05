/-
뚜껑 — 홈과 돌기 : 정육면체 · 두 정사면체 · 케플러의 마름모 십이면체 · ½ 단면 · 황금 삼각형
린 4 커널 확인 (Mathlib 없이, 린 코어만 · 모든 좌표는 정수 · 필요하면 2 · 4 · 6 배)

읽기 «해석» — 임계 띠 0 ≤ Re s ≤ 1 를 홈과 돌기로 본다 : 홈 바닥 0 · 원래 면 ½ (리만 선 = «0 점») · 돌기 끝 1 (천장 «무한대»).
유한체 = 홈 (보이는 쪽) · 무한체 = 돌기 (안 보이는 쪽). ζ 의 극 ζ(1) = ∞ 와 대칭 s ↔ 1 − s 는 전언 (리만, 1859).
리만 가설은 미해결 □ 이고 이 파일은 그것을 다루지 않는다. 아래 ■ 는 정육면체 기하의 0 · ½ · 1 을 이 파일에서 커널이 확인한 것.

■ 1. 정육면체의 비트 : 꼭짓점 {0,1}³ = 비트 xyz. 무게 0 · 1 · 2 · 3 의 꼭짓점 1 · 3 · 3 · 1.
     T1 = 홀수 무게 {100, 010, 001, 111} · T2 = 짝수 무게 {000, 110, 101, 011}. 거울 v ↦ v xor 111 은 무게 w ↦ 3 − w · T1 ↔ T2.
     T2 = [3, 2] 짝수 검사 부호 (xor 에 닫힘) · T1 = T2 xor 100 · 같은 무리 두 점의 거리는 모두 2 (면 대각선 → 정사면체).
■ 2. 부피 — 6 × 부피 = |행렬식| · 2 배 좌표에서 24 × 부피 = (|행렬식| 의 합) / 2 :
     정육면체 24 (쿤 사면체 여섯) · 모서리 조각 4 (= 1/6) · T1 8 (= 1/3) · 정육면체 − T1 = 조각 넷 16 (= 2/3, 조각의 바닥 = T1 의 면 = 숨은 면) ·
     팔면체 T1 ∩ T2 = 중심 사면체 여덟 4 (= 1/6) · 별 끝 1 (= 1/24, 바닥 = 팔면체의 면) · T1 = 팔면체 + 끝 넷 (8 = 4 + 4) ·
     별 팔면체 = 8 + 8 − 4 = 팔면체 + 끝 여덟 = 12 (정육면체의 절반) · 두 사면체의 모서리 가운데점 = 정육면체 면의 중심 (면 ½).
     모든 유리점에서 T1 ∩ T2 = 중심 (½, ½, ½) 의 L1 공 (반지름 ½) · 점 대칭 p ↦ 1 − p 가 T1 과 T2 를 바꾼다 (omega).
■ 3. 케플러 (2 배 좌표 · 정육면체 [−1, 1]³) : 가운데를 꼭짓점으로 한 사각뿔 여섯 (홈) 각 4 = 24 / 6 · 바깥 사각뿔 (돌기) = 이웃 큐브의 홈 ·
     마름모 십이면체 = 정육면체 ∪ 바깥 사각뿔 여섯 = 48 (정육면체 × 2) · 꼭짓점 14 = 8 + 6 · 모서리 24 · 면 12 · 14 − 24 + 12 = 2 ·
     면 x + y = 2 위의 (1,1,1) · (1,1,−1) · (2,0,0) · (0,2,0) · 대각선 길이 제곱 8 : 4 = 2 : 1 · 축 위 0 (자기 중심) · ½ (면 중심) · 1 (이웃 중심).
■ 4. ½ 단면 (4 배 좌표 · x + y + z = 6) : 정육면체 → 육각형 · T1 → 삼각형 · T2 → 그 점 대칭 · 팔면체 → 안 육각형 (단면 증명서).
     (x, y) 사영 넓이 12 · 9/2 · 9/2 · 3 (아핀 사영은 넓이 비를 지킨다) → 삼각형 : 육각형 = 3 : 8 · 안 육각형 : 육각형 = 1 : 4 ·
     육망성 : 육각형 = 1 : 2. 중심과 육각형 변의 삼각형 여섯은 모두 넓이 2 (여섯 사각뿔의 단면).
■ 5. 대각선 층 : 층 x + y + z = k (k = 0 … 3) 의 꼭짓점 1 · 3 · 3 · 1 · 대각선을 0 · 1/3 (T1 의 면) · 1/2 (중심) · 2/3 (T2 의 면) · 1 로.
     단면 넓이 비 (별 팔면체 / 정육면체) : t = 1/6 → 1/4 · t = 1/3 → 1 (평면이 T1 의 면을 품는다) · t = 1/2 → 1/2.
△ 5'. 린 밖의 계산 (파이썬 · 정확 분수 · 커널 확인 아님) : t = 5/12 · 7/12 → 13/22 · t = 2/3 → 1 · t = 5/6 → 1/4.
     닫힌 꼴 : 0 < t < 1/3 과 2/3 < t < 1 에서 1/4 · 1/3 ≤ t ≤ 2/3 에서 (3t² − 3t + 1) / (−6t² + 6t − 1) — t = 1/3 에서 1/4 → 1 로 뛴다.
■ 6. 황금 삼각형 (꼭지각 108°) : Z[φ] = {a + bφ} (φ² = φ + 1) · φ (φ − 1) = 1 · 빗변 1 의 밑변² = 2 + (φ − 1) = φ² ·
     φⁿ⁺¹ = F(n) + F(n+1) φ · F(n+1)² − F(n+1) F(n) − F(n)² = (−1)ⁿ (n ≤ 30 은 계산 · 모든 n 은 귀납).
     2 cos 72° = φ − 1 은 전언. «해석» 오징어 놀이 판의 세모를 이 삼각형으로 읽는다.

검증 : lean 뚜껑.lean  (린 v4.34.0 · decide +kernel · omega · grind · 끝의 #print axioms 가 공리 목록) · 반대 시험 : 뚜껑_반대.lean
-/

namespace Trombo.Lid

/-! ## 0. 도구 — 비트 · 점 · 집합 · 부피 · 반공간 -/

def bit (v i : Nat) : Nat := v / 2 ^ i % 2
/-- 무게 = 켜진 비트 수 (세 자리) -/
def wt (v : Nat) : Nat := bit v 0 + bit v 1 + bit v 2

/-- 정수 좌표의 점 (x, y, z) -/
abbrev Pt := Int × Int × Int
/-- 비트 xyz ↦ n 배 좌표의 꼭짓점 (x = 100 의 자리 · y = 010 · z = 001) -/
def ptn (n v : Nat) : Pt := (((n * bit v 2 : Nat) : Int), ((n * bit v 1 : Nat) : Int), ((n * bit v 0 : Nat) : Int))
def addP (p q : Pt) : Pt := (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)
def subP (p q : Pt) : Pt := (p.1 - q.1, p.2.1 - q.2.1, p.2.2 - q.2.2)
def sumP (l : List Pt) : Pt := l.foldl addP (0, 0, 0)
/-- 거리의 제곱 -/
def dist2 (p q : Pt) : Int := let d := subP p q; d.1 * d.1 + d.2.1 * d.2.1 + d.2.2 * d.2.2
/-- 가운데점 (좌표 합이 짝수인 곳에만 쓴다) -/
def mid (p q : Pt) : Pt := ((p.1 + q.1) / 2, (p.2.1 + q.2.1) / 2, (p.2.2 + q.2.2) / 2)

def nodupB {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs
/-- 같은 집합 : 겹침 없음 · 같은 길이 · 한쪽이 다른 쪽 안에 -/
def sameSet {α : Type} [BEq α] (a b : List α) : Bool :=
  nodupB a && nodupB b && a.length == b.length && a.all (fun x => b.contains x)
/-- 서로 다른 두 원소의 짝 모두 -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

/-- 3 × 3 행렬식 (행 a, b, c) -/
def det3 (a b c : Pt) : Int :=
  a.1 * (b.2.1 * c.2.2 - b.2.2 * c.2.1) - a.2.1 * (b.1 * c.2.2 - b.2.2 * c.1) + a.2.2 * (b.1 * c.2.1 - b.2.1 * c.1)
/-- 사면체 [a, b, c, d] ↦ |행렬식| = 6 × 부피 -/
def sixVol : List Pt → Nat
  | [a, b, c, d] => (det3 (subP b a) (subP c a) (subP d a)).natAbs
  | _ => 0
def detSum (ts : List (List Pt)) : Nat := ts.foldl (fun s t => s + sixVol t) 0
/-- 2 배 좌표 (단위 정육면체의 한 변 = 2) : 6 × 부피가 2³ = 8 배이므로 48 × 부피 = 행렬식 합 · 24 × 부피 = 합 / 2 -/
def vol24 (ts : List (List Pt)) : Nat := detSum ts / 2
/-- 그 나눗셈이 정확하다 (합이 짝수) -/
def exact2 (ts : List (List Pt)) : Bool := detSum ts % 2 == 0

/-- 반공간 a x + b y + c z ≤ d 를 (a, b, c, d) 로 -/
abbrev HS := Int × Int × Int × Int
def hval (h : HS) (p : Pt) : Int := h.1 * p.1 + h.2.1 * p.2.1 + h.2.2.1 * p.2.2
def inside (H : List HS) (p : Pt) : Bool := H.all fun h => decide (hval h p ≤ h.2.2.2)
def tight (h : HS) (p : Pt) : Bool := hval h p == h.2.2.2
/-- n 배 좌표 : 정육면체 [0, n]³ · T1 · T2 의 면 · 팔면체 = T1 ∩ T2 -/
def cubeH (n : Int) : List HS := [(-1, 0, 0, 0), (1, 0, 0, n), (0, -1, 0, 0), (0, 1, 0, n), (0, 0, -1, 0), (0, 0, 1, n)]
def t1H (n : Int) : List HS := [(-1, -1, -1, -n), (1, 1, -1, n), (1, -1, 1, n), (-1, 1, 1, n)]
def t2H (n : Int) : List HS := [(1, 1, 1, 2 * n), (-1, -1, 1, 0), (-1, 1, -1, 0), (1, -1, -1, 0)]
def octH (n : Int) : List HS := t1H n ++ t2H n
/-- H 가 V 의 볼록 껍질의 면 : 꼭짓점이 모두 안 · 면마다 등호인 꼭짓점 m 개 · 꼭짓점마다 등호가 아닌 면 r 개 -/
def facetsOK (H : List HS) (V : List Pt) (m r : Nat) : Bool :=
  V.all (inside H) && H.all (fun h => V.countP (tight h) == m) && V.all (fun p => H.countP (fun h => !tight h p) == r)

/-! ## 1. 정육면체의 비트 — 두 정사면체 -/

def verts : List Nat := List.range 8
def T1 : List Nat := verts.filter (fun v => wt v % 2 == 1)
def T2 : List Nat := verts.filter (fun v => wt v % 2 == 0)

/-- 홈 바닥 000 에서 돌기 끝 111 까지 — 무게 0 · 1 · 2 · 3 의 꼭짓점이 1 · 3 · 3 · 1 -/
theorem cube_layers_1331 : (List.range 4).map (fun w => verts.countP (fun v => wt v == w)) = [1, 3, 3, 1] := by
  decide +kernel

/-- 서로의 거울인 두 무리 : 홀수 무게 T1 = {001, 010, 100, 111} 과 짝수 무게 T2 = {000, 011, 101, 110} 이 여덟을 넷 · 넷으로 가른다 -/
theorem two_tetrahedra_parity :
    T1 = [1, 2, 4, 7] ∧ T2 = [0, 3, 5, 6] ∧ verts.all (fun v => T1.contains v != T2.contains v) = true := by
  decide +kernel

/-- 거울 v ↦ v xor 111 : 무게 w ↦ 3 − w · T1 ↔ T2 · 두 번 비추면 제자리 -/
theorem complement_mirror :
    verts.all (fun v => wt (v ^^^ 7) == 3 - wt v && (v ^^^ 7) ^^^ 7 == v) = true ∧
    sameSet (T1.map (· ^^^ 7)) T2 = true ∧ sameSet (T2.map (· ^^^ 7)) T1 = true := by
  decide +kernel

/-- 홈 바닥 000 을 품은 T2 = [3, 2] 짝수 검사 부호 (xor 에 닫힘) · T1 = T2 xor 100 (닫히지 않음) · 같은 무리 두 점은 거리 2 = 면 대각선 → 정사면체 -/
theorem even_tetra_code :
    T2.all (fun a => T2.all fun b => T2.contains (a ^^^ b)) = true ∧ sameSet (T2.map (· ^^^ 4)) T1 = true ∧
    T1.contains (1 ^^^ 2) = false ∧
    [T1, T2].all (fun T => (pairs T).all fun (a, b) => wt (a ^^^ b) == 2) = true ∧
    [T1, T2].all (fun T => (pairs (T.map (ptn 2))).all fun (p, q) => dist2 p q == 8) = true := by
  decide +kernel

/-! ## 2. 부피 — 정육면체 · 모서리 조각 · 정사면체 · 팔면체 · 별 끝 (2 배 좌표 · 24 × 부피) -/

def tetT1 : List Pt := T1.map (ptn 2)
def tetT2 : List Pt := T2.map (ptn 2)
/-- 쿤 분할 : 000 → 비트 하나 → 비트 둘 → 111 의 길 여섯 = 대각선을 함께 쓰는 사면체 여섯 -/
def kuhn (p : Nat → Pt) : List (List Pt) :=
  ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] : List (Nat × Nat)).map fun (a, b) =>
    [p 0, p (2 ^ a), p (2 ^ a + 2 ^ b), p 7]
/-- 꼭짓점 v 의 모서리 조각 : v 와 그 이웃 셋 (비트 하나씩 뒤집기) -/
def corner (v : Nat) : List Pt := [ptn 2 v, ptn 2 (v ^^^ 4), ptn 2 (v ^^^ 2), ptn 2 (v ^^^ 1)]

/-- 모서리 돌기 : 정육면체 24 = T1 8 (1/3) + 모서리 조각 넷 (각 4 = 1/6 · 합 16 = 2/3) · 조각의 바닥 = T1 의 면 (숨은 면) -/
theorem cube_minus_tetra :
    vol24 (kuhn (ptn 2)) = 24 ∧ vol24 [tetT1] = 8 ∧ vol24 [tetT2] = 8 ∧
    T2.all (fun v => vol24 [corner v] == 4) = true ∧ vol24 (T2.map corner) = 16 ∧
    vol24 (kuhn (ptn 2)) = vol24 [tetT1] + vol24 (T2.map corner) ∧
    T2.all (fun v => sameSet [v ^^^ 4, v ^^^ 2, v ^^^ 1] (T1.filter (· != (v ^^^ 7)))) = true ∧
    [kuhn (ptn 2), [tetT1], [tetT2], T2.map corner].all exact2 = true := by
  decide +kernel

/-- 팔면체의 면 v : 정육면체 꼭짓점 v 쪽의 세 면 중심 (2 배 좌표 · 중심 (1, 1, 1)) -/
def octFace (v : Nat) : List Pt :=
  [(((2 * bit v 2 : Nat) : Int), 1, 1), (1, ((2 * bit v 1 : Nat) : Int), 1), (1, 1, ((2 * bit v 0 : Nat) : Int))]
def octa : List (List Pt) := verts.map fun v => (1, 1, 1) :: octFace v

/-- 면 ½ 여섯을 꼭짓점으로 한 팔면체 T1 ∩ T2 = 중심 사면체 여덟 (|행렬식| 각 1) → 4 (1/6) · 면 v 는 v 가 T1 이면 T2 의 면 위, T2 이면 T1 의 면 위 -/
theorem octahedron_eight_pieces :
    octa.all (fun t => sixVol t == 1) = true ∧ vol24 octa = 4 ∧ exact2 octa = true ∧
    facetsOK (t1H 2) tetT1 3 1 = true ∧ facetsOK (t2H 2) tetT2 3 1 = true ∧
    verts.all (fun v => (octFace v).all (inside (octH 2))) = true ∧
    verts.all (fun v => (if wt v % 2 == 1 then t2H 2 else t1H 2).any fun h => (octFace v).all (tight h)) = true := by
  decide +kernel

/-- 꼭짓점 v 의 별 끝 : v 와, v 가 속한 사면체의 다른 세 꼭짓점 (v xor 011 · 101 · 110) 과의 가운데점 -/
def tip (v : Nat) : List Pt := ptn 2 v :: [3, 5, 6].map fun m => mid (ptn 2 v) (ptn 2 (v ^^^ m))

/-- 돌기 : 별 끝 여덟 — 끝 = 정육면체의 꼭짓점 · 바닥 = 팔면체의 면 · 각 1 (1/24) · T1 = 팔면체 + 끝 넷 (8 = 4 + 4) · T2 도 같다 -/
theorem star_tips :
    verts.all (fun v => vol24 [tip v] == 1 && exact2 [tip v] && sameSet (tip v).tail (octFace v)) = true ∧
    vol24 (T1.map tip) = 4 ∧ vol24 [tetT1] = vol24 octa + vol24 (T1.map tip) ∧
    vol24 [tetT2] = vol24 octa + vol24 (T2.map tip) := by
  decide +kernel

/-- 거울 사면체 둘의 합집합 (별 팔면체) = T1 + T2 − 팔면체 = 팔면체 + 끝 여덟 = 12 = 정육면체 24 의 절반 -/
theorem star_octahedron_half :
    vol24 [tetT1] + vol24 [tetT2] - vol24 octa = 12 ∧ vol24 (octa ++ verts.map tip) = 12 ∧
    2 * vol24 (octa ++ verts.map tip) = vol24 (kuhn (ptn 2)) := by
  decide +kernel

def faceCenters : List Pt := [(0, 1, 1), (2, 1, 1), (1, 0, 1), (1, 2, 1), (1, 1, 0), (1, 1, 2)]

/-- 면 ½ : T1 의 모서리 가운데점 여섯 = T2 의 것 = 정육면체 면의 중심 (면의 네 꼭짓점 평균) = 팔면체의 꼭짓점 (면 넷이 만남) -/
theorem edge_midpoints_face_centers :
    sameSet ((pairs tetT1).map fun (p, q) => mid p q) faceCenters = true ∧
    sameSet ((pairs tetT2).map fun (p, q) => mid p q) faceCenters = true ∧
    faceCenters.all (fun c => (cubeH 2).any fun h =>
      sumP ((verts.map (ptn 2)).filter (tight h)) == (4 * c.1, 4 * c.2.1, 4 * c.2.2)) = true ∧
    faceCenters.all (fun c => verts.countP (fun v => (octFace v).contains c) == 4) = true := by
  decide +kernel

/-! ### 모든 유리점 — 분모 k 의 점 (x/k, y/k, z/k) -/

def inT1 (k x y z : Int) : Prop := k ≤ x + y + z ∧ x + y - z ≤ k ∧ x - y + z ≤ k ∧ -x + y + z ≤ k
def inT2 (k x y z : Int) : Prop := x + y + z ≤ 2 * k ∧ 0 ≤ x + y - z ∧ 0 ≤ x - y + z ∧ 0 ≤ -x + y + z

/-- 거울 · 면 ½ : 모든 유리점에서 T1 ∩ T2 = 중심 (½, ½, ½) 의 L1 공 (반지름 ½) · p ↦ 1 − p 가 T1 과 T2 를 바꾼다 · 부등식 = 면 목록 t1H · t2H -/
theorem octahedron_is_cap (k x y z : Int) :
    (inT1 k x y z ∧ inT2 k x y z ↔ (((2 * x - k).natAbs + (2 * y - k).natAbs + (2 * z - k).natAbs : Nat) : Int) ≤ k) ∧
    (inT1 k x y z ↔ inT2 k (k - x) (k - y) (k - z)) ∧
    (inside (t1H k) (x, y, z) = true ↔ inT1 k x y z) ∧ (inside (t2H k) (x, y, z) = true ↔ inT2 k x y z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [inT1, inT2]; omega
  · simp only [inT1, inT2]; omega
  · simp [inside, t1H, hval, inT1]; omega
  · simp [inside, t2H, hval, inT2]; omega

/-! ## 3. 케플러 — 홈 여섯과 돌기 여섯 (2 배 좌표 · 정육면체 [−1, 1]³) -/

/-- 축 i 에 a, 남은 두 축에 u, v -/
def place (i : Nat) (a u v : Int) : Pt := if i == 0 then (a, u, v) else if i == 1 then (u, a, v) else (u, v, a)
/-- 면 (축 i · 쪽 s) 의 네 꼭짓점 (도는 차례) -/
def sq (i : Nat) (s : Int) : List Pt := [place i s (-1) (-1), place i s 1 (-1), place i s 1 1, place i s (-1) 1]
/-- 사각뿔 = 바닥 정사각형을 대각선으로 나눈 사면체 둘 -/
def pyr (apex : Pt) (f : List Pt) : List (List Pt) :=
  [[apex, f.getD 0 (0, 0, 0), f.getD 1 (0, 0, 0), f.getD 2 (0, 0, 0)],
   [apex, f.getD 0 (0, 0, 0), f.getD 2 (0, 0, 0), f.getD 3 (0, 0, 0)]]
def dirs : List (Nat × Int) := [(0, 1), (0, -1), (1, 1), (1, -1), (2, 1), (2, -1)]
/-- 홈 : 가운데 (0, 0, 0) 을 꼭짓점으로 한 사각뿔 -/
def inner (d : Nat × Int) : List (List Pt) := pyr (0, 0, 0) (sq d.1 d.2)
/-- 돌기 : 이웃 큐브의 중심 (축 위 ±2) 을 꼭짓점으로 한 사각뿔 -/
def outer (d : Nat × Int) : List (List Pt) := pyr (place d.1 (2 * d.2) 0 0) (sq d.1 d.2)
def ptC (v : Nat) : Pt := addP (ptn 2 v) (-1, -1, -1)
def cubeC : List Pt := verts.map ptC
def apexes : List Pt := dirs.map fun d => place d.1 (2 * d.2) 0 0
def rdVerts : List Pt := cubeC ++ apexes
/-- 마름모 십이면체의 면 ±x ± y = 2 · ±y ± z = 2 · ±x ± z = 2 -/
def rdH : List HS :=
  [(1, 1, 0, 2), (1, -1, 0, 2), (-1, 1, 0, 2), (-1, -1, 0, 2), (0, 1, 1, 2), (0, 1, -1, 2), (0, -1, 1, 2), (0, -1, -1, 2),
   (1, 0, 1, 2), (1, 0, -1, 2), (-1, 0, 1, 2), (-1, 0, -1, 2)]

/-- 홈 : 정육면체 [−1, 1]³ = 24 · 가운데를 꼭짓점으로 한 사각뿔 여섯이 각 4 = 24 / 6 · 합이 정육면체 -/
theorem kepler_six_pyramids :
    vol24 (kuhn ptC) = 24 ∧ dirs.all (fun d => vol24 (inner d) == 4 && exact2 (inner d)) = true ∧
    vol24 (dirs.flatMap inner) = vol24 (kuhn ptC) := by
  decide +kernel

/-- 축 위 0 · ½ · 1 : 자기 중심 = 홈 바닥 · 면 ½ = 바닥 네 꼭짓점의 평균 = 중심과 돌기 끝의 가운데 · 돌기 끝 = 이웃 큐브 꼭짓점 여덟의 평균 -/
theorem center_face_neighbor :
    dirs.all (fun d =>
      sumP (sq d.1 d.2) == place d.1 (4 * d.2) 0 0 && mid (0, 0, 0) (place d.1 (2 * d.2) 0 0) == place d.1 d.2 0 0 &&
      sumP (cubeC.map (addP (place d.1 (2 * d.2) 0 0))) == place d.1 (16 * d.2) 0 0) = true := by
  decide +kernel

/-- 돌기 : 정육면체 + 바깥 사각뿔 여섯 = 48 = 정육면체 × 2 · 꼭짓점 14 = 8 + 6 (면 셋 · 넷이 만남) · 면마다 꼭짓점 넷 · 모서리 24 · 14 − 24 + 12 = 2 -/
theorem rhombic_dodecahedron :
    dirs.all (fun d => vol24 (outer d) == 4 && exact2 (outer d)) = true ∧
    vol24 (kuhn ptC ++ dirs.flatMap outer) = 48 ∧ vol24 (kuhn ptC ++ dirs.flatMap outer) = 2 * vol24 (kuhn ptC) ∧
    rdVerts.length = 14 ∧ nodupB rdVerts = true ∧ rdVerts.all (inside rdH) = true ∧
    cubeC.all (fun p => rdH.countP (fun h => tight h p) == 3) = true ∧
    apexes.all (fun p => rdH.countP (fun h => tight h p) == 4) = true ∧
    rdH.all (fun h => rdVerts.countP (tight h) == 4) = true ∧
    rdH.foldl (fun s h => s + rdVerts.countP (tight h)) 0 = 2 * 24 ∧ rdVerts.length + rdH.length = 24 + 2 := by
  decide +kernel

def isCube (p : Pt) : Bool := cubeC.contains p
/-- 마름모 : 꼭짓점 넷 = 정육면체 꼭짓점 둘 (짧은 대각선 = 정육면체 모서리, 길이 제곱 4) + 돌기 끝 둘 (긴 대각선, 8) · 네 변 길이 제곱 3 -/
def rhombusOK (l : List Pt) : Bool :=
  let c := l.filter isCube
  let a := l.filter (fun p => !isCube p)
  l.length == 4 && c.length == 2 && a.length == 2 &&
  dist2 (c.getD 0 (0, 0, 0)) (c.getD 1 (0, 0, 0)) == 4 && dist2 (a.getD 0 (0, 0, 0)) (a.getD 1 (0, 0, 0)) == 8 &&
  c.all (fun p => a.all fun q => dist2 p q == 3)

/-- 돌기의 면 : (1,1,1) · (1,1,−1) · (2,0,0) · (0,2,0) 이 x + y = 2 위 (이웃한 두 돌기의 삼각형이 한 마름모) · 대각선 길이 제곱 8 : 4 · 면 열둘 = 모서리 열둘 -/
theorem rhombus_face :
    sameSet (rdVerts.filter (tight (1, 1, 0, 2))) [(1, 1, 1), (1, 1, -1), (2, 0, 0), (0, 2, 0)] = true ∧
    dist2 (2, 0, 0) (0, 2, 0) = 8 ∧ dist2 (1, 1, 1) (1, 1, -1) = 4 ∧
    rdH.all (fun h => rhombusOK (rdVerts.filter (tight h))) = true ∧
    (pairs cubeC).countP (fun (p, q) => dist2 p q == 4) = 12 ∧
    nodupB (rdH.map fun h => (rdVerts.filter (tight h)).filter isCube) = true := by
  decide +kernel

/-! ### 모든 유리점 — 정육면체 [−k, k]³ -/

def inCubeC (k x y z : Int) : Prop := -k ≤ x ∧ x ≤ k ∧ -k ≤ y ∧ y ≤ k ∧ -k ≤ z ∧ z ≤ k
/-- 홈 (+x 쪽) : 꼭짓점 = 가운데 · 바닥 = 면 x = k -/
def innerX (k x y z : Int) : Prop := x ≤ k ∧ -x ≤ y ∧ y ≤ x ∧ -x ≤ z ∧ z ≤ x
/-- 돌기 (+x 쪽) : 꼭짓점 = 이웃 중심 (2k, 0, 0) · 바닥 = 면 x = k -/
def outerX (k x y z : Int) : Prop := k ≤ x ∧ x - 2 * k ≤ y ∧ y ≤ 2 * k - x ∧ x - 2 * k ≤ z ∧ z ≤ 2 * k - x
def sixInner (k x y z : Int) : Prop :=
  innerX k x y z ∨ innerX k (-x) y z ∨ innerX k y x z ∨ innerX k (-y) x z ∨ innerX k z x y ∨ innerX k (-z) x y
def sixOuter (k x y z : Int) : Prop :=
  outerX k x y z ∨ outerX k (-x) y z ∨ outerX k y x z ∨ outerX k (-y) x z ∨ outerX k z x y ∨ outerX k (-z) x y
/-- 마름모 십이면체 (면 rdH 의 k 배) -/
def inRD (k x y z : Int) : Prop :=
  x + y ≤ 2 * k ∧ x - y ≤ 2 * k ∧ -x + y ≤ 2 * k ∧ -x - y ≤ 2 * k ∧ y + z ≤ 2 * k ∧ y - z ≤ 2 * k ∧
  -y + z ≤ 2 * k ∧ -y - z ≤ 2 * k ∧ x + z ≤ 2 * k ∧ x - z ≤ 2 * k ∧ -x + z ≤ 2 * k ∧ -x - z ≤ 2 * k

/-- 모든 유리점 : 정육면체 = 홈 여섯의 합집합 · 돌기 = 이웃 큐브 (중심 (2k, 0, 0)) 의 홈을 뒤집어 붙인 것 · 마름모 십이면체 = 정육면체 ∪ 돌기 여섯 -/
theorem kepler_cover (k x y z : Int) :
    (inCubeC k x y z ↔ sixInner k x y z) ∧ (outerX k x y z ↔ innerX k (2 * k - x) y z) ∧
    (inRD k x y z ↔ inCubeC k x y z ∨ sixOuter k x y z) := by
  simp only [inCubeC, sixInner, innerX, outerX, sixOuter, inRD]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## 4. ½ 단면 — 4 배 좌표 · 평면 x + y + z = 6 (정육면체 [0, 4]³ 의 가운데 (2, 2, 2) 를 지남) -/

def onPlane (s : Int) (p : Pt) : Bool := p.1 + p.2.1 + p.2.2 == s
/-- 평면 x + y + z = s 에 평행하지 않은 면 -/
def slanted (h : HS) : Bool := !(h.1 == h.2.1 && h.2.1 == h.2.2.1)
/-- 다각형의 변 (돌아가며) -/
def edges (l : List Pt) : List (Pt × Pt) := l.zip (l.drop 1 ++ l.take 1)
/-- (x, y) 사영에서 변 p → q 에 대한 r 의 쪽 (외적) -/
def cross2 (p q r : Pt) : Int := (q.1 - p.1) * (r.2.1 - p.2.1) - (q.2.1 - p.2.1) * (r.1 - p.1)
/-- 신발끈 : (x, y) 사영 넓이의 2 배 (부호 = 도는 방향) -/
def shoe (l : List Pt) : Int := (edges l).foldl (fun s (p, q) => s + (p.1 * q.2.1 - q.1 * p.2.1)) 0
def area2 (l : List Pt) : Nat := (shoe l).natAbs
/-- 볼록한 차례 : 꼭짓점 셋 이상 · 변 위에 있지 않은 꼭짓점은 모두 변의 안쪽에 엄격히 -/
def convexOK (l : List Pt) : Bool :=
  let sg : Int := if shoe l > 0 then 1 else -1
  decide (3 ≤ l.length) && (edges l).all fun (p, q) => l.all fun r => r == p || r == q || decide (0 < sg * cross2 p q r)
/-- 단면 증명서 : 꼭짓점이 평면 위 · 입체 안 (→ 다각형 ⊆ 단면) · 볼록한 차례 · 변마다 평면에 평행하지 않은 입체의 면 하나가 두 끝에서 등호
    (→ 단면 ⊆ 변들의 안쪽 반평면의 교집합 = 다각형). 따라서 단면 = 다각형. -/
def sectionOK (H : List HS) (s : Int) (l : List Pt) : Bool :=
  l.all (onPlane s) && l.all (inside H) && convexOK l &&
  (edges l).all fun (p, q) => H.any fun h => slanted h && tight h p && tight h q
/-- 빈 단면 증명서 : 평면에 평행한 면 하나 (a = b = c) 가 평면 전체를 밖에 둔다 (a · s > d) -/
def emptyOK (H : List HS) (s : Int) : Bool := H.any fun h => !slanted h && decide (h.2.2.2 < h.1 * s)

def hexHalf : List Pt := [(4, 2, 0), (4, 0, 2), (2, 0, 4), (0, 2, 4), (0, 4, 2), (2, 4, 0)]
def triT1 : List Pt := [(4, 1, 1), (1, 4, 1), (1, 1, 4)]
def triT2 : List Pt := [(3, 3, 0), (3, 0, 3), (0, 3, 3)]
def hexIn : List Pt := [(3, 1, 2), (3, 2, 1), (2, 3, 1), (1, 3, 2), (1, 2, 3), (2, 1, 3)]
/-- 점 대칭 (중심 (2, 2, 2)) = 보수 v ↦ v xor 111 의 기하 -/
def pmirror (p : Pt) : Pt := (4 - p.1, 4 - p.2.1, 4 - p.2.2)

/-- 면 ½ : 정육면체 → 육각형 · T1 → 삼각형 · T2 → 그 거울 (점 대칭) · 팔면체 T1 ∩ T2 → 안 육각형 (면 목록과 단면 증명서) -/
theorem half_section_polygons :
    facetsOK (cubeH 4) (verts.map (ptn 4)) 4 3 = true ∧ facetsOK (t1H 4) (T1.map (ptn 4)) 3 1 = true ∧
    facetsOK (t2H 4) (T2.map (ptn 4)) 3 1 = true ∧
    sectionOK (cubeH 4) 6 hexHalf = true ∧ sectionOK (t1H 4) 6 triT1 = true ∧ sectionOK (t2H 4) 6 triT2 = true ∧
    sectionOK (octH 4) 6 hexIn = true ∧
    sameSet (triT1.map pmirror) triT2 = true ∧ sameSet (hexIn.map pmirror) hexIn = true ∧
    sameSet (hexHalf.map pmirror) hexHalf = true := by
  decide +kernel

/-- 면 ½ 의 넓이 (사영 × 2) : 육각형 24 · 삼각형 9 · 9 · 안 육각형 6 → 3 : 8 · 1 : 4 · 육망성 (9 + 9 − 6 = 12) : 24 = 1 : 2 -/
theorem half_section_areas :
    area2 hexHalf = 24 ∧ area2 triT1 = 9 ∧ area2 triT2 = 9 ∧ area2 hexIn = 6 ∧
    8 * area2 triT1 = 3 * area2 hexHalf ∧ 4 * area2 hexIn = area2 hexHalf ∧
    2 * (area2 triT1 + area2 triT2 - area2 hexIn) = area2 hexHalf := by
  decide +kernel

/-- 홈의 단면 : 중심 (2, 2, 2) 과 육각형 변의 삼각형 여섯이 모두 넓이 2 · 변마다 정육면체의 다른 면 위 — 여섯 사각뿔의 단면 -/
theorem six_pyramid_sections :
    (edges hexHalf).all (fun (p, q) => area2 [(2, 2, 2), p, q] == 4) = true ∧
    (edges hexHalf).foldl (fun s (p, q) => s + area2 [(2, 2, 2), p, q]) 0 = area2 hexHalf ∧
    (cubeH 4).all (fun h => (edges hexHalf).countP (fun (p, q) => tight h p && tight h q) == 1) = true := by
  decide +kernel

/-! ## 5. 대각선 층 — 0 · 1/3 · 1/2 · 2/3 · 1 -/

/-- 대각선 (6 배 좌표 (j, j, j) · t = j/6) : 층 꼭짓점 1 · 3 · 3 · 1 · T1 의 면 무게중심 (2,2,2) = 1/3 · 무게중심 (3,3,3) = 1/2 · T2 의 면 (4,4,4) = 2/3 · 거울이 두 면을 바꾼다 -/
theorem diagonal_layers :
    (List.range 4).map (fun k => (verts.map (ptn 1)).countP (onPlane (Int.ofNat k))) = [1, 3, 3, 1] ∧
    (T1.map (ptn 6)).countP (onPlane 6) = 3 ∧ (T2.map (ptn 6)).countP (onPlane 12) = 3 ∧
    sumP ((T1.map (ptn 6)).filter (onPlane 6)) = (6, 6, 6) ∧ sumP ((T2.map (ptn 6)).filter (onPlane 12)) = (12, 12, 12) ∧
    sumP (T1.map (ptn 6)) = (12, 12, 12) ∧ sumP (T2.map (ptn 6)) = (12, 12, 12) ∧
    sameSet (((T1.map (ptn 6)).filter (onPlane 6)).map (subP (6, 6, 6))) ((T2.map (ptn 6)).filter (onPlane 12)) = true := by
  decide +kernel

def cubeTri2 : List Pt := [(2, 0, 0), (0, 2, 0), (0, 0, 2)]
def t2Tri2 : List Pt := [(1, 1, 0), (1, 0, 1), (0, 1, 1)]
def cubeTri4 : List Pt := [(4, 0, 0), (0, 4, 0), (0, 0, 4)]
def t2Tri4 : List Pt := [(2, 2, 0), (2, 0, 2), (0, 2, 2)]

/-- 별 팔면체 단면의 넓이 = T1 단면 + T2 단면 − 팔면체 (T1 ∩ T2) 단면 -/
def starArea (a1 a2 ao : Nat) : Nat := a1 + a2 - ao

/-- 단면 넓이 비 (별 팔면체 / 정육면체) : t = 1/6 (합 2 · T1 과 팔면체는 빈 단면) → 1/4 · t = 1/3 (합 4 · T1 의 면) → 1 · 면 ½ (합 6) → 1/2 -/
theorem section_ratios :
    (sectionOK (cubeH 4) 2 cubeTri2 && emptyOK (t1H 4) 2 && sectionOK (t2H 4) 2 t2Tri2 && emptyOK (octH 4) 2) = true ∧
    area2 cubeTri2 = 4 ∧ area2 t2Tri2 = 1 ∧ 4 * starArea 0 (area2 t2Tri2) 0 = area2 cubeTri2 ∧
    (sectionOK (cubeH 4) 4 cubeTri4 && sectionOK (t1H 4) 4 cubeTri4 && sectionOK (t2H 4) 4 t2Tri4 &&
      sectionOK (octH 4) 4 t2Tri4) = true ∧
    area2 cubeTri4 = 16 ∧ area2 t2Tri4 = 4 ∧ starArea (area2 cubeTri4) (area2 t2Tri4) (area2 t2Tri4) = area2 cubeTri4 ∧
    2 * starArea (area2 triT1) (area2 triT2) (area2 hexIn) = area2 hexHalf := by
  decide +kernel

/-! ## 6. 황금 삼각형 — 꼭지각 108° · Z[φ] -/

/-- Z[φ] 의 수 a + bφ = 정수 짝 (a, b) · φ² = φ + 1 로 곱한다 -/
def gmul (p q : Int × Int) : Int × Int := (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)
def gadd (p q : Int × Int) : Int × Int := (p.1 + q.1, p.2 + q.2)
def phi : Int × Int := (0, 1)
def gpow : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => gmul (gpow n) phi
/-- 피보나치 짝 (F n, F (n + 1)) -/
def fibPair : Nat → Int × Int
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)
/-- 노름 꼴 F(n+1)² − F(n+1) F(n) − F(n)² -/
def cass (p : Int × Int) : Int := p.2 * p.2 - p.2 * p.1 - p.1 * p.1

/-- φ² = φ + 1 · 거울 φ ↦ 1 − φ 와의 곱이 −1 (φ (φ − 1) = 1 · φ 는 단위) · c = φ − 1 은 c² + c − 1 = 0 · 꼭지각 108° 빗변 1 의 밑변² = 2 + c = φ² -/
theorem golden_triangle :
    gmul phi phi = gadd phi (1, 0) ∧ gmul phi (-1, 1) = (1, 0) ∧
    gadd (gadd (gmul (-1, 1) (-1, 1)) (-1, 1)) (-1, 0) = (0, 0) ∧ gadd (2, 0) (-1, 1) = gmul phi phi := by
  decide +kernel

/-- φⁿ⁺¹ = F(n) + F(n+1) φ (n ≤ 30) · F(n+1)² − F(n+1) F(n) − F(n)² = (−1)ⁿ 로 걸음마다 거울 (n ≤ 30) · F(30) = 832040 -/
theorem fibonacci_unit_30 :
    (List.range 31).all (fun n => gpow (n + 1) == fibPair n) = true ∧
    (List.range 31).all (fun n => cass (fibPair n) == (if n % 2 == 0 then 1 else -1)) = true ∧
    fibPair 30 = (832040, 1346269) := by
  decide +kernel

/-- 모든 n : F(n+1)² − F(n+1) F(n) − F(n)² = (−1)ⁿ (귀납 · grind) — 한 걸음마다 부호가 거울에 비친다 -/
theorem cassini_all (n : Nat) : cass (fibPair n) = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [cass, fibPair] at *
    rw [Int.pow_succ]
    grind

end Trombo.Lid

#print axioms Trombo.Lid.cube_layers_1331
#print axioms Trombo.Lid.two_tetrahedra_parity
#print axioms Trombo.Lid.complement_mirror
#print axioms Trombo.Lid.even_tetra_code
#print axioms Trombo.Lid.cube_minus_tetra
#print axioms Trombo.Lid.octahedron_eight_pieces
#print axioms Trombo.Lid.star_tips
#print axioms Trombo.Lid.star_octahedron_half
#print axioms Trombo.Lid.edge_midpoints_face_centers
#print axioms Trombo.Lid.octahedron_is_cap
#print axioms Trombo.Lid.kepler_six_pyramids
#print axioms Trombo.Lid.center_face_neighbor
#print axioms Trombo.Lid.rhombic_dodecahedron
#print axioms Trombo.Lid.rhombus_face
#print axioms Trombo.Lid.kepler_cover
#print axioms Trombo.Lid.half_section_polygons
#print axioms Trombo.Lid.half_section_areas
#print axioms Trombo.Lid.six_pyramid_sections
#print axioms Trombo.Lid.diagonal_layers
#print axioms Trombo.Lid.section_ratios
#print axioms Trombo.Lid.golden_triangle
#print axioms Trombo.Lid.fibonacci_unit_30
#print axioms Trombo.Lid.cassini_all

/-
정20면체 · 정육면체 · 여섯 축 · 피터슨 — 공 열둘과 가운데 하나 (린 4 코어만 · Mathlib 없음)

좌표는 Z[φ] (a + bφ 를 (a, b) 로 · φ² = φ + 1) 로 정확하다. 꼭짓점 (0, ±1, ±φ) · (±1, ±φ, 0) · (±φ, 0, ±1).
· 꼭짓점 12 · 모서리 30 · 면 20 · 오일러 12 − 30 + 20 = 2 · 꼭짓점마다 이웃 다섯 · 모두 가운데에서 거리² 2 + φ.
· 가운데 공에 열두 공이 닿게 놓으면 이웃끼리는 닿지 않는다 : 5 · 모서리² = (12 − 4φ) · 반지름²
  — 비 (12 − 4φ)/5 ≈ 1.1056 = sec²18° > 1 (틈 · 공간을 채우지 못함).
· 정육면체 [−φ, φ]³ 의 여섯 면에 꼭짓점이 둘씩 앉고, 그 둘은 모서리 하나다 — 정육면체 여섯 면에 공 둘씩 = 정20면체.
· 돌림 셋 : 다섯 겹 R (2R 의 원소가 Z[φ] · (2R)ᵀ(2R) = 4I · 행렬식(2R) = 8) · 세 겹 (x, y, z) ↦ (y, z, x) · 두 겹 (x, y, z) ↦ (−x, −y, z).
  셋 다 꼭짓점을 꼭짓점으로 보내고, 셋이 만든 무리는 60 개 — 차수 1 · 2 · 3 · 5 가 1 · 15 · 20 · 24 개.
· 다섯 겹 축 여섯 (대척 꼭짓점 짝) 에 F₅ 위 사영직선의 이름 0 · 1 · 2 · 3 · 4 · ∞ 를 붙이면, 60 돌림이 여섯 축에 하는 일이
  정확히 PSL(2, 5) 의 뫼비우스 변환 x ↦ (ax + b)/(cx + d) (ad − bc = 1) 60 개와 같다.
  다섯 겹 R 은 x ↦ x/(x + 1) — 0 (0점) 을 두고 나머지 다섯 ∞ → 1 → 3 → 2 → 4 → ∞ 를 오각형으로 돌린다.
· 세 겹 축 열 (대척 면 짝) 가운데 모서리를 나누는 짝을 이으면 피터슨 그래프 = 크네저 K(5, 2) (꼭짓점 10 · 변 15 · 3-정칙 ·
  둘레 5 · 이웃 아닌 두 점의 공통 이웃 정확히 1). 다섯 겹 축마다 둘레의 세 겹 축 다섯이 5-순환을 이루고, 여섯 5-순환이
  변마다 정확히 두 번 지나간다 — 반정12면체의 오각형 면 여섯 (10 − 15 + 6 = 1).
· 원 셋 사이의 자리 (면) 스물 = 정육면체 꼭짓점 쪽 여덟 (팔분면마다 하나) + 면 쪽 열둘 (면마다 둘) · 다섯 겹 축마다 둘레 자리 다섯.
· 공 여섯 (±x · ±y · ±z) = 정팔면체 = 위 피라미드 + 아래 피라미드 · 면 여덟 = 팔분면 여덟 · 가족 (0, ±t, ±1) 은 t = 0 정팔면체 →
  t = φ − 1 정20면체 (t² + t − 1 = 0, 2cos 72° 와 같은 식) → t = 1 정육팔면체 (결정) · 꼭짓점의 삼각형 n 개 : 공 12/(6 − n).

검증 : lake build (decide +kernel)
-/
namespace Trombo.Icosa

/-! ## 1. Z[φ] 와 꼭짓점 -/

abbrev Z := Int × Int
def zadd (x y : Z) : Z := (x.1 + y.1, x.2 + y.2)
def zneg (x : Z) : Z := (-x.1, -x.2)
def zmul (x y : Z) : Z := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

abbrev P3 := Z × Z × Z
def vneg (u : P3) : P3 := (zneg u.1, zneg u.2.1, zneg u.2.2)
def vdbl (u : P3) : P3 := (zadd u.1 u.1, zadd u.2.1 u.2.1, zadd u.2.2 u.2.2)
def vsub (u v : P3) : P3 := (zadd u.1 (zneg v.1), zadd u.2.1 (zneg v.2.1), zadd u.2.2 (zneg v.2.2))
def dot (u v : P3) : Z := zadd (zadd (zmul u.1 v.1) (zmul u.2.1 v.2.1)) (zmul u.2.2 v.2.2)
def d2 (u v : P3) : Z := dot (vsub u v) (vsub u v)

/-- 0 (0,1,φ) · 1 (1,φ,0) · 2 (φ,0,1) · 3 (0,1,−φ) · 4 (1,−φ,0) · 5 (φ,0,−1) · 6 … 11 은 그 순서로 부호를 바꾼 것 -/
def verts : List P3 :=
  [((0, 0), (1, 0), (0, 1)), ((1, 0), (0, 1), (0, 0)), ((0, 1), (0, 0), (1, 0)),
   ((0, 0), (1, 0), (0, -1)), ((1, 0), (0, -1), (0, 0)), ((0, 1), (0, 0), (-1, 0)),
   ((0, 0), (-1, 0), (0, 1)), ((-1, 0), (0, 1), (0, 0)), ((0, -1), (0, 0), (1, 0)),
   ((0, 0), (-1, 0), (0, -1)), ((-1, 0), (0, -1), (0, 0)), ((0, -1), (0, 0), (-1, 0))]

def vt (i : Nat) : P3 := verts.getD i ((0, 0), (0, 0), (0, 0))
def adj (i j : Nat) : Bool := d2 (vt i) (vt j) == (4, 0)

def edgeList : List (Nat × Nat) :=
  (List.range 12).flatMap fun i => (List.range 12).filterMap fun j => if i < j ∧ adj i j = true then some (i, j) else none

def triangles : List (List Nat) :=
  (List.range 12).flatMap fun i => (List.range 12).flatMap fun j => (List.range 12).filterMap fun k =>
    if i < j ∧ j < k ∧ adj i j = true ∧ adj i k = true ∧ adj j k = true then some [i, j, k] else none

/-- ★ 꼭짓점 12 · 모서리 30 · 면 20 · 오일러 2 · 이웃 다섯 · 한 구 위 (거리² 2 + φ) -/
theorem counts :
    verts.length = 12 ∧ edgeList.length = 30 ∧ triangles.length = 20 ∧ (12 : Int) - 30 + 20 = 2 ∧
    (List.range 12).all (fun i => ((List.range 12).filter (adj i)).length == 5) = true ∧
    verts.all (fun v => dot v v == (2, 1)) = true := by
  decide +kernel

/-- 틈 : 5 · 모서리² = (12 − 4φ) · 반지름² (모서리² = 4 · 반지름² = 2 + φ) — 비 (12 − 4φ)/5 ≈ 1.1056 > 1 은 셈 (린에는 식만) -/
theorem gap : zmul (5, 0) (4, 0) = zmul (12, -4) (2, 1) ∧ ((4 : Int), (0 : Int)) ≠ (2, 1) := by decide

/-! ## 2. 정육면체의 여섯 면에 둘씩 -/

def coord (v : P3) (k : Nat) : Z := if k = 0 then v.1 else if k = 1 then v.2.1 else v.2.2

/-- 면 (k, s) : 좌표 k 가 s·φ (s = ±1) -/
def onFace (i k : Nat) (s : Int) : Bool := coord (vt i) k == (0, s)

def faceList : List (Nat × Int) := [(0, 1), (0, -1), (1, 1), (1, -1), (2, 1), (2, -1)]

/-- ★ 꼭짓점마다 정확히 한 면 위 · 면마다 꼭짓점 정확히 둘 · 그 둘은 이웃 (모서리 하나) -/
theorem on_cube :
    (List.range 12).all (fun i => (faceList.filter fun f => onFace i f.1 f.2).length == 1) = true ∧
    faceList.all (fun f => ((List.range 12).filter fun i => onFace i f.1 f.2).length == 2) = true ∧
    faceList.all (fun f => match (List.range 12).filter (fun i => onFace i f.1 f.2) with
      | [i, j] => adj i j
      | _ => false) = true := by
  decide +kernel

/-! ## 3. 돌림 셋과 60 -/

abbrev M3 := List (List Z)

def row (r : List Z) (v : P3) : Z :=
  zadd (zadd (zmul (r.getD 0 (0, 0)) v.1) (zmul (r.getD 1 (0, 0)) v.2.1)) (zmul (r.getD 2 (0, 0)) v.2.2)
def apply (M : M3) (v : P3) : P3 := (row (M.getD 0 []) v, row (M.getD 1 []) v, row (M.getD 2 []) v)

/-- 2R — 축 (0, 1, φ) 둘레 72° 돌림의 두 배 -/
def R5x2 : M3 := [[(-1, 1), (0, -1), (1, 0)], [(0, 1), (1, 0), (-1, 1)], [(-1, 0), (-1, 1), (0, 1)]]

def tcol (M : M3) (j : Nat) : P3 := ((M.getD 0 []).getD j (0, 0), (M.getD 1 []).getD j (0, 0), (M.getD 2 []).getD j (0, 0))

def det3 (M : M3) : Z :=
  let e := fun i j => (M.getD i []).getD j ((0 : Int), (0 : Int))
  zadd (zadd (zmul (e 0 0) (zadd (zmul (e 1 1) (e 2 2)) (zneg (zmul (e 1 2) (e 2 1)))))
             (zneg (zmul (e 0 1) (zadd (zmul (e 1 0) (e 2 2)) (zneg (zmul (e 1 2) (e 2 0)))))))
       (zmul (e 0 2) (zadd (zmul (e 1 0) (e 2 1)) (zneg (zmul (e 1 1) (e 2 0)))))

def r5 : List Nat := [0, 7, 1, 11, 5, 3, 2, 8, 6, 9, 4, 10]
def c3 : List Nat := [1, 2, 0, 4, 8, 6, 7, 5, 3, 10, 11, 9]
def f2 : List Nat := [6, 10, 8, 9, 7, 11, 0, 4, 2, 3, 1, 5]

/-- ★ 세 돌림이 꼭짓점을 꼭짓점으로 정확히 보낸다 · 2R 은 직교 (열끼리 내적 4δ) · 행렬식(2R) = 8 · 축 꼭짓점 0 은 그대로 -/
theorem rotations :
    (List.range 12).all (fun i => apply R5x2 (vt i) == vdbl (vt (r5.getD i 0))) = true ∧
    (List.range 12).all (fun i => vt (c3.getD i 0) == ((vt i).2.1, (vt i).2.2, (vt i).1)) = true ∧
    (List.range 12).all (fun i => vt (f2.getD i 0) == (zneg (vt i).1, zneg (vt i).2.1, (vt i).2.2)) = true ∧
    (List.range 3).all (fun i => (List.range 3).all fun j =>
      dot (tcol R5x2 i) (tcol R5x2 j) == (if i = j then (4, 0) else (0, 0))) = true ∧
    det3 R5x2 = (8, 0) ∧ r5.getD 0 99 = 0 := by
  decide +kernel

def comp (p q : List Nat) : List Nat := q.map fun i => p.getD i 0

def grow (gens S : List (List Nat)) : List (List Nat) :=
  S.foldl (fun acc g => gens.foldl (fun acc2 h =>
    let x := comp h g
    if acc2.contains x then acc2 else acc2 ++ [x]) acc) S

def iter (gens : List (List Nat)) : Nat → List (List Nat) → List (List Nat)
  | 0, S => S
  | k + 1, S => iter gens k (grow gens S)

def gens : List (List Nat) := [r5, c3, f2]

/-- 항등에서 시작해 생성원을 곱해 넓힌 무리 -/
def G : List (List Nat) := iter gens 5 [List.range 12]

def powP (p : List Nat) : Nat → List Nat
  | 0 => List.range p.length
  | k + 1 => comp p (powP p k)

def ordP (p : List Nat) : Nat := (((List.range 10).map (· + 1)).find? fun k => powP p k == List.range 12).getD 0

/-- ★ 60 개 · 생성원을 곱해도 더 늘지 않는다 (닫힘) · 차수 1 · 2 · 3 · 5 가 1 · 15 · 20 · 24 -/
theorem group_60 :
    G.length = 60 ∧ grow gens G = G ∧ G.eraseDups.length = 60 ∧
    (G.map ordP).count 1 = 1 ∧ (G.map ordP).count 2 = 15 ∧ (G.map ordP).count 3 = 20 ∧ (G.map ordP).count 5 = 24 ∧
    ordP r5 = 5 ∧ ordP c3 = 3 ∧ ordP f2 = 2 := by
  decide +kernel

/-! ## 4. 여섯 축 = F₅ 위 사영직선 -/

def anti : List Nat := [9, 10, 11, 6, 7, 8, 3, 4, 5, 0, 1, 2]
def axesL : List (Nat × Nat) := [(0, 9), (1, 10), (2, 11), (3, 6), (4, 7), (5, 8)]
def axisOf (i : Nat) : Nat := if i < 6 then i else [3, 4, 5, 0, 1, 2].getD (i - 6) 0

/-- 축 k 의 이름 (5 = ∞) : 축 0 (0, 1, φ) 이 0 — 0점 -/
def label : List Nat := [0, 1, 5, 4, 3, 2]
def unlabel : List Nat := [0, 1, 5, 4, 3, 2]

theorem axes_ok :
    (List.range 12).all (fun i => vt (anti.getD i 0) == vneg (vt i)) = true ∧
    axesL.all (fun p => anti.getD p.1 0 == p.2 && axisOf p.1 == axisOf p.2) = true ∧
    (List.range 6).all (fun x => label.getD (unlabel.getD x 0) 9 == x) = true := by
  decide +kernel

/-- 돌림 g 가 이름 붙인 여섯 축에 하는 일 -/
def onP1 (g : List Nat) : List Nat :=
  (List.range 6).map fun x => label.getD (axisOf (g.getD (axesL.getD (unlabel.getD x 0) (0, 0)).1 0)) 0

def inv5 (x : Nat) : Nat := [0, 1, 3, 2, 4].getD x 0

/-- 뫼비우스 x ↦ (ax + b)/(cx + d) 를 F₅ ∪ {∞} 위에서 (∞ = 5) -/
def mob (a b c d x : Nat) : Nat :=
  if x = 5 then (if c % 5 = 0 then 5 else (a * inv5 (c % 5)) % 5)
  else if (c * x + d) % 5 = 0 then 5 else ((a * x + b) % 5 * inv5 ((c * x + d) % 5)) % 5

def psl : List (List Nat) :=
  ((List.range 625).filterMap fun n =>
    let a := n % 5
    let b := n / 5 % 5
    let c := n / 25 % 5
    let d := n / 125 % 5
    if (a * d + 4 * (b * c)) % 5 = 1 then some ((List.range 6).map (mob a b c d)) else none).eraseDups

/-- ★ 60 돌림이 여섯 축에 하는 일 = PSL(2, 5) 의 뫼비우스 60 · 다섯 겹 R = x ↦ x/(x + 1) (0 을 두고 ∞ → 1 → 3 → 2 → 4 → ∞) -/
theorem six_axes_are_P1F5 :
    psl.length = 60 ∧ (G.map onP1).eraseDups.length = 60 ∧
    (G.map onP1).all (fun g => psl.contains g) = true ∧ psl.all (fun g => (G.map onP1).contains g) = true ∧
    onP1 r5 = (List.range 6).map (mob 1 0 1 1) ∧ onP1 r5 = [0, 3, 4, 2, 5, 1] := by
  decide +kernel

/-! ## 5. 세 겹 축 열 = 피터슨 그래프 · 반정12면체 -/

def faces : List (List Nat) :=
  [[0, 1, 2], [0, 1, 7], [0, 2, 6], [0, 6, 8], [0, 7, 8], [1, 2, 5], [1, 3, 5], [1, 3, 7], [2, 4, 5], [2, 4, 6],
   [3, 5, 9], [3, 7, 11], [3, 9, 11], [4, 5, 9], [4, 6, 10], [4, 9, 10], [6, 8, 10], [7, 8, 11], [8, 10, 11], [9, 10, 11]]

def fpairs : List (Nat × Nat) := [(0, 19), (1, 15), (2, 12), (3, 10), (4, 13), (5, 18), (6, 16), (7, 14), (8, 17), (9, 11)]

def sort3 (l : List Nat) : List Nat := match l with
  | [a, b, c] =>
    let x := min a (min b c)
    let z := max a (max b c)
    [x, a + b + c - x - z, z]
  | _ => l

def fc (i : Nat) : List Nat := faces.getD i []

def shareEdge (f g : List Nat) : Bool := (f.filter fun x => g.contains x).length == 2

def adjAx (i j : Nat) : Bool :=
  let p := fpairs.getD i (0, 0)
  let q := fpairs.getD j (0, 0)
  i != j && (shareEdge (fc p.1) (fc q.1) || shareEdge (fc p.1) (fc q.2))

def k52 : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def kadj (i j : Nat) : Bool :=
  let p := k52.getD i (0, 0)
  let q := k52.getD j (0, 0)
  p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2

def iso : List Nat := [0, 7, 8, 2, 6, 9, 4, 3, 1, 5]

def common (i j : Nat) : Nat := ((List.range 10).filter fun k => kadj i k && kadj j k).length

/-- 다섯 겹 축 k 둘레의 세 겹 축 (그 꼭짓점을 품은 면의 짝) -/
def around (k : Nat) : List Nat :=
  (List.range 10).filter fun i =>
    let p := fpairs.getD i (0, 0)
    (fc p.1).contains (axesL.getD k (0, 0)).1 || (fc p.2).contains (axesL.getD k (0, 0)).1

/-- ★ 피터슨 : 면 20 이 바로 그 삼각형들 · 대척 면 짝 열 · 모서리를 나누는 짝의 그래프 ≅ K(5, 2) -/
theorem petersen :
    faces = triangles ∧
    fpairs.all (fun p => sort3 ((fc p.1).map fun i => anti.getD i 0) == fc p.2) = true ∧
    iso.eraseDups.length = 10 ∧ iso.all (· < 10) = true ∧
    (List.range 10).all (fun i => (List.range 10).all fun j => adjAx i j == kadj (iso.getD i 0) (iso.getD j 0)) = true := by
  decide +kernel

/-- K(5, 2) : 변 15 · 3-정칙 · 이웃끼리 공통 이웃 0 (삼각형 없음) · 이웃 아닌 두 점의 공통 이웃 정확히 1 (사각형 없음 · 둘레 5) -/
theorem kneser :
    ((List.range 10).flatMap fun i => (List.range 10).filter fun j => i < j && kadj i j).length = 15 ∧
    (List.range 10).all (fun i => ((List.range 10).filter (kadj i)).length == 3) = true ∧
    (List.range 10).all (fun i => (List.range 10).all fun j =>
      i == j || (if kadj i j then common i j == 0 else common i j == 1)) = true := by
  decide +kernel

/-- ★ 반정12면체 : 다섯 겹 축마다 둘레 세 겹 축 다섯이 5-순환 · 여섯 순환이 변마다 정확히 두 번 · 10 − 15 + 6 = 1 -/
theorem hemi_dodecahedron :
    (List.range 6).all (fun k => (around k).length == 5 &&
      (around k).all fun i => ((around k).filter (adjAx i)).length == 2) = true ∧
    (List.range 10).all (fun i => (List.range 10).all fun j =>
      !(i < j && adjAx i j) || ((List.range 6).filter fun k => (around k).contains i && (around k).contains j).length == 2) = true ∧
    around 0 = [0, 1, 2, 3, 4] ∧ (10 : Int) - 15 + 6 = 1 := by
  decide +kernel

/-! ## 6. 세 겹 자리 스물 = 꼭짓점 쪽 여덟 + 면 쪽 열둘 -/

/-- 꼭짓점이 앉은 정육면체 면의 축 (φ 가 있는 좌표) 과 그 부호 -/
def faceAxis (i : Nat) : Nat := if (vt i).1.2 != 0 then 0 else if (vt i).2.1.2 != 0 then 1 else 2
def faceSign (i : Nat) : Int := (coord (vt i) (faceAxis i)).2

/-- 팔분면 면 : 세 꼭짓점이 서로 다른 세 축의 면 위 -/
def octant (f : List Nat) : Bool := (f.map faceAxis).eraseDups.length == 3

/-- 팔분면 면의 방향 (x, y, z 의 부호) — 무게중심의 좌표마다 ±φ ± 1 이므로 φ 쪽 부호가 정한다 -/
def octSigns (f : List Nat) : List Int :=
  [0, 1, 2].map fun k => ((f.filter fun i => faceAxis i == k).map faceSign).headD 0

/-- ★ 원 셋 사이의 자리 (정20면체의 면) 스물 = 정육면체 꼭짓점 쪽 여덟 (팔분면마다 하나 · 부호 (±, ±, ±) 여덟이 한 번씩)
    + 면 쪽 열둘 (정육면체 면마다 둘 — 그 면 위의 모서리를 품은 삼각형) · 다섯 겹 축마다 둘레 자리 다섯 -/
theorem twenty_is_eight_plus_twelve :
    (faces.filter octant).length = 8 ∧ ((faces.filter octant).map octSigns).eraseDups.length = 8 ∧
    ((faces.filter octant).map octSigns).all (fun l => l.all fun x => x == 1 || x == -1) = true ∧
    (faces.filter fun f => !octant f).length = 12 ∧
    faceList.all (fun F => ((faces.filter fun f => !octant f).filter fun f =>
      (f.filter fun i => onFace i F.1 F.2).length == 2).length == 2) = true ∧
    (List.range 6).all (fun k => (around k).length == 5) = true := by
  decide +kernel

/-! ## 7. 공 여섯 — 플러스 · 마이너스, 위 피라미드 하나 · 아래 하나 (정팔면체) · 여섯에서 열둘로 · 삼각형 3 · 4 · 5 · 6 · 7 -/

def oct6 : List (Int × Int × Int) := [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
def od2 (p q : Int × Int × Int) : Int := (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2
def ov (i : Nat) : Int × Int × Int := oct6.getD i (0, 0, 0)
def oadj (i j : Nat) : Bool := od2 (ov i) (ov j) == 2
def oEdges : List (Nat × Nat) :=
  (List.range 6).flatMap fun i => (List.range 6).filterMap fun j => if i < j ∧ oadj i j = true then some (i, j) else none
def oFaces : List (List Nat) :=
  (List.range 6).flatMap fun i => (List.range 6).flatMap fun j => (List.range 6).filterMap fun k =>
    if i < j ∧ j < k ∧ oadj i j = true ∧ oadj i k = true ∧ oadj j k = true then some [i, j, k] else none
def oSum (f : List Nat) : Int × Int × Int :=
  f.foldl (fun acc i => (acc.1 + (ov i).1, acc.2.1 + (ov i).2.1, acc.2.2 + (ov i).2.2)) (0, 0, 0)

/-- ★ 공 여섯 (±x · ±y · ±z) : 모서리 12 · 삼각형 면 8 · 오일러 2 · 면의 합이 (±1, ±1, ±1) 여덟 (팔분면 = 3태극 자리 여덟) ·
    +z 를 품은 면 4 (위 피라미드) · −z 를 품은 면 4 (아래 피라미드) · 둘은 겹치지 않고 합쳐 8 · 꼭짓점마다 이웃 넷 -/
theorem octahedron :
    oEdges.length = 12 ∧ oFaces.length = 8 ∧ (6 : Int) - 12 + 8 = 2 ∧
    (oFaces.map oSum).eraseDups.length = 8 ∧
    (oFaces.map oSum).all (fun s => (s.1 == 1 || s.1 == -1) && (s.2.1 == 1 || s.2.1 == -1) && (s.2.2 == 1 || s.2.2 == -1)) = true ∧
    (oFaces.filter fun f => f.contains 4).length = 4 ∧ (oFaces.filter fun f => f.contains 5).length = 4 ∧
    (oFaces.filter fun f => f.contains 4 && f.contains 5).length = 0 ∧
    (List.range 6).all (fun i => ((List.range 6).filter (oadj i)).length == 4) = true := by
  decide +kernel

/-- 두 피라미드의 부피 (셈만 · 기하는 아님) : 밑면 (대각선 2 · 2 인 정사각형) 넓이 2 · 높이 1 → 3 × 부피 = 2 — 둘이면 4/3 = 정육면체 [−1, 1]³ (부피 8) 의 1/6 -/
theorem two_pyramids : (2 * 2) / 2 = (2 : Int) ∧ 3 * 2 * 4 = 8 * 3 := by decide

/-- 가족 (0, ±t, ±1) 순환 : 같은 면의 짝 거리² 4t² · 이웃 면 사이 거리² 2t² − 2t + 2 — 차이 = −2(t² + t − 1) -/
theorem family_edges (t : Int) : (2 * t ^ 2 - 2 * t + 2) - 4 * t ^ 2 = -2 * (t ^ 2 + t - 1) := by grind

/-- ★ 모서리가 다 같아지는 t = φ − 1 (= 2cos 72°) 는 t² + t − 1 = 0 — Z[φ] 에서 정확히 · 그때 (0, ±t, ±1) 을 φ 배 하면 꼭짓점 (0, ±1, ±φ) -/
theorem family_golden :
    zadd (zadd (zmul (-1, 1) (-1, 1)) (-1, 1)) (-1, 0) = (0, 0) ∧ zmul (-1, 1) (0, 1) = (1, 0) := by decide

/-- 정육팔면체 (t = 1) : (0, ±1, ±1) 순환 12 점 · 가장 가까운 거리² 2 · 꼭짓점마다 이웃 넷 · 모서리 24 — 결정 (면심 입방) 의 이웃 열둘 -/
def cubo : List (Int × Int × Int) :=
  [(0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1),
   (1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0)]

theorem cuboctahedron :
    cubo.length = 12 ∧
    (List.range 12).all (fun i => ((List.range 12).filter fun j =>
      od2 (cubo.getD i (0, 0, 0)) (cubo.getD j (0, 0, 0)) == 2).length == 4) = true ∧
    ((List.range 12).flatMap fun i => (List.range 12).filter fun j =>
      i < j && od2 (cubo.getD i (0, 0, 0)) (cubo.getD j (0, 0, 0)) == 2).length = 24 := by
  decide +kernel

/-- ★ 꼭짓점에 정삼각형 n 개 : V (6 − n) = 12 · E = nV/2 · F = nV/3 · V − E + F = 2 — n = 3 · 4 · 5 에서 공 4 · 6 · 12 ·
    n = 6 은 모자람 0 (평면) · n = 7 은 넘침 (쌍곡) — 부호 6 − n 이 셋을 가른다 -/
theorem ladder :
    ([(3, 4), (4, 6), (5, 12)] : List (Int × Int)).all (fun p =>
      p.2 * (6 - p.1) == 12 && (p.1 * p.2) % 2 == 0 && (p.1 * p.2) % 3 == 0 &&
      p.2 - p.1 * p.2 / 2 + p.1 * p.2 / 3 == 2) = true ∧
    ([3, 4, 5, 6, 7] : List Int).map (fun n => 360 - 60 * n) = [180, 120, 60, 0, -60] := by
  decide

/-! ## 8. 검토 뒤 덧붙임 — 오일러를 셈한 수에 묶고, 사다리를 오일러에서 끌어내고, 가족의 거리를 직접 -/

/-- 오일러를 셈한 목록의 길이로 : 정20면체 · 정팔면체 · 반정12면체 (세 겹 축 10 · 피터슨 변 15 · 다섯 겹 축의 5-순환 6) -/
theorem euler_tied :
    (verts.length : Int) - edgeList.length + triangles.length = 2 ∧
    (oct6.length : Int) - oEdges.length + oFaces.length = 2 ∧
    (fpairs.length : Int) - ((List.range 10).flatMap fun i => (List.range 10).filter fun j => i < j && adjAx i j).length
      + ((List.range 6).filter fun k => (around k).length == 5).length = 1 := by
  decide +kernel

/-- ★ 꼭짓점마다 삼각형 n 개인 닫힌 다면체 : 2E = 3F · 2E = nV · V − E + F = 2 이면 V(6 − n) = 12 -/
theorem euler_ladder (V E F n : Int) (h1 : 2 * E = 3 * F) (h2 : 2 * E = n * V) (h3 : V - E + F = 2) :
    V * (6 - n) = 12 := by
  have e : V * (6 - n) = 6 * V - n * V := by grind
  rw [e]
  omega

/-- ★ 그 해는 셋뿐 : V > 0 · n ≥ 3 이면 (n, V) = (3, 4) · (4, 6) · (5, 12) — n = 6 은 평면 (V 가 없음) · n ≥ 7 은 쌍곡 -/
theorem ladder_unique (V n : Int) (hV : 0 < V) (hn : 3 ≤ n) (h : V * (6 - n) = 12) :
    (n = 3 ∧ V = 4) ∨ (n = 4 ∧ V = 6) ∨ (n = 5 ∧ V = 12) := by
  have hlt : n < 6 := by
    by_cases hge : 6 ≤ n
    · exfalso
      have : V * (6 - n) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    · omega
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 by omega) with e | e | e <;> subst e
  · left; constructor; rfl; omega
  · right; left; constructor; rfl; omega
  · right; right; constructor; rfl; omega

/-- 가족 (0, ±t, ±1) 의 거리를 직접 : 같은 면의 짝 4t² · 이웃 면 사이 2t² − 2t + 2 -/
theorem family_distances (t : Int) :
    od2 (0, t, 1) (0, -t, 1) = 4 * t ^ 2 ∧ od2 (0, t, 1) (t, 1, 0) = 2 * t ^ 2 - 2 * t + 2 := by
  simp only [od2]; constructor <;> grind

end Trombo.Icosa

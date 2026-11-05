/-
일곱 공 — 정수 고리 안에서 정확히 (린 4 코어)

1. 평면의 일곱 공 : 아이젠슈타인 정수 ℤ[ω] (ω² = −1 − ω) 의 노름 N(a + bω) = a² − ab + b² 로 거리²를 정수로 잰다.
   공 중심은 0 과 2u (u 는 단위 여섯 : ±1, ±ω, ±ω²). 반지름 1 의 공 일곱 개는
   · 서로 겹치지 않고 (모든 중심 거리² ≥ 4),
   · 둘레 여섯은 가운데와 양옆 이웃에 닿고 (거리² = 4),
   · 모든 중심이 원점에서 거리 2 안에 있어 반지름 3 의 큰 원 안에 꽉 들어간다.
2. 정다면체 다섯 : 황금 정수 ℤ[φ] (φ² = φ + 1) 좌표로, 다섯 입체의 꼭짓점이 저마다 한 구 위에 있다
   (|v|² 가 모두 같다). 정십이면체의 (0, ±1/φ, ±φ) 꼭짓점이 (±1, ±1, ±1) 과 같은 구에 놓이는 까닭은
   1/φ² + φ² = 3 이다. 꼭짓점 · 모서리 · 면 수는 오일러 V − E + F = 2 를 따른다.
고전 사실을 정수로 옮겨 커널이 확인한 것이다. 어떤 미해결 문제에 대해서도 주장하지 않는다.
-/
namespace SevenBalls

/-! ## 1. 아이젠슈타인 정수와 일곱 공 -/

/-- a + bω -/
structure E where
  a : Int
  b : Int
deriving DecidableEq, Repr

def E.sub (x y : E) : E := ⟨x.a - y.a, x.b - y.b⟩
/-- 노름 N(a + bω) = a² − ab + b² (= |a + bω|²) -/
def E.norm (x : E) : Int := x.a * x.a - x.a * x.b + x.b * x.b

/-- 여섯 단위 : 1, 1 + ω (= −ω²), ω, −1, −1 − ω (= ω²), −ω — 60° 씩 돈다 -/
def units : List E := [⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩]

/-- 일곱 중심 : 0 과 2u -/
def centers : List E := ⟨0, 0⟩ :: units.map (fun u => ⟨2 * u.a, 2 * u.b⟩)

theorem units_norm_one : units.all (fun u => u.norm = 1) = true := by decide

theorem seven_centers : centers.length = 7 := by decide

/-- 반지름 1 의 공 일곱 개는 서로 겹치지 않는다 : 다른 두 중심의 거리² ≥ 4 -/
theorem no_overlap : centers.all (fun x => centers.all (fun y => x == y || decide (4 ≤ (x.sub y).norm))) = true := by
  decide

/-- 둘레 공은 가운데 공에 닿는다 : 거리² = 4 -/
theorem touch_center : (centers.drop 1).all (fun x => (x.sub ⟨0, 0⟩).norm = 4) = true := by decide

/-- 둘레 공은 양옆 이웃에 닿는다 : 차례로 이웃한 두 중심의 거리² = 4 (마지막과 처음도) -/
theorem touch_ring :
    let r := centers.drop 1
    (List.range 6).all (fun t => ((r.getD t ⟨0, 0⟩).sub (r.getD ((t + 1) % 6) ⟨0, 0⟩)).norm = 4) = true := by
  decide

/-- 큰 원에 꽉 : 모든 중심이 원점에서 거리 ≤ 2 (거리² ≤ 4) 이므로 반지름 1 의 공은 반지름 3 의 원 안에 있고,
둘레 여섯은 거리 정확히 2 라 큰 원에 닿는다 -/
theorem inside_big : centers.all (fun x => decide (x.norm ≤ 4)) = true := by decide

/-! ## 2. 황금 정수와 정다면체 다섯 -/

/-- a + bφ, φ² = φ + 1 -/
structure G where
  a : Int
  b : Int
deriving DecidableEq, Repr

def G.add (x y : G) : G := ⟨x.a + y.a, x.b + y.b⟩
def G.sub (x y : G) : G := ⟨x.a - y.a, x.b - y.b⟩
/-- (a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ -/
def G.mul (x y : G) : G := ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

def φ : G := ⟨0, 1⟩
/-- 1/φ = φ − 1 -/
def iφ : G := ⟨-1, 1⟩
def g (n : Int) : G := ⟨n, 0⟩

theorem phi_inv : G.mul φ iφ = g 1 := by decide
/-- 1/φ² + φ² = 3 -/
theorem inv_sq_add_sq : (G.mul iφ iφ).add (G.mul φ φ) = g 3 := by decide

abbrev V3 := G × G × G
def n2 (v : V3) : G := ((G.mul v.1 v.1).add (G.mul v.2.1 v.2.1)).add (G.mul v.2.2 v.2.2)
def d2 (u v : V3) : G := n2 (u.1.sub v.1, u.2.1.sub v.2.1, u.2.2.sub v.2.2)

def neg (x : G) : G := ⟨-x.a, -x.b⟩
def sgn (s : Bool) (x : G) : G := if s then neg x else x
/-- 부호 여덟 가지 -/
def signs (v : V3) : List V3 :=
  [false, true].flatMap fun s1 => [false, true].flatMap fun s2 => [false, true].map fun s3 =>
    (sgn s1 v.1, sgn s2 v.2.1, sgn s3 v.2.2)
def cyc (v : V3) : List V3 := [v, (v.2.1, v.2.2, v.1), (v.2.2, v.1, v.2.1)]
def dedup (l : List V3) : List V3 := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def cube : List V3 := signs (g 1, g 1, g 1)
def tetra : List V3 := cube.filter fun v =>
  ([v.1, v.2.1, v.2.2].filter (fun c => decide (c.a < 0))).length % 2 == 0
def octa : List V3 := dedup ((signs (g 1, g 0, g 0)).flatMap cyc)
def icosa : List V3 := dedup ((signs (g 0, g 1, φ)).flatMap cyc)
def dodeca : List V3 := cube ++ dedup ((signs (g 0, iφ, φ)).flatMap cyc)

/-- 모든 꼭짓점의 |v|² 가 같다 = 한 구 위 -/
def onSphere (l : List V3) (r2 : G) : Bool := l.all fun v => n2 v == r2
/-- 거리² 가 a2 인 짝의 수 (모서리 수) -/
def edges (l : List V3) (a2 : G) : Nat :=
  ((List.range l.length).flatMap fun i => (List.range l.length).filter fun j =>
    decide (i < j) && d2 (l.getD i (g 0, g 0, g 0)) (l.getD j (g 0, g 0, g 0)) == a2).length

theorem tetra_sphere : tetra.length = 4 ∧ onSphere tetra (g 3) = true ∧ edges tetra (g 8) = 6 := by decide
theorem cube_sphere : cube.length = 8 ∧ onSphere cube (g 3) = true ∧ edges cube (g 4) = 12 := by decide
theorem octa_sphere : octa.length = 6 ∧ onSphere octa (g 1) = true ∧ edges octa (g 2) = 12 := by decide
/-- 정이십면체 : |v|² = 1 + φ² = 2 + φ, 모서리² = 4 -/
theorem icosa_sphere : icosa.length = 12 ∧ onSphere icosa ⟨2, 1⟩ = true ∧ edges icosa (g 4) = 30 := by
  decide +kernel
/-- 정십이면체 : 스무 꼭짓점이 모두 |v|² = 3 (1/φ² + φ² = 3 때문), 모서리² = 4/φ² = 4(2 − φ) -/
theorem dodeca_sphere : dodeca.length = 20 ∧ onSphere dodeca (g 3) = true ∧ edges dodeca ⟨8, -4⟩ = 30 := by
  decide +kernel

/-- 오일러 V − E + F = 2 : (4, 6, 4) · (8, 12, 6) · (6, 12, 8) · (12, 30, 20) · (20, 30, 12) -/
theorem euler_five :
    [(4, 6, 4), (8, 12, 6), (6, 12, 8), (12, 30, 20), (20, 30, 12)].all
      (fun (t : Int × Int × Int) => t.1 - t.2.1 + t.2.2 == 2) = true := by decide

end SevenBalls

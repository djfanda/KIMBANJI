/-
두 정사면체 — ± 짝으로 남은 축을 채우기 (린 4 코어 · 정수 좌표만)

정사면체는 홀로 자기 쌍대라 짝 없이 남는다. 그러나 «자리까지 정한» 쌍대(중심에 대한 극 쌍대)에서는
정사면체 T⁺ 의 쌍대가 뒤집힌 정사면체 T⁻ = −T⁺ 이다. 이 ± 두 개(ㅅ)를 붙이는 두 가지 방법을 커널이 확인한다.

1. 별 (서로 꿰기) : T⁺ = {(1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)} · T⁻ = −T⁺
   · T⁺ 의 면마다 바깥 법선이 맞은편 꼭짓점의 반대 −v 다 → 극 쌍대는 T⁻
   · T⁺ 와 T⁻ 의 꼭짓점을 합치면 정육면체의 여덟 꼭짓점 (바깥 = 정육면체)
   · T⁺ 와 T⁻ 의 겹친 속은 여덟 부등식 ±x ± y ± z ≤ 1 = 정팔면체 (속 = 정팔면체) — 꼭짓점은 두 정사면체 모서리의 가운데
   → ± 정사면체 한 쌍이 P 대 NP (정육면체) ↔ 호지 (정팔면체) 의 쌍대 짝을 낳는다.
2. 모래시계 (꼭짓점 맞대기) : T⁺ = {O, (1,1,0), (1,0,1), (0,1,1)} · T⁻ = −T⁺ (O 에 대한 점대칭)
   · 둘 다 정사면체 (모서리² 모두 2) · 공유하는 점은 허리 O 하나 · 평면 x + y + z = 0 이 둘을 가름
   · 꼭짓점은 모두 일곱 (O 와 둘레 여섯) — 일곱 공의 자리 수와 같다
3. 세 축이 모두 쌍대 : 자리까지 정한 쌍대로 보면 ±z = T⁺ ↔ T⁻ · ±x = 정육면체 ↔ 정팔면체 · ±y = 정이십면체 ↔ 정십이면체.

저자의 읽기 (수학 주장 아님) : 보이는 T⁺ = 유한체 · 알갱이 · 양–밀스의 보이는 쪽, 보이지 않는 T⁻ = 비율 ·
정사면체는 탄생과 죽음, 구에서 다시 정사면체로. 이 파일은 위의 좌표 사실만 판정하고, 어떤 열린 문제도 채우지 않는다.
-/
namespace TwoTetra

abbrev V := Int × Int × Int
def neg (v : V) : V := (-v.1, -v.2.1, -v.2.2)
def dot (u v : V) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
def sub (u v : V) : V := (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)
def d2 (u v : V) : Int := dot (sub u v) (sub u v)

/-! ## 1. 별 -/

def Tp : List V := [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
def Tm : List V := Tp.map neg
def cube : List V :=
  [(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)]

/-- 두 목록이 같은 원소들 (차례 무관 · 중복 없음 가정은 따로) -/
def sameSet (a b : List V) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

theorem tp_regular : (Tp.all fun u => Tp.all fun v => u == v || d2 u v == 8) = true := by decide
theorem tm_regular : (Tm.all fun u => Tm.all fun v => u == v || d2 u v == 8) = true := by decide

/-- 극 쌍대 : T⁺ 에서 v 의 맞은편 면 (나머지 세 꼭짓점) 은 모두 평면 (−v)·x = 1 위에 있고, v 는 그 반대쪽 (−v)·v = −3 < 1 -/
theorem polar_dual :
    (Tp.all fun v => (Tp.erase v).all (fun w => dot (neg v) w == 1) && decide (dot (neg v) v < 1)) = true := by decide

/-- 극 쌍대의 꼭짓점 (면 법선 −v) 을 모으면 T⁻ -/
theorem dual_is_Tm : sameSet (Tp.map neg) Tm = true := by decide

/-- 바깥 : T⁺ ∪ T⁻ = 정육면체의 여덟 꼭짓점 -/
theorem hull_cube : sameSet (Tp ++ Tm) cube = true ∧ (Tp ++ Tm).length = 8 := by decide

/-- 겹친 속 : T⁺ 의 부등식 (−v)·x ≤ 1 과 T⁻ 의 부등식 v·x ≤ 1 을 모으면 여덟 방향 s·x ≤ 1 (s ∈ {±1}³) — 정팔면체 |x| + |y| + |z| ≤ 1 -/
theorem core_octahedron : sameSet (Tp.map neg ++ Tp) cube = true := by decide

def octa : List V := [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- 정팔면체 꼭짓점은 두 정사면체 모두의 안 (부등식 여덟을 모두 만족 · 그 가운데 넷에서 등호) -/
theorem octa_in_both :
    (octa.all fun x => cube.all (fun s => decide (dot s x ≤ 1)) && (cube.filter (fun s => dot s x == 1)).length == 4) = true := by
  decide

/-- 정팔면체 꼭짓점의 두 배는 T⁺ 모서리 가운데의 두 배 (u + v) 이자 T⁻ 모서리 가운데의 두 배 -/
theorem octa_edge_midpoints :
    (octa.all fun x =>
      (Tp.any fun u => Tp.any fun v => u != v && (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2) == (2 * x.1, 2 * x.2.1, 2 * x.2.2)) &&
      (Tm.any fun u => Tm.any fun v => u != v && (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2) == (2 * x.1, 2 * x.2.1, 2 * x.2.2))) = true := by
  decide

/-! ## 2. 모래시계 -/

def Hp : List V := [(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)]
def Hm : List V := Hp.map neg

theorem hp_regular : (Hp.all fun u => Hp.all fun v => u == v || d2 u v == 2) = true := by decide
theorem hm_regular : (Hm.all fun u => Hm.all fun v => u == v || d2 u v == 2) = true := by decide

/-- 공유하는 꼭짓점은 허리 O 하나 -/
theorem waist_one : (Hp.filter (Hm.contains ·)) = [(0, 0, 0)] := by decide

/-- 평면 x + y + z = 0 이 둘을 가름 : T⁺ 쪽은 ≥ 0, T⁻ 쪽은 ≤ 0, 등호는 O 에서만 -/
theorem plane_separates :
    (Hp.all fun v => decide (0 ≤ dot (1, 1, 1) v)) = true ∧ (Hm.all fun v => decide (dot (1, 1, 1) v ≤ 0)) = true ∧
    ((Hp ++ Hm).filter (fun v => dot (1, 1, 1) v == 0)).eraseDups = [(0, 0, 0)] := by decide

/-- 꼭짓점은 모두 일곱 (O 와 둘레 여섯) -/
theorem seven_vertices : (Hp ++ Hm).eraseDups.length = 7 := by decide

/-- 둘레 여섯은 모두 허리에서 같은 거리 (거리² 2) -/
theorem six_around : ((Hp ++ Hm).eraseDups.filter (· != (0, 0, 0))).all (fun v => d2 v (0, 0, 0) == 2) = true := by decide

/-! ## 3. 자리까지 정한 쌍대로 보면 세 축이 모두 쌍대 -/

inductive Placed where
  | tetraPlus | tetraMinus | cube | octa | icosa | dodeca
deriving DecidableEq, Repr

/-- 중심에 대한 극 쌍대 (자리까지) -/
def polar : Placed → Placed
  | .tetraPlus => .tetraMinus | .tetraMinus => .tetraPlus
  | .cube => .octa | .octa => .cube
  | .icosa => .dodeca | .dodeca => .icosa

/-- 셋째 배치 : ±z = T⁺ ↔ T⁻ (양–밀스의 ±) · ±x = 정육면체 (P 대 NP) ↔ 정팔면체 (호지) · ±y = 정이십면체 (나비에–스토크스) ↔ 정십이면체 (BSD) -/
def axes : List (Placed × Placed) := [(.tetraPlus, .tetraMinus), (.cube, .octa), (.icosa, .dodeca)]

theorem all_three_axes_dual : (axes.all fun p => polar p.1 == p.2 && polar p.2 == p.1) = true := by decide

theorem polar_involutive :
    ([Placed.tetraPlus, .tetraMinus, .cube, .octa, .icosa, .dodeca].all fun p => polar (polar p) == p) = true := by decide

/-- 자리까지 정하면 자기 자신과 쌍대인 것은 없다 (T⁺ 의 쌍대도 T⁻) -/
theorem no_placed_self_dual :
    ([Placed.tetraPlus, .tetraMinus, .cube, .octa, .icosa, .dodeca].all fun p => polar p != p) = true := by decide

end TwoTetra

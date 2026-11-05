/-
분모와 분자를 바꾸면 — 린 4 커널 확인 (Mathlib 없이, 린 코어만 · import 없음)

뜻 : 극 역수. 반지름 1 인 공에서 면 n·x = d 의 쌍대 꼭짓점은 n/d — 면까지의 거리 d 가 꼭짓점의 분모로 내려간다.
그래서 꼭짓점 V ↔ 면 F, 모서리 E 는 그대로, 차원 k ↔ n − 1 − k.
사영 좌표로 적으면 면 (n, d) 와 점 [n : d] 는 같은 네 수이고, 놓임 n·v = d·w 는 두 쪽에 대칭이다.

■ 커널 확인 (이 파일 · 정리 40)
· 0. 극 역수 : 점 [v : w] 와 면 (n, d) 의 놓임 · 안쪽 판정이 대칭 (모든 정수) · 큐브 (±2)³ 의 면 e·x = 2 의 극 [e : 2] = e/2 는
     팔면체이고, 그 팔면체의 면은 큐브 꼭짓점의 극 · 사면체의 극 = 거꾸로 선 사면체, 둘의 꼭짓점 합 = 큐브의 여덟 꼭짓점.
· 1. 콘웨이 연산 11 개를 (V, E, F) 위 함수로 : d(xP) = y(dP) 다섯 짝 (t,k) (a,j) (e,o) (b,m) (s,g) — 모든 V E F ·
     모든 연산이 V − E + F 를 그대로 둠 · 씨앗 다섯 T C O D I 에서 아르키메데스 13 · 카탈랑 13 = 그 쌍대 (분모분자.md 표와 같음).
· 2. 각기둥 (2n, 3n, n+2) ↔ 쌍뿔 · 엇각기둥 (2n, 4n, 2n+2) ↔ 사다리꼴면체 — 모든 n.
· 3. 별 정다면체 넷 (χ = −6, −6, 2, 2) · 쌍대 짝 {5/2,5} ↔ {5,5/2} · {5/2,3} ↔ {3,5/2} · 깃발 셈 ·
     케일리 식 (분모가 밀도로 들어감) · {3, 4, 5, 5/2} 안에서 1/p + 1/q > 1/2 를 만족하는 짝은 12.
· 4. 데카르트 결손 (π 단위 분수) : V = 4/δ_V · F = 4/δ_F · δ_V/δ_F = F/V — 정다면체 다섯, 그리고 모든 p, q 의 일반 식.
· 5. 반다면체 넷 (χ = 1 · 두 배 = 정다면체) · 클라인 {7,3} ↔ {3,7} (χ = −4) · 골드버그 ↔ 측지 (모든 T) ·
     n 차원 큐브 ↔ 정축체 (n ≤ 8, 수열이 뒤집힘).
· 6. 부호 : 짝수 부호 T2 의 쌍대 = {000, 111} (코어의 두 0 점) · 해밍 [7,4] ↔ 심플렉스 [7,3] (128 낱말 전수) · 파노 극 a ↔ a^⊥.
· 7. 제타의 역수 지도 (정수 항등식) : 직선 Re s = σ 의 1/s 상은 원 — (σ² − t²)² + (2σt)² = (σ² + t²)² ·
     Re s = ½ → |w − 1| = 1 · Re s = 1 → |w − ½| = ½ · 리 지도 z = 1 − 1/s : 돌기 쪽 원 안 · 면 위 원 위 · 홈 쪽 원 밖 ·
     복비 (0, 1 ; ½, ∞) = −1 과 뫼비우스 불변.

주의 : 세 수 (V, E, F) 는 꼴을 정하지 않는다 — tC 와 tO, 10 각기둥과 십이면체는 세 수가 같고 꼴은 다르다.
△ 파이썬 수치 (이 파일 밖, 분모분자.py) : 볼록 38 개의 좌표 껍질 · 반지름 역수 · ζ 영점 50 개의 |z| = 1 · 대븐포트–헤일브론 선 밖 영점.
전언 (이 파일이 증명하지 않음) : 닫히는 정다면체는 5 + 4 = 9 뿐 (코시 1813) · 케일리 식의 일반형 (케일리 1859) ·
  리만 가설 ⇔ 모든 n ≥ 1 에서 λ_n ≥ 0 (리 1997).
□ 리만 가설은 열린 문제. 리 지도 정리들은 «Re s = ½ ⇔ |z| = 1» 을 바꿔 쓴 것일 뿐, 영점이 어디 있는지는 말하지 않는다.
«해석» : 7 절은 정수에서 커널이 확인했다. 정수 전체에서 맞는 다항 항등식은 다항식으로서 같으므로 실수 σ, t 에서도 맞고, (c) 의 세 판정은
  항등식 (S − 2)² + T² − (S² + T²) = 4 − 4S 에서 나오므로 실수에서도 같다 (이 다리는 커널 밖의 표준 사실).

검증 : lean 분모분자.lean  (린 v4.34.0 · decide +kernel · omega · grind · 끝의 #print axioms 가 공리 목록)
-/

namespace Trombo.Duality

/-! ## 0. 극 역수 — 면 (n, d) ↔ 점 [n : d] -/

/-- 세 정수 좌표 -/
abbrev Vec3 := Int × Int × Int

/-- 내적 -/
def dot3 (a b : Vec3) : Int := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- 사영 점 [u : w] (= u/w) 와 면 n·x = d : d·w − n·u 가 0 이면 면 위, 양수면 안쪽 -/
def side (n : Vec3) (d : Int) (p : Vec3 × Int) : Int := d * p.2 - dot3 n p.1

/-- 면 (n, d) 가 점 모음의 받침면 : 모든 점이 안쪽이거나 위, 정확히 k 개가 면 위 -/
def supports (pts : List (Vec3 × Int)) (n : Vec3) (d : Int) (k : Nat) : Bool :=
  pts.all (fun p => side n d p ≥ 0) && pts.countP (fun p => side n d p == 0) == k

def scale3 (c : Int) (a : Vec3) : Vec3 := (c * a.1, c * a.2.1, c * a.2.2)
def neg3 (a : Vec3) : Vec3 := scale3 (-1) a
def signs : List Vec3 := [(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)]
def axes : List Vec3 := [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
/-- 큐브 (±2, ±2, ±2) = 점 [v : 1] -/
def cube_h : List (Vec3 × Int) := signs.map fun s => (scale3 2 s, 1)
/-- 큐브의 면 e·x = 2 의 극 [e : 2] = e/2 — 거리 2 가 분모로 -/
def octa_h : List (Vec3 × Int) := axes.map fun e => (e, 2)
def tetra_v : List Vec3 := [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
def tetra_h : List (Vec3 × Int) := tetra_v.map fun v => (v, 1)
def anti_tetra_h : List (Vec3 × Int) := tetra_v.map fun v => (neg3 v, 1)

/-- 놓임은 대칭 : 점 [v : w] 가 면 (n, d) 위(안쪽) ⇔ 점 [n : d] 가 면 (v, w) 위(안쪽) — 모든 정수 -/
theorem polar_incidence_symmetric (n v : Vec3) (d w : Int) :
    (side n d (v, w) = 0 ↔ side v w (n, d) = 0) ∧ (side n d (v, w) ≥ 0 ↔ side v w (n, d) ≥ 0) := by
  obtain ⟨n1, n2, n3⟩ := n
  obtain ⟨v1, v2, v3⟩ := v
  simp only [side, dot3]
  constructor <;> grind

/-- 큐브의 여섯 면 e·x = 2 (넷씩) 의 극이 팔면체 · 큐브 꼭짓점의 극 v·x = 1 이 팔면체의 면 (셋씩) · 사면체의 극 = 거꾸로 선 사면체 · 둘의 합 = 큐브 꼭짓점 여덟 -/
theorem polar_cube_octa_tetra :
    axes.all (fun e => supports cube_h e 2 4) = true ∧
    cube_h.all (fun p => supports octa_h p.1 p.2 3) = true ∧
    tetra_h.all (fun p => supports anti_tetra_h p.1 p.2 3) = true ∧
    anti_tetra_h.all (fun p => supports tetra_h p.1 p.2 3) = true ∧
    signs.all (fun s => (tetra_v ++ tetra_v.map neg3).contains s) = true ∧
    (tetra_v ++ tetra_v.map neg3).length = 8 := by
  decide +kernel

/-! ## 1. 콘웨이 연산 — (V, E, F) 위의 함수 -/

/-- 꼴의 세 수 (꼭짓점 V, 모서리 E, 면 F) -/
abbrev VEF := Nat × Nat × Nat

def v_of : VEF → Nat
  | (v, _, _) => v
def e_of : VEF → Nat
  | (_, e, _) => e
def f_of : VEF → Nat
  | (_, _, f) => f

/-- 오일러 지표 V − E + F (정수) -/
def chi : VEF → Int
  | (v, e, f) => (v : Int) - e + f

/-- d 쌍대 : 꼭짓점과 면을 바꾼다 -/
def op_d : VEF → VEF
  | (v, e, f) => (f, e, v)
/-- a 모서리 가운데까지 깎기 -/
def op_a : VEF → VEF
  | (v, e, f) => (e, 2 * e, f + v)
/-- j 돌기가 모서리에서 만남 -/
def op_j : VEF → VEF
  | (v, e, f) => (f + v, 2 * e, e)
/-- t 꼭짓점 깎기 -/
def op_t : VEF → VEF
  | (v, e, f) => (2 * e, 3 * e, f + v)
/-- k 면마다 뿔 돌기 -/
def op_k : VEF → VEF
  | (v, e, f) => (v + f, 3 * e, 2 * e)
/-- e 면을 떼어 벌림 -/
def op_e : VEF → VEF
  | (v, e, f) => (2 * e, 4 * e, v + e + f)
/-- o 면을 연꼴 넷으로 -/
def op_o : VEF → VEF
  | (v, e, f) => (v + e + f, 4 * e, 2 * e)
/-- b 깎고 또 깎기 -/
def op_b : VEF → VEF
  | (v, e, f) => (4 * e, 6 * e, v + e + f)
/-- m 돌기 위의 돌기 -/
def op_m : VEF → VEF
  | (v, e, f) => (v + e + f, 6 * e, 4 * e)
/-- s 비틀어 벌림 -/
def op_s : VEF → VEF
  | (v, e, f) => (2 * e, 5 * e, f + v + 2 * e)
/-- g 오각 나선 -/
def op_g : VEF → VEF
  | (v, e, f) => (f + v + 2 * e, 5 * e, 2 * e)

def tetra : VEF := (4, 6, 4)
def cube : VEF := (8, 12, 6)
def octa : VEF := (6, 12, 8)
def dodeca : VEF := (20, 30, 12)
def icosa : VEF := (12, 30, 20)

/-- 쌍대를 두 번 하면 제자리 — 모든 V E F -/
theorem dual_involutive : ∀ p : VEF, op_d (op_d p) = p := by
  intro ⟨v, e, f⟩
  rfl

/-- d(tP) = k(dP) : 꼭짓점 깎기의 쌍대 = 쌍대에 뿔 돌기 — 모든 V E F -/
theorem dual_truncate_kis : ∀ p : VEF, op_d (op_t p) = op_k (op_d p) := by
  intro ⟨v, e, f⟩
  rfl

/-- d(aP) = j(dP) : 모서리 가운데까지 깎기의 쌍대 = 쌍대의 돌기가 모서리에서 만남 — 모든 V E F -/
theorem dual_ambo_join : ∀ p : VEF, op_d (op_a p) = op_j (op_d p) := by
  intro ⟨v, e, f⟩
  simp only [op_d, op_a, op_j, Prod.mk.injEq, and_true]
  omega

/-- d(eP) = o(dP) : 면 떼어 벌림의 쌍대 = 쌍대의 면을 연꼴 넷으로 — 모든 V E F -/
theorem dual_expand_ortho : ∀ p : VEF, op_d (op_e p) = op_o (op_d p) := by
  intro ⟨v, e, f⟩
  simp only [op_d, op_e, op_o, Prod.mk.injEq, and_true]
  omega

/-- d(bP) = m(dP) : 깎고 또 깎기의 쌍대 = 쌍대에 돌기 위의 돌기 — 모든 V E F -/
theorem dual_bevel_meta : ∀ p : VEF, op_d (op_b p) = op_m (op_d p) := by
  intro ⟨v, e, f⟩
  simp only [op_d, op_b, op_m, Prod.mk.injEq, and_true]
  omega

/-- d(sP) = g(dP) : 비틀어 벌림의 쌍대 = 쌍대의 오각 나선 — 모든 V E F -/
theorem dual_snub_gyro : ∀ p : VEF, op_d (op_s p) = op_g (op_d p) := by
  intro ⟨v, e, f⟩
  simp only [op_d, op_s, op_g, Prod.mk.injEq, and_true]
  omega

/-- 연산 11 개 모두 V − E + F 를 그대로 둔다 — 모든 V E F (구 · 사영 평면 · 클라인 판 어디서나) -/
theorem chi_kept_by_all_ops : ∀ p : VEF,
    chi (op_d p) = chi p ∧ chi (op_a p) = chi p ∧ chi (op_j p) = chi p ∧ chi (op_t p) = chi p ∧
    chi (op_k p) = chi p ∧ chi (op_e p) = chi p ∧ chi (op_o p) = chi p ∧ chi (op_b p) = chi p ∧
    chi (op_m p) = chi p ∧ chi (op_s p) = chi p ∧ chi (op_g p) = chi p := by
  intro ⟨v, e, f⟩
  simp only [chi, op_d, op_a, op_j, op_t, op_k, op_e, op_o, op_b, op_m, op_s, op_g]
  and_intros <;> omega

/-- V − E + F = 2 이면 연산 11 개 뒤에도 2 -/
theorem euler_two_kept : ∀ p : VEF, chi p = 2 →
    chi (op_d p) = 2 ∧ chi (op_a p) = 2 ∧ chi (op_j p) = 2 ∧ chi (op_t p) = 2 ∧
    chi (op_k p) = 2 ∧ chi (op_e p) = 2 ∧ chi (op_o p) = 2 ∧ chi (op_b p) = 2 ∧
    chi (op_m p) = 2 ∧ chi (op_s p) = 2 ∧ chi (op_g p) = 2 := by
  intro p h
  have k := chi_kept_by_all_ops p
  omega

/-- 정다면체 다섯 : 사면체는 자기 쌍대 · 큐브 ↔ 팔면체 · 십이면체 ↔ 이십면체 · 모두 χ = 2 -/
theorem platonic_duals :
    op_d tetra = tetra ∧ op_d cube = octa ∧ op_d octa = cube ∧ op_d dodeca = icosa ∧ op_d icosa = dodeca ∧
    [tetra, cube, octa, dodeca, icosa].map chi = [2, 2, 2, 2, 2] := by
  decide +kernel

/-- 아르키메데스 13 (분모분자.md 표 순서 : tT aC tC tO eC bC sC aD tD tI eD bD sD) -/
def archimedean : List VEF :=
  [op_t tetra, op_a cube, op_t cube, op_t octa, op_e cube, op_b cube, op_s cube,
   op_a dodeca, op_t dodeca, op_t icosa, op_e dodeca, op_b dodeca, op_s dodeca]

/-- 카탈랑 13 (같은 순서 : kT jC kO kC oC mC gC jD kI kD oD mD gD) -/
def catalan : List VEF :=
  [op_k tetra, op_j cube, op_k octa, op_k cube, op_o cube, op_m cube, op_g cube,
   op_j dodeca, op_k icosa, op_k dodeca, op_o dodeca, op_m dodeca, op_g dodeca]

/-- 씨앗 다섯에서 지은 아르키메데스 13 의 (V, E, F) 가 표와 같고 모두 χ = 2 -/
theorem archimedean_thirteen :
    archimedean = [(12, 18, 8), (12, 24, 14), (24, 36, 14), (24, 36, 14), (24, 48, 26), (48, 72, 26), (24, 60, 38),
      (30, 60, 32), (60, 90, 32), (60, 90, 32), (60, 120, 62), (120, 180, 62), (60, 150, 92)] ∧
    archimedean.all (fun p => chi p == 2) = true := by
  decide +kernel

/-- 카탈랑 13 의 (V, E, F) 가 표와 같고, 하나하나가 짝 아르키메데스의 쌍대 -/
theorem catalan_thirteen_are_duals :
    catalan = [(8, 18, 12), (14, 24, 12), (14, 36, 24), (14, 36, 24), (26, 48, 24), (26, 72, 48), (38, 60, 24),
      (32, 60, 30), (32, 90, 60), (32, 90, 60), (62, 120, 60), (62, 180, 120), (92, 150, 60)] ∧
    catalan = archimedean.map op_d := by
  decide +kernel

/-- 껍질 ↔ 홈 : 사면체 + 돌기 = 큐브 (jT) ↔ 사면체 − 꼭지 = 팔면체 (aT) · 케플러의 jC = jO · aC = aO · tC 와 tO 는 세 수만 같음 -/
theorem shell_groove_tetra :
    op_j tetra = cube ∧ op_a tetra = octa ∧ op_d (op_j tetra) = op_a tetra ∧
    op_j cube = op_j octa ∧ op_a cube = op_a octa ∧ op_j cube = (14, 24, 12) ∧ op_t cube = op_t octa := by
  decide +kernel

/-! ## 2. 각기둥 ↔ 쌍뿔 · 엇각기둥 ↔ 사다리꼴면체 -/

def prism (n : Nat) : VEF := (2 * n, 3 * n, n + 2)
def bipyramid (n : Nat) : VEF := (n + 2, 3 * n, 2 * n)
def antiprism (n : Nat) : VEF := (2 * n, 4 * n, 2 * n + 2)
def trapezohedron (n : Nat) : VEF := (2 * n + 2, 4 * n, 2 * n)

/-- 모든 n : 각기둥 ↔ 쌍뿔, 엇각기둥 ↔ 사다리꼴면체 (V ↔ F, E 그대로) -/
theorem prism_antiprism_duals : ∀ n : Nat,
    op_d (prism n) = bipyramid n ∧ op_d (bipyramid n) = prism n ∧
    op_d (antiprism n) = trapezohedron n ∧ op_d (trapezohedron n) = antiprism n :=
  fun _ => ⟨rfl, rfl, rfl, rfl⟩

/-- 모든 n : 네 갈래 모두 V − E + F = 2 -/
theorem prism_family_euler : ∀ n : Nat,
    chi (prism n) = 2 ∧ chi (bipyramid n) = 2 ∧ chi (antiprism n) = 2 ∧ chi (trapezohedron n) = 2 := by
  intro n
  simp only [chi, prism, bipyramid, antiprism, trapezohedron]
  and_intros <;> omega

/-- 표의 n = 3 … 12 · 4 각기둥 = 큐브 · 3 엇각기둥 = 팔면체 · 10 각기둥은 십이면체와 세 수만 같음 -/
theorem prism_table :
    (List.range 10).map (fun i => prism (i + 3)) =
      [(6, 9, 5), (8, 12, 6), (10, 15, 7), (12, 18, 8), (14, 21, 9), (16, 24, 10), (18, 27, 11), (20, 30, 12),
       (22, 33, 13), (24, 36, 14)] ∧
    (List.range 10).map (fun i => antiprism (i + 3)) =
      [(6, 12, 8), (8, 16, 10), (10, 20, 12), (12, 24, 14), (14, 28, 16), (16, 32, 18), (18, 36, 20), (20, 40, 22),
       (22, 44, 24), (24, 48, 26)] ∧
    prism 4 = cube ∧ bipyramid 4 = octa ∧ antiprism 3 = octa ∧ trapezohedron 3 = cube ∧ prism 10 = dodeca := by
  decide +kernel

/-! ## 3. 별 정다면체 — 분모 있는 슐레플리 기호 -/

/-- 분수 n/d 를 정수 짝 (n, d) 로 -/
abbrev Frac := Nat × Nat

/-- 정다면체 {p, q} : 기호 · 세 수 · 밀도 -/
structure Regular where
  p : Frac
  q : Frac
  vef : VEF
  density : Nat
  deriving DecidableEq

def tetra_r : Regular := ⟨(3, 1), (3, 1), tetra, 1⟩
def cube_r : Regular := ⟨(4, 1), (3, 1), cube, 1⟩
def octa_r : Regular := ⟨(3, 1), (4, 1), octa, 1⟩
def dodeca_r : Regular := ⟨(5, 1), (3, 1), dodeca, 1⟩
def icosa_r : Regular := ⟨(3, 1), (5, 1), icosa, 1⟩
/-- 작은 별 십이면체 {5/2, 5} -/
def small_stellated : Regular := ⟨(5, 2), (5, 1), (12, 30, 12), 3⟩
/-- 큰 십이면체 {5, 5/2} -/
def great_dodeca : Regular := ⟨(5, 1), (5, 2), (12, 30, 12), 3⟩
/-- 큰 별 십이면체 {5/2, 3} -/
def great_stellated : Regular := ⟨(5, 2), (3, 1), (20, 30, 12), 7⟩
/-- 큰 이십면체 {3, 5/2} -/
def great_icosa : Regular := ⟨(3, 1), (5, 2), (12, 30, 20), 7⟩

def stars : List Regular := [small_stellated, great_dodeca, great_stellated, great_icosa]
def regulars : List Regular := [tetra_r, cube_r, octa_r, dodeca_r, icosa_r] ++ stars

/-- 쌍대 : 기호 {p, q} ↔ {q, p}, V ↔ F, 밀도 그대로 -/
def dual_reg (r : Regular) : Regular := ⟨r.q, r.p, op_d r.vef, r.density⟩

/-- 별 정다면체 넷의 (V, E, F) 와 χ = −6, −6, 2, 2 -/
theorem star_counts_chi :
    stars.map (·.vef) = [(12, 30, 12), (12, 30, 12), (20, 30, 12), (12, 30, 20)] ∧
    stars.map (fun r => chi r.vef) = [-6, -6, 2, 2] := by
  decide +kernel

/-- 쌍대 짝 {5/2,5} ↔ {5,5/2} · {5/2,3} ↔ {3,5/2} · 아홉은 쌍대로 닫힘 -/
theorem star_dual_pairs :
    dual_reg small_stellated = great_dodeca ∧ dual_reg great_dodeca = small_stellated ∧
    dual_reg great_stellated = great_icosa ∧ dual_reg great_icosa = great_stellated ∧
    regulars.all (fun r => regulars.contains (dual_reg r)) = true := by
  decide +kernel

/-- 깃발 셈 : 면의 분자 × F = 2E = 꼭짓점 그림의 분자 × V — 아홉 모두 -/
theorem regular_flags :
    regulars.all (fun r => r.p.1 * f_of r.vef == 2 * e_of r.vef && r.q.1 * v_of r.vef == 2 * e_of r.vef) = true := by
  decide +kernel

/-- 케일리 식 : (q 의 분모)·V − E + (p 의 분모)·F = 2 × 밀도 — 아홉 모두 (일반형은 전언) -/
theorem cayley_density :
    regulars.all (fun r =>
      ((r.q.2 * v_of r.vef : Nat) : Int) - (e_of r.vef : Int) + ((r.p.2 * f_of r.vef : Nat) : Int) ==
        2 * (r.density : Int)) = true := by
  decide +kernel

def symbols : List Frac := [(3, 1), (4, 1), (5, 1), (5, 2)]
/-- 1/p + 1/q > 1/2 를 교차 곱으로 : p = a/b, q = c/d 이면 2(bc + ad) > ac -/
def spherical (p q : Frac) : Bool := decide (p.1 * q.1 < 2 * (p.2 * q.1 + p.1 * q.2))
def admissible : List (Frac × Frac) :=
  (symbols.flatMap fun p => symbols.map fun q => (p, q)).filter fun pq => spherical pq.1 pq.2

-- 닫히는 정다면체가 이 아홉뿐이라는 것은 코시 1813 · 전언 — 아래 정리는 부등식의 셈과 목록의 포함만 확인한다
/-- {3, 4, 5, 5/2} 의 16 짝 가운데 부등식을 만족하는 것은 12 · 정다면체 아홉은 모두 그 안 · 남는 셋 {4,5/2} {5/2,4} {5/2,5/2} -/
theorem fraction_inequality :
    admissible = [((3, 1), (3, 1)), ((3, 1), (4, 1)), ((3, 1), (5, 1)), ((3, 1), (5, 2)), ((4, 1), (3, 1)),
      ((4, 1), (5, 2)), ((5, 1), (3, 1)), ((5, 1), (5, 2)), ((5, 2), (3, 1)), ((5, 2), (4, 1)), ((5, 2), (5, 1)),
      ((5, 2), (5, 2))] ∧
    regulars.all (fun r => admissible.contains (r.p, r.q)) = true ∧
    admissible.filter (fun pq => !(regulars.any fun r => (r.p, r.q) == pq)) =
      [((4, 1), (5, 2)), ((5, 2), (4, 1)), ((5, 2), (5, 2))] := by
  decide +kernel

/-! ## 4. 데카르트 결손 — π 단위 분수를 정수 짝으로 -/

/-- 꼭짓점 결손 δ_V = 2 − q(p − 2)/p 를 (분자, 분모) 로 -/
def deficit_v (p q : Int) : Int × Int := (2 * p - q * (p - 2), p)
/-- 면 결손 δ_F = 2 − p(q − 2)/q 를 (분자, 분모) 로 -/
def deficit_f (p q : Int) : Int × Int := (2 * q - p * (q - 2), q)
/-- 분수 같음 a/b = c/d ⇔ a·d = b·c -/
def frac_eq (x y : Int × Int) : Bool := x.1 * y.2 == x.2 * y.1

/-- 정다면체 다섯 : {p, q} · V · F · 표의 δ_V · δ_F (기약) -/
def deficit_rows : List (Int × Int × Int × Int × (Int × Int) × (Int × Int)) :=
  [(3, 3, 4, 4, (1, 1), (1, 1)), (4, 3, 8, 6, (1, 2), (2, 3)), (3, 4, 6, 8, (2, 3), (1, 2)),
   (5, 3, 20, 12, (1, 5), (1, 3)), (3, 5, 12, 20, (1, 3), (1, 5))]

/-- 정다면체 다섯에서 δ_V · δ_F 가 표와 같고, V = 4/δ_V · F = 4/δ_F · δ_V/δ_F = F/V -/
theorem descartes_deficit_table :
    deficit_rows.all (fun (p, q, V, F, dv, df) =>
      frac_eq (deficit_v p q) dv && frac_eq (deficit_f p q) df &&
      V * (deficit_v p q).1 == 4 * (deficit_v p q).2 && F * (deficit_f p q).1 == 4 * (deficit_f p q).2 &&
      (deficit_v p q).1 * (deficit_f p q).2 * V == (deficit_v p q).2 * (deficit_f p q).1 * F) = true := by
  decide +kernel

/-- 모든 정수 p, q : 두 결손의 분자는 같은 4 − (p−2)(q−2) 이고, V = 4/δ_V · F = 4/δ_F 이면 δ_V/δ_F = F/V -/
theorem deficit_general (p q V F : Int) :
    (deficit_v p q).1 = (deficit_f p q).1 ∧ (deficit_v p q).1 = 4 - (p - 2) * (q - 2) ∧
    (V * (deficit_v p q).1 = 4 * p → F * (deficit_f p q).1 = 4 * q →
      (deficit_v p q).1 * q * V = p * (deficit_f p q).1 * F) := by
  simp only [deficit_v, deficit_f]
  refine ⟨by grind, by grind, fun h1 h2 => by grind⟩

/-! ## 5. 반다면체 · 클라인 · 골드버그 · n 차원 큐브 -/

def hemicube : VEF := (4, 6, 3)
def hemioctahedron : VEF := (3, 6, 4)
def hemidodecahedron : VEF := (10, 15, 6)
def hemiicosahedron : VEF := (6, 15, 10)
def double : VEF → VEF
  | (v, e, f) => (2 * v, 2 * e, 2 * f)

/-- 반다면체 넷 : χ = 1 · 쌍대 짝 · 두 배 하면 정다면체 (사영 평면의 두 겹 = 구) -/
theorem hemi_four :
    [hemicube, hemioctahedron, hemidodecahedron, hemiicosahedron].map chi = [1, 1, 1, 1] ∧
    op_d hemicube = hemioctahedron ∧ op_d hemidodecahedron = hemiicosahedron ∧
    double hemicube = cube ∧ double hemioctahedron = octa ∧
    double hemidodecahedron = dodeca ∧ double hemiicosahedron = icosa := by
  decide +kernel

def klein73 : VEF := (56, 84, 24)
def klein37 : VEF := (24, 84, 56)

/-- 클라인 {7,3} (56, 84, 24) ↔ {3,7} (24, 84, 56) · χ = −4 = 2 − 2·3 (종수 3) · 7F = 2E = 3V -/
theorem klein_quartic_pair :
    op_d klein73 = klein37 ∧ chi klein73 = -4 ∧ chi klein37 = -4 ∧ chi klein73 = 2 - 2 * 3 ∧
    7 * f_of klein73 = 2 * e_of klein73 ∧ 3 * v_of klein73 = 2 * e_of klein73 := by
  decide +kernel

def goldberg (T : Nat) : VEF := (20 * T, 30 * T, 10 * T + 2)
def geodesic (T : Nat) : VEF := (10 * T + 2, 30 * T, 20 * T)
def hexagons (T : Nat) : Nat := 10 * (T - 1)

/-- 모든 T : 골드버그 ↔ 측지 쌍대 · T ≥ 1 이면 χ = 2 · 오각 12 + 육각 10(T−1) = F · 5·12 + 6·육각 = 2E = 3V -/
theorem goldberg_every_t : ∀ T : Nat,
    op_d (goldberg T) = geodesic T ∧
    (1 ≤ T → chi (goldberg T) = 2 ∧ chi (geodesic T) = 2 ∧ 12 + hexagons T = f_of (goldberg T) ∧
      5 * 12 + 6 * hexagons T = 2 * e_of (goldberg T) ∧ 3 * v_of (goldberg T) = 2 * e_of (goldberg T)) := by
  intro T
  refine ⟨rfl, fun hT => ?_⟩
  simp only [chi, goldberg, geodesic, hexagons, f_of, e_of, v_of]
  and_intros <;> omega

def gp_list : List (Nat × Nat) := [(1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (4, 0)]

/-- 표의 GP(m,n) : T = m² + mn + n² · 육각 수 · GP(1,0) = 십이면체 · GP(1,1) = tI (깎은 이십면체) · 측지 = kD -/
theorem goldberg_table :
    gp_list.map (fun (m, n) => m * m + m * n + n * n) = [1, 3, 4, 7, 12, 9, 13, 16] ∧
    [1, 3, 4, 7, 12, 9, 13, 16].map hexagons = [0, 20, 30, 60, 110, 80, 120, 150] ∧
    goldberg 1 = dodeca ∧ geodesic 1 = icosa ∧ goldberg 3 = op_t icosa ∧ geodesic 3 = op_k dodeca := by
  decide +kernel

/-- 이항계수 (자체 정의) -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- n 차원 큐브의 k 차원 면 수 f_k = C(n,k)·2^(n−k), k = 0 … n−1 -/
def cube_f (n : Nat) : List Nat := (List.range n).map fun k => binom n k * 2 ^ (n - k)
/-- n 차원 정축체의 k 차원 면 수 f_k = C(n,k+1)·2^(k+1), k = 0 … n−1 -/
def cross_f (n : Nat) : List Nat := (List.range n).map fun k => binom n (k + 1) * 2 ^ (k + 1)
/-- 번갈아 더하기 f_0 − f_1 + f_2 − … -/
def alt_sum : List Nat → Int
  | [] => 0
  | x :: xs => (x : Int) - alt_sum xs

/-- n ≤ 8 : 큐브의 수열 = 정축체 수열을 뒤집은 것 (차원 k ↔ n−1−k) · 둘 다 번갈아 합 1 − (−1)^n -/
theorem cube_cross_reverse :
    (List.range 9).all (fun n => cube_f n == (cross_f n).reverse) = true ∧
    cube_f 4 = [16, 32, 24, 8] ∧ cross_f 4 = [8, 24, 32, 16] ∧
    cube_f 8 = [256, 1024, 1792, 1792, 1120, 448, 112, 16] ∧
    (List.range 9).all (fun n => alt_sum (cube_f n) == 1 - (-1) ^ n && alt_sum (cross_f n) == 1 - (-1) ^ n) = true := by
  decide +kernel

/-! ## 6. 부호와 파노 — 내적 0 의 쌍대 -/

/-- 낮은 k 비트의 1 의 개수 홀짝 -/
def parity_bits : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, x => (x % 2 == 1) != parity_bits k (x / 2)
/-- 낮은 k 비트의 1 의 개수 -/
def ones : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => x % 2 + ones k (x / 2)
/-- 길이 n 낱말의 내적 (F₂) -/
def dot (n a b : Nat) : Bool := parity_bits n (a &&& b)
/-- 쌍대 부호 : 모든 부호어와 내적 0 인 낱말 전부 (2^n 개를 모두 셈) -/
def dual_code (n : Nat) (C : List Nat) : List Nat :=
  (List.range (2 ^ n)).filter fun w => C.all fun c => !dot n w c
/-- 짝수 부호 T2 = {000, 110, 101, 011} — 큐브 안의 정사면체 -/
def even_code : List Nat := [0, 6, 5, 3]

/-- T2 의 쌍대 = {000, 111} (큰 대각선 두 끝 · 코어의 두 0 점) · 다시 쌍대하면 T2 -/
theorem even_code_dual : dual_code 3 even_code = [0, 7] ∧ dual_code 3 [0, 7] = [0, 3, 5, 6] := by
  decide +kernel

/-- 검사 행 셋 : 자리 i (0 … 6) 의 열 = i + 1 의 이진 -/
def check_rows : List Nat :=
  (List.range 3).map fun j => (List.range 7).foldl (fun s i => if ((i + 1) >>> j) % 2 == 1 then s + 2 ^ i else s) 0
/-- 심플렉스 [7,3] = 검사 행 셋의 생성 -/
def simplex : List Nat :=
  (List.range 128).filter fun w => [0, 85].any fun x => [0, 102].any fun y => [0, 120].any fun z => w == (x ^^^ y ^^^ z)
/-- 해밍 [7,4] = 심플렉스의 쌍대 -/
def hamming : List Nat := dual_code 7 simplex
/-- 신드롬 : 켜진 자리 i 의 (i + 1) 을 모두 XOR (해밍 부호를 따로 정의하는 검사) -/
def syndrome (w : Nat) : Nat := (List.range 7).foldl (fun s i => if (w >>> i) % 2 == 1 then s ^^^ (i + 1) else s) 0

/-- 128 낱말 전수 : 심플렉스 8 낱말의 쌍대 = 신드롬 0 인 해밍 16 낱말 · 다시 쌍대하면 심플렉스 · 심플렉스의 0 아닌 낱말은 모두 무게 4 -/
theorem hamming_simplex_dual :
    check_rows = [85, 102, 120] ∧ simplex = [0, 30, 45, 51, 75, 85, 102, 120] ∧ hamming.length = 16 ∧
    hamming = (List.range 128).filter (fun w => syndrome w == 0) ∧
    dual_code 7 hamming = simplex ∧ simplex.all (fun w => w == 0 || ones 7 w == 4) = true := by
  decide +kernel

def fano_pts : List Nat := [1, 2, 3, 4, 5, 6, 7]
/-- 점 a 의 쌍대 줄 a^⊥ = {x : a·x = 0} -/
def polar_line (a : Nat) : List Nat := fano_pts.filter fun x => !dot 3 a x

/-- 파노 : a ↦ a^⊥ 가 점 7 ↔ 줄 7 의 일대일 · 놓임 x ∈ a^⊥ ⇔ a ∈ x^⊥ · 줄은 XOR 로 닫힘 · 두 점에 줄 하나 · 두 줄에 점 하나 · 자기 줄 위의 점 = 짝수 점 = 7^⊥ -/
theorem fano_polarity :
    fano_pts.all (fun a => (polar_line a).length == 3) = true ∧
    fano_pts.all (fun a => fano_pts.all fun b => a == b || polar_line a != polar_line b) = true ∧
    fano_pts.all (fun x => fano_pts.all fun a => (polar_line a).contains x == (polar_line x).contains a) = true ∧
    fano_pts.all (fun a => (polar_line a).all fun x => (polar_line a).all fun y =>
      x == y || (polar_line a).contains (x ^^^ y)) = true ∧
    fano_pts.all (fun x => fano_pts.all fun y =>
      x == y || (fano_pts.filter fun a => (polar_line a).contains x && (polar_line a).contains y).length == 1) = true ∧
    fano_pts.all (fun a => fano_pts.all fun b =>
      a == b || ((polar_line a).filter fun x => (polar_line b).contains x).length == 1) = true ∧
    fano_pts.filter (fun a => (polar_line a).contains a) = [3, 5, 6] ∧ polar_line 7 = [3, 5, 6] := by
  decide +kernel

/-! ## 7. 제타의 역수 지도 — 분모를 없앤 정수 항등식 -/

/-- 직선 Re s = σ 의 1/s 상은 원 |2σ·w − 1| = 1 : 분모를 없애면 피타고라스 매개 (σ² − t²)² + (2σt)² = (σ² + t²)² -/
theorem pythagorean_param : ∀ m n : Int, (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  intro m n
  grind

/-- (a) s = ½ + it 이면 w = 1/s = (2 − 4it)/(1 + 4t²) 는 원 |w − 1| = 1 위 -/
theorem half_line_to_unit_circle : ∀ t : Int, (2 - (1 + 4 * t ^ 2)) ^ 2 + (4 * t) ^ 2 = (1 + 4 * t ^ 2) ^ 2 := by
  intro t
  grind

/-- (b) 천장 s = 1 + it 이면 w = (1 − it)/(1 + t²) 는 원 |w − ½| = ½ 위 (|2w − 1| = 1) -/
theorem one_line_to_half_circle : ∀ t : Int, (2 - (1 + t ^ 2)) ^ 2 + (2 * t) ^ 2 = (1 + t ^ 2) ^ 2 := by
  intro t
  grind

/-- (c) 리 지도 |z|² = |s − 1|²/|s|², S = 2σ · T = 2t : 돌기 쪽 (σ > ½) 원 안 · 면 위 (σ = ½) 원 위 · 홈 쪽 (σ < ½) 원 밖 -/
theorem li_map_sides : ∀ S T : Int,
    ((S - 2) ^ 2 + T ^ 2 < S ^ 2 + T ^ 2 ↔ 1 < S) ∧
    ((S - 2) ^ 2 + T ^ 2 = S ^ 2 + T ^ 2 ↔ S = 1) ∧
    (S ^ 2 + T ^ 2 < (S - 2) ^ 2 + T ^ 2 ↔ S < 1) := by
  intro S T
  refine ⟨by grind, by grind, by grind⟩

/-- 사영 좌표 [x : y] (정수 짝) -/
abbrev Proj := Int × Int
/-- 괄호 [p, q] = x_p·y_q − x_q·y_p -/
def bracket (p q : Proj) : Int := p.1 * q.2 - q.1 * p.2
/-- 복비 (a, b ; c, d) = [c,a][d,b] / ([c,b][d,a]) 를 (분자, 분모) 로 -/
def cross_ratio (a b c d : Proj) : Int × Int := (bracket c a * bracket d b, bracket c b * bracket d a)
/-- 뫼비우스 변환 z ↦ (αz + β)/(γz + δ) 를 사영 좌표에 -/
def mobius (M : Int × Int × Int × Int) (p : Proj) : Proj :=
  (M.1 * p.1 + M.2.1 * p.2, M.2.2.1 * p.1 + M.2.2.2 * p.2)
def det2 (M : Int × Int × Int × Int) : Int := M.1 * M.2.2.2 - M.2.1 * M.2.2.1
def pt_zero : Proj := (0, 1)
def pt_one : Proj := (1, 1)
def pt_half : Proj := (1, 2)
def pt_inf : Proj := (1, 0)
/-- 리 지도 z = 1 − 1/s = (s − 1)/s -/
def li_mat : Int × Int × Int × Int := (1, -1, 1, 0)
/-- 역수 지도 w = 1/s -/
def inv_mat : Int × Int × Int × Int := (0, 1, 1, 0)

/-- 뫼비우스 변환은 괄호를 det 배 한다 — 모든 정수 -/
theorem bracket_mobius : ∀ (M : Int × Int × Int × Int) (p q : Proj),
    bracket (mobius M p) (mobius M q) = det2 M * bracket p q := by
  intro ⟨a, b, c, d⟩ ⟨x, y⟩ ⟨u, w⟩
  simp only [bracket, mobius, det2]
  grind

/-- 복비의 분자와 분모가 함께 det² 배 — 그래서 det ≠ 0 이면 복비 불변 (모든 정수) -/
theorem cross_ratio_mobius : ∀ (M : Int × Int × Int × Int) (a b c d : Proj),
    cross_ratio (mobius M a) (mobius M b) (mobius M c) (mobius M d) =
      (det2 M ^ 2 * (cross_ratio a b c d).1, det2 M ^ 2 * (cross_ratio a b c d).2) := by
  intro M a b c d
  simp only [cross_ratio, bracket_mobius, Prod.mk.injEq]
  constructor <;> grind

/-- (d) 복비 (0, 1 ; ½, ∞) = −1 · 리 지도로 (∞, 0 ; −1, 1) · 역수 지도로 (∞, 1 ; 2, 0) — 복비는 그대로 −1 -/
theorem harmonic_quadruple :
    cross_ratio pt_zero pt_one pt_half pt_inf = (1, -1) ∧
    [pt_zero, pt_one, pt_half, pt_inf].map (mobius li_mat) = [(-1, 0), (0, 1), (-1, 1), (1, 1)] ∧
    [pt_zero, pt_one, pt_half, pt_inf].map (mobius inv_mat) = [(1, 0), (1, 1), (2, 1), (0, 1)] ∧
    cross_ratio (-1, 0) (0, 1) (-1, 1) (1, 1) = (1, -1) ∧
    cross_ratio (1, 0) (1, 1) (2, 1) (0, 1) = (1, -1) ∧ det2 li_mat = 1 ∧ det2 inv_mat = -1 := by
  decide +kernel

/-- 모든 정수 a ≠ b : 가운데 (a+b)/2 는 a, b 에 대해 ∞ 의 조화 켤레 (복비 −1) -/
theorem midpoint_harmonic : ∀ a b : Int, a ≠ b →
    (cross_ratio (a, 1) (b, 1) (a + b, 2) (1, 0)).1 = -(cross_ratio (a, 1) (b, 1) (a + b, 2) (1, 0)).2 ∧
    (cross_ratio (a, 1) (b, 1) (a + b, 2) (1, 0)).2 ≠ 0 := by
  intro a b h
  simp only [cross_ratio, bracket]
  constructor <;> grind

end Trombo.Duality

#print axioms Trombo.Duality.polar_incidence_symmetric
#print axioms Trombo.Duality.polar_cube_octa_tetra
#print axioms Trombo.Duality.dual_involutive
#print axioms Trombo.Duality.dual_truncate_kis
#print axioms Trombo.Duality.dual_ambo_join
#print axioms Trombo.Duality.dual_expand_ortho
#print axioms Trombo.Duality.dual_bevel_meta
#print axioms Trombo.Duality.dual_snub_gyro
#print axioms Trombo.Duality.chi_kept_by_all_ops
#print axioms Trombo.Duality.euler_two_kept
#print axioms Trombo.Duality.platonic_duals
#print axioms Trombo.Duality.archimedean_thirteen
#print axioms Trombo.Duality.catalan_thirteen_are_duals
#print axioms Trombo.Duality.shell_groove_tetra
#print axioms Trombo.Duality.prism_antiprism_duals
#print axioms Trombo.Duality.prism_family_euler
#print axioms Trombo.Duality.prism_table
#print axioms Trombo.Duality.star_counts_chi
#print axioms Trombo.Duality.star_dual_pairs
#print axioms Trombo.Duality.regular_flags
#print axioms Trombo.Duality.cayley_density
#print axioms Trombo.Duality.fraction_inequality
#print axioms Trombo.Duality.descartes_deficit_table
#print axioms Trombo.Duality.deficit_general
#print axioms Trombo.Duality.hemi_four
#print axioms Trombo.Duality.klein_quartic_pair
#print axioms Trombo.Duality.goldberg_every_t
#print axioms Trombo.Duality.goldberg_table
#print axioms Trombo.Duality.cube_cross_reverse
#print axioms Trombo.Duality.even_code_dual
#print axioms Trombo.Duality.hamming_simplex_dual
#print axioms Trombo.Duality.fano_polarity
#print axioms Trombo.Duality.pythagorean_param
#print axioms Trombo.Duality.half_line_to_unit_circle
#print axioms Trombo.Duality.one_line_to_half_circle
#print axioms Trombo.Duality.li_map_sides
#print axioms Trombo.Duality.bracket_mobius
#print axioms Trombo.Duality.cross_ratio_mobius
#print axioms Trombo.Duality.harmonic_quadruple
#print axioms Trombo.Duality.midpoint_harmonic

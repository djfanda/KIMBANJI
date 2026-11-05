/-
모래시계 — 점 · 면 · 점 의 사슬, 코어의 태극 뫼비우스, 두 곳 스위치, 대각선 그림자
(린 4 커널 확인 · Mathlib 없이 · import 없이 · 린 코어만 · 정수만)

표시 : ■ 린 커널 확인 · △ 셈으로 범위를 정해 확인 · □ 열린 물음 · «해석» 그림 읽기 (판정 아님) · «전언» 남의 결과

[1] 모래시계와 쌍뿔 — 2 배 좌표 : 큐브 c 의 중심 2c · 축 위의 두 면 2c ± 1
  ■ 정육면체를 중심에서 사각뿔 여섯으로 나눔 : [−4, 4]³ 의 격자점 729 개가 모두 닫힌 사각뿔 하나 이상에 들고, 열린 사각뿔
    둘에 함께 드는 점은 없으며, 여섯은 부호 있는 좌표 치환으로 서로 합동 → 사각뿔 하나 = 정육면체의 1/6.
  ■ 계단 : 모든 n ≥ 1 에서 3·(0² + … + (n − 1)²) < n³ < 3·(1² + … + n²) · 모든 계단 사이에 끼이는 분수는 1/3 하나
    → 사각뿔 = 밑면 × 높이 / 3 (2 배 좌표에서 4 × 1 / 3 = 8 / 6) · 모래시계 (꼭짓점끼리 둘) = 쌍뿔 (밑면끼리 둘) = 정육면체의 1/3.
  ■ 사슬 c = 0 … 9 : 사각뿔 20 · 모래시계 10 (중심 2c 에서 꼭짓점끼리, 밑면은 두 면 2c ± 1) · 쌍뿔 9 (면 2c + 1 에서 밑면끼리,
    꼭짓점은 두 점 2c · 2c + 2) + 끝의 반쪽 2 · 이웃한 사각뿔은 꼭짓점과 밑면을 번갈아 나눔 ·
    고리 (c mod 10) 에서는 쌍뿔 10 이 모두 온전하고 사각뿔마다 모래시계 하나 · 쌍뿔 하나.
  «해석» 모래시계 = 송신 (점 하나 → 두 면) · 쌍뿔 = 수신 (면 → 이웃 점) · 이 번갈음이 부호 · 코어 = 가운데 점.
[2] 코어 F = [[0, 0, −1], [−1, 0, 0], [0, −1, 0]] — F(x, y, z) = (−z, −x, −y)
  ■ ±e_i 여섯의 고리 +x → −y → +z → −x → +y → −z → +x (부호 번갈아).
  ■ F² = 좌표 순환 (x, y, z) ↦ (y, z, x) (축 (1, 1, 1) 둘레 120°) · F³ = −I (점 대칭) · F⁶ = I · 차수 정확히 6.
  ■ det F = −1 · FᵀF = I · F(1, 1, 1) = −(1, 1, 1) · 모든 정수 a, b 에서 평면 x + y + z = 0 을 지키고 그 위에서 60° 회전
    → 회전반사 S6 (축 둘레 60° 돌리고 그 평면에 비춤).
  ■ 큐브 {0, 1}³ 위의 같은 대칭 σ(v) = 1 − (v₃, v₁, v₂) : 000 ↔ 111 · 가운데 여섯이 모서리를 따라 한 고리 · 그림자에서 σ = F.
  «해석» F² 의 세 갈래 120° = 삼태극 · F³ = −I = 모래시계 뒤집기 · 세 걸음 (반 바퀴) 마다 뒤집히는 여섯 고리 = 태극 뫼비우스.
[3] 뫼비우스 띠 — 팔면체 (꼭짓점 ±e_i · 면 8)
  ■ 팔면체 V 6 · E 12 · F 8 · χ 2 · 일관된 방향 2 / 256 · 옆 띠 (면 (+, +, +) · (−, −, −) 를 뺀 6) V 6 · E 12 · F 6 · χ 0 ·
    경계는 두 삼각형 (점 대칭이 맞바꿈) · 방향 2 / 64.
  ■ 코어 F 는 면 (+, +, +) ↔ (−, −, −) 를 맞바꾸고 옆 띠 여섯 면을 한 고리로 돌림 · F³ = 점 대칭 · 몫에서는 면 셋의 고리.
  ■ 띠 / 점 대칭 : V 3 · E 6 · F 3 · χ 0 · 경계 모서리 3 이 꼭짓점 셋을 한 바퀴 · 일관된 방향 0 / 8 → 뫼비우스 띠.
  ■ 팔면체 / 점 대칭 (반팔면체) : V 3 · E 6 · F 4 · χ 1 · 모서리마다 면 둘 · 방향 0 / 16 → 사영 평면.
  «전언» 곡면 분류 : 경계 하나 · χ 0 · 방향 없음 → 뫼비우스 띠 · 경계 없음 · χ 1 · 방향 없음 → 사영 평면.
[4] 두 곳 스위치와 가운데 등 — 3 로 스위치 A · B, 4 로 (교차) 스위치 X₁ … X_k
  ■ 등 켜짐 ⇔ (A xor X₁ xor … xor X_k) = B · 모든 k 에서 어느 스위치 하나를 바꾸어도 등이 바뀜 · 켜짐 ⇔ (A, X, B) 의 무게가 짝수.
  ■ 배선 그래프 (마디 9 + 4k) 의 너비 우선 탐색 : k = 0 … 3 의 모든 상태 60 에서 «L → … → 등 → N» 길 ⇔ 위 식 ·
    N 의 이웃은 등 하나 · 등을 빼면 L 과 N 은 끊김 (합선 없음).
  ■ 상태 2^(k + 2) 가운데 켜짐 2^(k + 1) (k ≤ 5).
  «해석» 4 로 스위치의 교차 = 두 전선의 반 비틀림 (뫼비우스) · 가운데 등 = 코어 · 스위치 하나 = 큐브 모서리 하나 건너기.
[5] 대각선 그림자 — v ∈ {0, 1}ⁿ, 무게 w, p(v) = n·v − w·(1, …, 1) (긴 대각선에 수직인 평면에 비춘 그림자의 n 배)
  ■ 모든 n · 모든 v : |p(v)|² = n·w·(n − w) · 보수의 그림자 = −p(v) → 코어 (0) 에 겹치는 것은 0…0 과 1…1 뿐.
  ■ n = 2 … 6 : 코어에 둘 · 무게별 개수 = 이항계수.
  ■ n = 3 : 무게 1 · 2 의 여섯이 같은 거리 · 이웃끼리 60° · 무게 번갈아 · 코어 F 의 여섯 고리를 비춘 것과 같음.
  ■ n = 4 (거리² 는 16 배 정수로) : 무게 1 · 3 의 여덟 = 모서리 1 인 정육면체 (거리² 1 이 12 · 2 가 12 · 3 이 4) ·
    무게 2 의 여섯 = 거리 1 의 돌기 · 돌기마다 이웃 모퉁이 넷이 정육면체의 면, 그 중심 거리 ½ · 돌기와 모퉁이 거리² 3/4 ·
    이웃한 돌기 둘과 공통 모퉁이 둘이 마름모 (12) 이고 모두 껍질의 면 · V 14 − E 24 + F 12 = 2 → 마름모 십이면체.
  ■ n = 5 : 거리² 4/5 인 점 10 · 6/5 인 점 20 · n = 6 : 5/6 이 12 · 4/3 이 30 · 3/2 가 20 (코어에 둘씩).
  «전언» 케플러 : 정육면체에 그 중심 사각뿔 여섯을 바깥으로 붙이면 마름모 십이면체 (부피는 정육면체의 2 배) ·
    4 차원 큐브를 꼭짓점 쪽에서 비춘 그림자가 마름모 십이면체라는 것은 알려진 사실.
  «해석» 3 차원 큐브의 그림자 = 육각형 · 4 차원 = 정육면체 + 돌기 여섯 (면 ½ · 끝 1) · 5 차원 = 두 껍질 위의 점 30.
[6] 페트리 다각형 — 0…0 → e₁ → e₁ + e₂ → … → 1…1 → 1…1 − e₁ → … → e_n → 0…0
  ■ n = 2 … 6 : 모서리를 따라 닫힌 2n 각형 · 꼭짓점 2n 개 모두 다름 · 잇단 모서리 n − 1 개는 늘 한 면 (facet) 에, n 개는 아님.
  ■ 그림자에서 코어를 두 번 (0…0 · 1…1) 지나고 뒤 절반은 앞 절반의 보수 = 점 대칭 — 코어에서 만나는 두 고리.
  «전언» n 차원 큐브의 페트리 다각형은 2n 각형 (콕서터 수 2n).
△ 셈으로 범위를 정한 것 : 켜짐 절반 k ≤ 5 · 배선 k ≤ 3 · 그림자 셈 n ≤ 6 · 페트리 n ≤ 6
  (모든 k · n 에 대한 린 문장은 노름 식 · 보수 · 짝홀 · 스위치 뒤집기 · 제곱합 · 계단 · 1/3).
□ n = 5, 6 그림자 껍질들의 볼록 껍질 면 구조 — 이 파일에서 판정하지 않음.

검증 : lean 모래시계.lean  (린 v4.34.0 · decide +kernel · omega · grind · induction · 끝의 #print axioms)
-/
namespace Trombo.Hourglass

/-! ## 0. 공통 — 정수 벡터 · 비트 · 무게 · 그림자 -/

def iabs (a : Int) : Int := if a < 0 then -a else a
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0
def vadd (a b : List Int) : List Int := List.zipWith (· + ·) a b
def vsub (a b : List Int) : List Int := List.zipWith (· - ·) a b
def vneg (a : List Int) : List Int := a.map (fun t => -t)
def dist2 (a b : List Int) : Int := dot (vsub a b) (vsub a b)
def dedup {α : Type} [BEq α] (l : List α) : List α := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
def bit (m i : Nat) : Bool := (m >>> i) % 2 == 1
def bits_of (n m : Nat) : List Bool := (List.range n).map (bit m)
def cube_pts (n : Nat) : List (List Bool) := (List.range (2 ^ n)).map (bits_of n)
def weight (v : List Bool) : Nat := v.countP id
def hamming (u v : List Bool) : Nat := (List.zipWith (fun a b => a != b) u v).countP id
/-- 대각선 그림자 (n 배) : p(v) = n·v − w·(1, …, 1) -/
def shadow (v : List Bool) : List Int := v.map (fun b => (v.length : Int) * (if b then 1 else 0) - (weight v : Int))
/-- 스위치 하나 뒤집기 = 큐브 모서리 하나 건너기 -/
def flip_at : Nat → List Bool → List Bool
  | _, [] => []
  | 0, x :: xs => (!x) :: xs
  | i + 1, x :: xs => x :: flip_at i xs
def cube_nbrs (v : List Bool) : List (List Bool) := (List.range v.length).map (fun i => flip_at i v)
def pairs (l : List (List Bool)) : List (List Bool × List Bool) :=
  (List.range l.length).flatMap fun i => ((List.range l.length).filter (i < ·)).map fun j => (l.getD i [], l.getD j [])
def euler (v e f : Nat) : Int := (v : Int) - e + f

/-! ## 1. 모래시계와 쌍뿔 -/

/-- 사각뿔 k (축 k / 2 · k 가 짝수면 + 쪽, 홀수면 − 쪽) 의 닫힌 몸 : 모든 좌표의 절댓값 ≤ 그 축 쪽 좌표 -/
def pyr_closed (k : Nat) (v : List Int) : Bool :=
  let t := if k % 2 == 0 then v.getD (k / 2) 0 else -(v.getD (k / 2) 0)
  v.all (fun x => decide (iabs x ≤ t))
/-- 열린 사각뿔 : 다른 두 좌표의 절댓값 < 그 축 쪽 좌표 -/
def pyr_open (k : Nat) (v : List Int) : Bool :=
  let t := if k % 2 == 0 then v.getD (k / 2) 0 else -(v.getD (k / 2) 0)
  (List.range 3).all (fun j => j == k / 2 || decide (iabs (v.getD j 0) < t))
def grid : List (List Int) :=
  (List.range 9).flatMap fun (a : Nat) => (List.range 9).flatMap fun (b : Nat) => (List.range 9).map fun (c : Nat) =>
    [(a : Int) - 4, (b : Int) - 4, (c : Int) - 4]
/-- + z 사각뿔을 사각뿔 k 로 옮기는 부호 있는 좌표 치환 -/
def to_axis (k : Nat) (v : List Int) : List Int :=
  let x := v.getD 0 0
  let y := v.getD 1 0
  let s := if k % 2 == 0 then v.getD 2 0 else -(v.getD 2 0)
  if k / 2 == 0 then [s, x, y] else if k / 2 == 1 then [x, s, y] else [x, y, s]

/-- 케플러의 나눔 : 격자점 729 개가 모두 닫힌 사각뿔에 들고, 열린 사각뿔 둘에 함께 드는 점은 없으며, 여섯 사각뿔은 서로 합동 -/
theorem kepler_six_pyramids :
    grid.length = 729 ∧
    grid.all (fun v => (List.range 6).any (fun k => pyr_closed k v)) = true ∧
    grid.all (fun v => decide ((List.range 6).countP (fun k => pyr_open k v) ≤ 1)) = true ∧
    (List.range 6).all (fun k => grid.all fun v =>
      pyr_closed k (to_axis k v) == pyr_closed 4 v && pyr_open k (to_axis k v) == pyr_open 4 v) = true := by
  decide +kernel

/-- 위 계단 : 1² + 2² + … + n² -/
def sq_upper : Nat → Nat
  | 0 => 0
  | n + 1 => sq_upper n + (n + 1) * (n + 1)
/-- 아래 계단 : 0² + 1² + … + (n − 1)² -/
def sq_lower : Nat → Nat
  | 0 => 0
  | n + 1 => sq_upper n

/-- 제곱의 합 : 모든 n 에서 6·(1² + … + n²) = n (n + 1) (2n + 1) -/
theorem sum_of_squares (n : Nat) : 6 * sq_upper n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sq_upper]; grind

/-- 사각뿔을 n 층으로 썬 두 계단 : 모든 n ≥ 1 에서 아래 계단 < n³ / 3 < 위 계단 -/
theorem pyramid_staircase (n : Nat) (hn : 1 ≤ n) : 3 * sq_lower n < n ^ 3 ∧ n ^ 3 < 3 * sq_upper n := by
  match n, hn with
  | m + 1, _ =>
    have h1 := sum_of_squares m
    have h2 := sum_of_squares (m + 1)
    simp only [sq_lower]
    constructor <;> grind

/-- 모든 n ≥ 1 의 두 계단 사이에 끼이는 분수 p / q 는 1/3 하나뿐 (n = 4q + 1 에서 갈림) -/
theorem one_third_unique (p q : Nat) (hq : 0 < q)
    (h : ∀ n, 1 ≤ n → q * sq_lower n ≤ p * n ^ 3 ∧ p * n ^ 3 ≤ q * sq_upper n) : 3 * p = q := by
  obtain ⟨h1, h2⟩ := h (4 * q + 1) (by omega)
  clear h
  have e1 := sum_of_squares (4 * q + 1)
  have e0 := sum_of_squares (4 * q)
  simp only [sq_lower] at h1
  generalize hU0 : sq_upper (4 * q) = U0 at h1 e0
  generalize hU1 : sq_upper (4 * q + 1) = U1 at h2 e1
  generalize hN : (4 * q + 1) ^ 3 = N at h1 h2
  rcases Nat.lt_trichotomy (3 * p) q with hlt | heq | hgt
  · exfalso
    have hm : (3 * p + 1) * N ≤ q * N := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hm
    have h6 : 6 * (q * U0) ≤ 6 * (p * N) := Nat.mul_le_mul_left 6 h1
    have k1 : 6 * (q * U0) = q * (4 * q * (4 * q + 1) * (2 * (4 * q) + 1)) := by
      rw [← e0, ← Nat.mul_assoc, Nat.mul_comm 6 q, Nat.mul_assoc]
    have key : q * (4 * q * (4 * q + 1) * (2 * (4 * q) + 1)) + 2 * N ≤ 2 * (q * N) := by omega
    rw [← hN] at key
    grind
  · exact heq
  · exfalso
    have hm : (q + 1) * N ≤ 3 * p * N := Nat.mul_le_mul_right _ hgt
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hm
    have h6 : 6 * (p * N) ≤ 6 * (q * U1) := Nat.mul_le_mul_left 6 h2
    have k1 : 6 * (q * U1) = q * ((4 * q + 1) * (4 * q + 1 + 1) * (2 * (4 * q + 1) + 1)) := by
      rw [← e1, ← Nat.mul_assoc, Nat.mul_comm 6 q, Nat.mul_assoc]
    have key : 2 * (q * N) + 2 * N ≤ q * ((4 * q + 1) * (4 * q + 1 + 1) * (2 * (4 * q + 1) + 1)) := by omega
    rw [← hN] at key
    grind

/-- 축 위의 사각뿔 (c, s) : 꼭짓점 = 중심 2c · 밑면 = 2c + 1 (s = true) 또는 2c − 1 (s = false) -/
def chain_pyrs : List (Int × Bool) := (List.range 10).flatMap fun (c : Nat) => [((c : Int), false), ((c : Int), true)]
def apex (p : Int × Bool) : Int := 2 * p.1
def base (p : Int × Bool) : Int := if p.2 then 2 * p.1 + 1 else 2 * p.1 - 1
def hourglass (c : Int) : List (Int × Bool) := chain_pyrs.filter (fun p => apex p == 2 * c)
def bipyramid (f : Int) : List (Int × Bool) := chain_pyrs.filter (fun p => base p == f)
def line_faces : List Int := (List.range 11).map fun (j : Nat) => 2 * (j : Int) - 1

/-- 사슬 c = 0 … 9 : 모래시계 10 (꼭짓점끼리 · 두 면으로) · 쌍뿔 9 (밑면끼리 · 두 점으로) + 끝 반쪽 2 · 사각뿔마다 하나씩 · 꼭짓점과 밑면이 번갈아 -/
theorem hourglass_chain :
    chain_pyrs.length = 20 ∧
    (List.range 10).all (fun (c : Nat) => hourglass (c : Int) == [((c : Int), false), ((c : Int), true)] &&
      (hourglass (c : Int)).map base == [2 * (c : Int) - 1, 2 * (c : Int) + 1]) = true ∧
    (List.range 9).all (fun (c : Nat) => bipyramid (2 * (c : Int) + 1) == [((c : Int), true), ((c : Int) + 1, false)] &&
      (bipyramid (2 * (c : Int) + 1)).map apex == [2 * (c : Int), 2 * (c : Int) + 2]) = true ∧
    bipyramid (-1) = [(0, false)] ∧ bipyramid 19 = [(9, true)] ∧
    chain_pyrs.all (fun p => (List.range 10).countP (fun (c : Nat) => (hourglass (c : Int)).contains p) == 1 &&
      line_faces.countP (fun f => (bipyramid f).contains p) == 1) = true ∧
    (List.range 19).all (fun j =>
      let a := chain_pyrs.getD j (0, false)
      let b := chain_pyrs.getD (j + 1) (0, false)
      if j % 2 == 0 then apex a == apex b && base a != base b else base a == base b && apex a != apex b) = true := by
  decide +kernel

/-- 고리 (면 번호 mod 20) 의 쌍뿔 -/
def ring_bipyramid (f : Int) : List (Int × Bool) := chain_pyrs.filter (fun p => base p % 20 == f)

/-- 고리 c mod 10 : 쌍뿔 10 개가 모두 온전 (사각뿔 둘 · + 와 − 하나씩) · 사각뿔마다 모래시계 하나 · 쌍뿔 하나 -/
theorem hourglass_ring :
    (List.range 10).all (fun (c : Nat) => (ring_bipyramid (2 * (c : Int) + 1)).length == 2 &&
      (ring_bipyramid (2 * (c : Int) + 1)).countP (fun p => p.2) == 1) = true ∧
    chain_pyrs.all (fun p => (List.range 10).countP (fun (c : Nat) => (hourglass (c : Int)).contains p) == 1 &&
      (List.range 10).countP (fun (c : Nat) => (ring_bipyramid (2 * (c : Int) + 1)).contains p) == 1) = true := by
  decide +kernel

/-! ## 2. 코어의 태극 뫼비우스 -/

def core_mat : List (List Int) := [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]
def id3 : List (List Int) := [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
def mat_vec (m : List (List Int)) (v : List Int) : List Int := m.map (fun row => dot row v)
def transpose3 (m : List (List Int)) : List (List Int) := (List.range 3).map fun j => m.map (fun row => row.getD j 0)
def mat_mul (a b : List (List Int)) : List (List Int) := a.map fun row => (transpose3 b).map fun col => dot row col
def mat_pow (m : List (List Int)) : Nat → List (List Int)
  | 0 => id3
  | k + 1 => mat_mul m (mat_pow m k)
def det3 (m : List (List Int)) : Int :=
  let e := fun i j => (m.getD i []).getD j 0
  e 0 0 * (e 1 1 * e 2 2 - e 1 2 * e 2 1) - e 0 1 * (e 1 0 * e 2 2 - e 1 2 * e 2 0) +
    e 0 2 * (e 1 0 * e 2 1 - e 1 1 * e 2 0)
def six_ring : List (List Int) := [[1, 0, 0], [0, -1, 0], [0, 0, 1], [-1, 0, 0], [0, 1, 0], [0, 0, -1]]

/-- 여섯 고리 : F 가 +x → −y → +z → −x → +y → −z → +x 로 돌리고, 부호가 번갈아, ±e_i 여섯을 모두 지남 -/
theorem core_six_ring :
    (List.range 6).all (fun k => mat_vec core_mat (six_ring.getD k []) == six_ring.getD ((k + 1) % 6) []) = true ∧
    six_ring.map (fun v => v.foldl (· + ·) 0) = [1, -1, 1, -1, 1, -1] ∧
    (dedup six_ring).length = 6 ∧ six_ring.all (fun v => dot v v == 1) = true := by
  decide +kernel

/-- 차수 6 : F² = 좌표 순환 (120°) · F³ = −I (점 대칭) · F⁶ = I · F¹ … F⁵ ≠ I -/
theorem core_order_six :
    mat_pow core_mat 2 = [[0, 1, 0], [0, 0, 1], [1, 0, 0]] ∧
    mat_pow core_mat 3 = [[-1, 0, 0], [0, -1, 0], [0, 0, -1]] ∧
    mat_pow core_mat 6 = id3 ∧
    [1, 2, 3, 4, 5].all (fun k => mat_pow core_mat k != id3) = true := by
  decide +kernel

/-- 회전반사 : det F = −1 · FᵀF = I · F(1, 1, 1) = −(1, 1, 1) · F² 는 축 (1, 1, 1) 을 지키는 회전 (det 1) -/
theorem core_rotoreflection :
    det3 core_mat = -1 ∧ mat_mul (transpose3 core_mat) core_mat = id3 ∧
    mat_vec core_mat [1, 1, 1] = [-1, -1, -1] ∧
    det3 (mat_pow core_mat 2) = 1 ∧ mat_vec (mat_pow core_mat 2) [1, 1, 1] = [1, 1, 1] := by
  decide +kernel

/-- 모든 정수 a, b : v = (a, b, −a − b) 에서 F v 도 평면 x + y + z = 0 위 · |F v| = |v| · 2⟨F v, v⟩ = |v|² (60°) -/
theorem core_plane_sixty (a b : Int) :
    (mat_vec core_mat [a, b, -a - b]).foldl (· + ·) 0 = 0 ∧
    dot (mat_vec core_mat [a, b, -a - b]) (mat_vec core_mat [a, b, -a - b]) = dot [a, b, -a - b] [a, b, -a - b] ∧
    2 * dot (mat_vec core_mat [a, b, -a - b]) [a, b, -a - b] = dot [a, b, -a - b] [a, b, -a - b] := by
  simp only [mat_vec, core_mat, dot, List.map, List.foldl]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- 큐브 {0, 1}³ 위의 코어 σ(v) = 1 − (v₃, v₁, v₂) -/
def sigma3 (v : List Bool) : List Bool := [!(v.getD 2 false), !(v.getD 0 false), !(v.getD 1 false)]
def sigma_pow : Nat → List Bool → List Bool
  | 0, v => v
  | k + 1, v => sigma3 (sigma_pow k v)

/-- 큐브 위의 코어 : 그림자에서 σ = F · σ³ = 보수 · σ⁶ = 항등 · 000 ↔ 111 · 가운데 여섯이 모서리를 따라 한 고리 -/
theorem core_on_cube :
    (cube_pts 3).all (fun v => shadow (sigma3 v) == mat_vec core_mat (shadow v)) = true ∧
    (cube_pts 3).all (fun v => sigma_pow 3 v == v.map (!·) && sigma_pow 6 v == v) = true ∧
    sigma3 [false, false, false] = [true, true, true] ∧ sigma3 [true, true, true] = [false, false, false] ∧
    (List.range 6).map (fun k => sigma_pow k [true, false, false]) =
      [[true, false, false], [true, false, true], [false, false, true],
       [false, true, true], [false, true, false], [true, true, false]] ∧
    (List.range 6).all (fun k =>
      hamming (sigma_pow k [true, false, false]) (sigma_pow (k + 1) [true, false, false]) == 1) = true := by
  decide +kernel

/-! ## 3. 뫼비우스 띠 — 팔면체의 옆 띠를 점 대칭으로 접기 -/

/-- 팔면체 : 꼭짓점 번호 2i + s (축 i · s = 0 이면 +e_i, 1 이면 −e_i) · 면 f ∈ 0 … 7 의 비트 i = 축 i 의 부호 -/
def face_verts (f : Nat) : List Nat := [f % 2, 2 + f / 2 % 2, 4 + f / 4 % 2]
def ecode (a b : Nat) : Nat := 6 * a + b
/-- 면의 모서리 (번호, 고리 0 → 1 → 2 → 0 에서 작은 번호 → 큰 번호 와 거꾸로인가) -/
def face_edges (f : Nat) : List (Nat × Bool) :=
  let v := face_verts f
  [(ecode (v.getD 0 0) (v.getD 1 0), false), (ecode (v.getD 1 0) (v.getD 2 0), false),
   (ecode (v.getD 0 0) (v.getD 2 0), true)]
def anti_e (e : Nat) : Nat := ecode (e / 6 ^^^ 1) (e % 6 ^^^ 1)
def q_v (v : Nat) : Nat := min v (v ^^^ 1)
def q_e (e : Nat) : Nat := min e (anti_e e)
def q_f (f : Nat) : Nat := min f (7 - f)
def octa : List Nat := List.range 8
def band : List Nat := [1, 2, 3, 4, 5, 6]
def verts_of (fs : List Nat) : List Nat := dedup (fs.flatMap face_verts)

/-- 복합체 = 면마다 (모서리 번호, 거꾸로) 목록 -/
def cx_of (fs : List Nat) : List (List (Nat × Bool)) := fs.map face_edges
/-- 점 대칭 (v ↦ −v) 으로 접은 몫 : 궤도마다 작은 번호 하나 -/
def cx_quot (fs : List Nat) : List (List (Nat × Bool)) := (dedup (fs.map q_f)).map fun f => (face_edges f).map fun (e, r) => (q_e e, r)
def cx_edges (c : List (List (Nat × Bool))) : List Nat := dedup (c.flatMap (fun f => f.map Prod.fst))
def edge_deg (c : List (List (Nat × Bool))) (e : Nat) : Nat := c.countP (fun f => f.any (fun er => er.1 == e))
def boundary (c : List (List (Nat × Bool))) : List Nat := (cx_edges c).filter (fun e => edge_deg c e == 1)
/-- 방향 m (면 j 의 방향 = 비트 j) 이 일관됨 : 함께 쓰는 모서리마다 두 면이 반대로 지남 -/
def consistent (c : List (List (Nat × Bool))) (m : Nat) : Bool :=
  (List.range c.length).all fun j => (List.range c.length).all fun k =>
    decide (k ≤ j) || (c.getD j []).all fun er => (c.getD k []).all fun er' =>
      er.1 != er'.1 || ((bit m j ^^ er.2) != (bit m k ^^ er'.2))
def orientations (c : List (List (Nat × Bool))) : Nat := (List.range (2 ^ c.length)).countP (consistent c)

/-- 팔면체 V 6 · E 12 · F 8 · χ 2 · 방향 2 · 옆 띠 V 6 · E 12 · F 6 · χ 0 · 경계 = 두 삼각형 (점 대칭이 맞바꿈) · 방향 2 -/
theorem octahedron_band :
    euler (verts_of octa).length (cx_edges (cx_of octa)).length octa.length = 2 ∧
    (cx_edges (cx_of octa)).length = 12 ∧ orientations (cx_of octa) = 2 ∧
    (verts_of band).length = 6 ∧ (cx_edges (cx_of band)).length = 12 ∧
    euler (verts_of band).length (cx_edges (cx_of band)).length band.length = 0 ∧
    (boundary (cx_of band)).length = 6 ∧
    (boundary (cx_of band)).all (fun e =>
      ((face_edges 0).map Prod.fst).contains e || ((face_edges 7).map Prod.fst).contains e) = true ∧
    (face_edges 0).map (fun er => anti_e er.1) = (face_edges 7).map Prod.fst ∧
    orientations (cx_of band) = 2 := by
  decide +kernel

/-- 꼭짓점 번호 → 벡터 ±e_i -/
def vert_vec (v : Nat) : List Int := (List.range 3).map fun i => if i == v / 2 then (if v % 2 == 0 then 1 else -1) else 0
/-- 코어 F 가 면에 하는 일 : 축 i 의 부호 s ↦ 축 i + 1 의 부호 −s -/
def core_face (f : Nat) : Nat := (1 - f / 4 % 2) + 2 * (1 - f % 2) + 4 * (1 - f / 2 % 2)
def core_face_pow : Nat → Nat → Nat
  | 0, f => f
  | k + 1, f => core_face (core_face_pow k f)

/-- 코어 F 가 팔면체의 면을 돌림 : (+, +, +) ↔ (−, −, −) · 옆 띠 여섯 면이 한 고리 · F³ = 점 대칭 · 몫 (뫼비우스) 에서는 면 셋의 고리 -/
theorem core_turns_band :
    core_face 0 = 7 ∧ core_face 7 = 0 ∧
    octa.all (fun f => (face_verts f).all fun u =>
      ((face_verts (core_face f)).map vert_vec).contains (mat_vec core_mat (vert_vec u))) = true ∧
    band.all (fun f => ((List.range 6).map fun k => core_face_pow k 1).contains f) = true ∧
    octa.all (fun f => core_face_pow 3 f == 7 - f && core_face_pow 6 f == f) = true ∧
    (dedup ((List.range 3).map fun k => q_f (core_face_pow k 1))).length = 3 := by
  decide +kernel

/-- 뫼비우스 띠 : 띠 / 점 대칭 은 V 3 · E 6 · F 3 · χ 0 · 경계 모서리 3 이 꼭짓점 셋을 한 바퀴 · 방향 8 가지 모두 어긋남 -/
theorem mobius_band :
    (cx_quot band).length = 3 ∧ (dedup ((verts_of band).map q_v)).length = 3 ∧
    (cx_edges (cx_quot band)).length = 6 ∧
    euler (dedup ((verts_of band).map q_v)).length (cx_edges (cx_quot band)).length (cx_quot band).length = 0 ∧
    (boundary (cx_quot band)).length = 3 ∧
    [0, 2, 4].all (fun x => ((boundary (cx_quot band)).countP fun e => q_v (e / 6) == x || q_v (e % 6) == x) == 2) = true ∧
    (dedup ((boundary (cx_quot band)).map fun e => (q_v (e / 6), q_v (e % 6)))).length = 3 ∧
    (cx_edges (cx_quot band)).all (fun e => decide (edge_deg (cx_quot band) e ≤ 2)) = true ∧
    orientations (cx_quot band) = 0 := by
  decide +kernel

/-- 반팔면체 (사영 평면) : 팔면체 / 점 대칭 은 V 3 · E 6 · F 4 · χ 1 · 모서리마다 면 둘 · 방향 16 가지 모두 어긋남 -/
theorem hemi_octahedron :
    (cx_quot octa).length = 4 ∧ (dedup ((verts_of octa).map q_v)).length = 3 ∧
    (cx_edges (cx_quot octa)).length = 6 ∧
    euler (dedup ((verts_of octa).map q_v)).length (cx_edges (cx_quot octa)).length (cx_quot octa).length = 1 ∧
    (cx_edges (cx_quot octa)).all (fun e => edge_deg (cx_quot octa) e == 2) = true ∧
    orientations (cx_quot octa) = 0 := by
  decide +kernel

/-! ## 4. 두 곳 스위치와 가운데 등 -/

/-- 짝홀 : X₁ xor … xor X_k -/
def par : List Bool → Bool
  | [] => false
  | x :: xs => x ^^ par xs
/-- 등 켜짐 ⇔ (A xor X₁ xor … xor X_k) = B -/
def lamp (a : Bool) (xs : List Bool) (b : Bool) : Bool := (a ^^ par xs) == b

/-- 모든 길이 · 모든 자리 i : 스위치 X_i 하나를 바꾸면 짝홀이 바뀜 -/
theorem parity_flip (xs : List Bool) (i : Nat) (h : i < xs.length) : par (flip_at i xs) = !par xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => cases x <;> simp [flip_at, par]
    | succ i =>
      simp only [flip_at, par]
      rw [ih i (by simp at h; omega)]
      cases x <;> simp

/-- 모든 k : A 를 바꾸든 B 를 바꾸든 X_i 하나를 바꾸든 등이 바뀐다 -/
theorem switch_toggles (a : Bool) (xs : List Bool) (b : Bool) :
    lamp (!a) xs b = !lamp a xs b ∧ lamp a xs (!b) = !lamp a xs b ∧
    ∀ i, i < xs.length → lamp a (flip_at i xs) b = !lamp a xs b := by
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simp only [lamp]; generalize par xs = t; cases a <;> cases b <;> cases t <;> rfl
  · simp only [lamp]; generalize par xs = t; cases a <;> cases b <;> cases t <;> rfl
  · simp only [lamp]; rw [parity_flip xs i hi]; generalize par xs = t; cases a <;> cases b <;> cases t <;> rfl

/-- 모든 k : 등 켜짐 ⇔ (A, X₁, …, X_k, B) 의 짝홀이 짝 · 짝홀 = 무게 mod 2 -/
theorem on_even_weight (a : Bool) (xs : List Bool) (b : Bool) :
    lamp a xs b = !par (a :: xs ++ [b]) ∧ ∀ l : List Bool, par l = (weight l % 2 == 1) := by
  constructor
  · have hcat : ∀ l : List Bool, par (l ++ [b]) = (par l ^^ b) := by
      intro l
      induction l with
      | nil => cases b <;> rfl
      | cons x l ih => simp only [List.cons_append, par, ih]; cases x <;> cases b <;> simp
    simp only [lamp, List.cons_append, par, hcat]
    generalize par xs = t
    cases a <;> cases b <;> cases t <;> rfl
  · intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [par, weight, List.countP_cons] at ih ⊢
      rw [ih]
      rcases Nat.mod_two_eq_zero_or_one (List.countP id l) with h | h <;> cases x <;> simp [h, Nat.add_mod]

def all_lists : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (all_lists k).flatMap fun l => [false :: l, true :: l]
def states (k : Nat) : List (Bool × List Bool × Bool) :=
  [false, true].flatMap fun a => (all_lists k).flatMap fun xs => [(a, xs, false), (a, xs, true)]

/-- k = 0 … 5 : 상태 2^(k + 2) 가운데 등 켜짐은 정확히 절반 -/
theorem half_on : (List.range 6).all (fun k => (states k).length == 2 ^ (k + 2) &&
    (states k).countP (fun s => lamp s.1 s.2.1 s.2.2) == 2 ^ (k + 1)) = true := by
  decide +kernel

/-- 배선 : L 0 · A 공통 1 · A.0 2 · A.1 3 · X_i 의 들 0 · 들 1 · 날 0 · 날 1 = 4 + 4i + 0 … 3 · B.0 · B.1 · B 공통 · 등 · N -/
def chain_wires : List Bool → Nat → Nat × Nat → List (Nat × Nat) × (Nat × Nat)
  | [], _, last => ([], last)
  | x :: xs, i, (p0, p1) =>
    let n0 := 4 + 4 * i
    let here := [(p0, n0), (p1, n0 + 1)] ++
      (if x then [(n0, n0 + 3), (n0 + 1, n0 + 2)] else [(n0, n0 + 2), (n0 + 1, n0 + 3)])
    let rest := chain_wires xs (i + 1) (n0 + 2, n0 + 3)
    (here ++ rest.1, rest.2)
def wires (a : Bool) (xs : List Bool) (b : Bool) : List (Nat × Nat) :=
  let c := chain_wires xs 0 (2, 3)
  let b0 := 4 + 4 * xs.length
  [(0, 1), (1, if a then 3 else 2)] ++ c.1 ++
    [(c.2.1, b0), (c.2.2, b0 + 1), (if b then b0 + 1 else b0, b0 + 2), (b0 + 2, b0 + 3), (b0 + 3, b0 + 4)]
def nbrs (es : List (Nat × Nat)) (v : Nat) : List Nat :=
  es.filterMap fun e => if e.1 == v then some e.2 else if e.2 == v then some e.1 else none
/-- 너비 우선 탐색 : 대기열 · 본 마디 · 연료 -/
def bfs (es : List (Nat × Nat)) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | f + 1, v :: queue, seen =>
    let new := (nbrs es v).foldl (fun acc u => if seen.contains u || acc.contains u then acc else acc ++ [u]) []
    bfs es f (queue ++ new) (seen ++ new)
def reach (es : List (Nat × Nat)) (n : Nat) : List Nat := bfs es (2 * n) [0] [0]
def lit_by_wires (a : Bool) (xs : List Bool) (b : Bool) : Bool :=
  (reach (wires a xs b) (9 + 4 * xs.length)).contains (8 + 4 * xs.length)

/-- 배선 그래프 (k = 0 … 3 · 모든 상태 60) : L 에서 N 까지 길 ⇔ 등 식 · N 의 이웃은 등 하나 · 등을 빼면 L 과 N 은 끊김 -/
theorem wiring_bfs : (List.range 4).all (fun k => (states k).all fun s =>
    let es := wires s.1 s.2.1 s.2.2
    lit_by_wires s.1 s.2.1 s.2.2 == lamp s.1 s.2.1 s.2.2 &&
    nbrs es (8 + 4 * k) == [7 + 4 * k] &&
    !(reach (es.filter fun e => e.1 != 7 + 4 * k && e.2 != 7 + 4 * k) (9 + 4 * k)).contains (8 + 4 * k)) = true := by
  decide +kernel

/-! ## 5. 대각선 그림자 -/

/-- 일반 꼴 : 모든 정수 N, W 와 모든 0/1 목록에서 Σ (N·vᵢ − W)² = N²·w − 2NW·w + 길이·W² -/
theorem square_sum_formula (N W : Int) (l : List Bool) :
    dot (l.map fun b => N * (if b then 1 else 0) - W) (l.map fun b => N * (if b then 1 else 0) - W) =
      N * N * (weight l : Int) - 2 * N * W * (weight l : Int) + (l.length : Int) * W * W := by
  induction l with
  | nil => simp [dot, weight]
  | cons b l ih =>
    simp only [List.map, dot, ih, weight, List.countP_cons, List.length_cons]
    cases b <;> simp <;> grind

/-- 모든 n · 모든 v ∈ {0, 1}ⁿ : |p(v)|² = n·w·(n − w) · 보수의 그림자 = −p(v) -/
theorem shadow_norm_all (v : List Bool) :
    dot (shadow v) (shadow v) = (v.length : Int) * (weight v : Int) * ((v.length : Int) - (weight v : Int)) ∧
    shadow (v.map (!·)) = vneg (shadow v) := by
  have hw : ∀ l : List Bool, weight (l.map (!·)) + weight l = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [weight] at ih ⊢
      rw [List.map_cons, List.countP_cons, List.countP_cons, List.length_cons]
      generalize List.countP id (List.map (!·) l) = c at ih ⊢
      generalize List.countP id l = w at ih ⊢
      cases x <;> simp <;> omega
  constructor
  · simp only [shadow]
    rw [square_sum_formula]
    grind
  · have h1 := hw v
    simp only [shadow, vneg, List.map_map, List.length_map]
    apply List.map_congr_left
    intro b _
    cases b <;> simp <;> omega

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- n = 2 … 6 : 그림자가 코어 (0) 인 꼭짓점은 0…0 과 1…1 뿐 · 무게 w 인 꼭짓점 수 = 이항계수 C(n, w) -/
theorem shadow_core_binomial : [2, 3, 4, 5, 6].all (fun n =>
    (cube_pts n).all (fun v => (dot (shadow v) (shadow v) == 0) == (weight v == 0 || weight v == n)) &&
    (List.range (n + 1)).all (fun w => (cube_pts n).countP (fun v => weight v == w) == choose n w)) = true := by
  decide +kernel

def hex3 : List (List Bool) := (List.range 6).map fun k => sigma_pow k [true, false, false]

/-- n = 3 : 무게 1 · 2 의 여섯 = 같은 거리 (|p|² 6) · 이웃끼리 60° (2⟨p, p'⟩ = 6) · 무게 번갈아 · 코어 고리 ±e_i 의 그림자 -/
theorem shadow_hexagon :
    hex3.map weight = [1, 2, 1, 2, 1, 2] ∧
    hex3.all (fun v => dot (shadow v) (shadow v) == 6) = true ∧
    (List.range 6).all (fun k => 2 * dot (shadow (hex3.getD k [])) (shadow (hex3.getD ((k + 1) % 6) [])) == 6) = true ∧
    (List.range 6).all (fun k => shadow (hex3.getD k []) ==
      vsub ((six_ring.getD k []).map (3 * ·)) (List.replicate 3 ((six_ring.getD k []).foldl (· + ·) 0))) = true ∧
    (cube_pts 3).all (fun v => (weight v == 1 || weight v == 2) == hex3.contains v) = true := by
  decide +kernel

def corners4 : List (List Bool) := (cube_pts 4).filter fun v => weight v == 1 || weight v == 3
def tips4 : List (List Bool) := (cube_pts 4).filter fun v => weight v == 2

/-- n = 4 (16 배) : 무게 1 · 3 의 여덟 = 모서리 1 인 정육면체 (거리² 1 · 2 · 3 이 12 · 12 · 4) · 돌기 여섯 거리 1 · 돌기마다 정사각형 면 (중심 ½) · 돌기–모퉁이 거리² 3/4 -/
theorem shadow_four_cube :
    corners4.length = 8 ∧ corners4.all (fun v => dot (shadow v) (shadow v) == 12) = true ∧
    (pairs corners4).countP (fun uv => dist2 (shadow uv.1) (shadow uv.2) == 16) = 12 ∧
    (pairs corners4).countP (fun uv => dist2 (shadow uv.1) (shadow uv.2) == 32) = 12 ∧
    (pairs corners4).countP (fun uv => dist2 (shadow uv.1) (shadow uv.2) == 48) = 4 ∧
    corners4.all (fun u => corners4.countP (fun v => dist2 (shadow u) (shadow v) == 16) == 3) = true ∧
    tips4.length = 6 ∧ tips4.all (fun t => dot (shadow t) (shadow t) == 16) = true ∧
    corners4.all (fun u => tips4.countP (fun t => (cube_nbrs t).contains u) == 3) = true ∧
    tips4.all (fun t =>
      let s := (cube_nbrs t).foldl (fun s u => vadd s (shadow u)) [0, 0, 0, 0]
      (cube_nbrs t).all (fun u => corners4.contains u) &&
      s == (shadow t).map (2 * ·) && dot s s == 64 &&
      (cube_nbrs t).all (fun u => dist2 (shadow t) (shadow u) == 12) &&
      (pairs (cube_nbrs t)).countP (fun uv => dist2 (shadow uv.1) (shadow uv.2) == 16) == 4 &&
      (pairs (cube_nbrs t)).countP (fun uv => dist2 (shadow uv.1) (shadow uv.2) == 32) == 2) = true := by
  decide +kernel

def tip_pairs : List (List Bool × List Bool) :=
  (pairs tips4).filter fun tt => dist2 (shadow tt.1) (shadow tt.2) == 32
def common_corners (tt : List Bool × List Bool) : List (List Bool) :=
  (cube_nbrs tt.1).filter fun u => (cube_nbrs tt.2).contains u

/-- n = 4 : 이웃한 돌기 둘 + 공통 모퉁이 둘 = 마름모 12 (대각 1 · √2) · 모두 껍질의 면 (16 점이 한쪽 · 같음은 넷) · V 14 − E 24 + F 12 = 2 -/
theorem shadow_four_rhombic :
    tip_pairs.length = 12 ∧
    tip_pairs.all (fun tt =>
      let cs := common_corners tt
      let m := vadd (shadow tt.1) (shadow tt.2)
      cs.length == 2 &&
      m == vadd (shadow (cs.getD 0 [])) (shadow (cs.getD 1 [])) &&
      dist2 (shadow (cs.getD 0 [])) (shadow (cs.getD 1 [])) == 16 &&
      (cube_pts 4).all (fun x => decide (dot (shadow x) m ≤ dot (shadow tt.1) m)) &&
      (cube_pts 4).countP (fun x => dot (shadow x) m == dot (shadow tt.1) m) == 4) = true ∧
    euler (corners4.length + tips4.length) (tips4.flatMap cube_nbrs).length tip_pairs.length = 2 := by
  decide +kernel

/-- n = 5 (25 배) : 거리² 4/5 인 점 10 · 6/5 인 점 20 · 코어 2 · n = 6 (36 배) : 5/6 이 12 · 4/3 이 30 · 3/2 가 20 · 코어 2 -/
theorem shadow_five_six :
    (cube_pts 5).countP (fun v => dot (shadow v) (shadow v) == 0) = 2 ∧
    (cube_pts 5).countP (fun v => dot (shadow v) (shadow v) == 20) = 10 ∧
    (cube_pts 5).countP (fun v => dot (shadow v) (shadow v) == 30) = 20 ∧
    (cube_pts 6).countP (fun v => dot (shadow v) (shadow v) == 0) = 2 ∧
    (cube_pts 6).countP (fun v => dot (shadow v) (shadow v) == 30) = 12 ∧
    (cube_pts 6).countP (fun v => dot (shadow v) (shadow v) == 48) = 30 ∧
    (cube_pts 6).countP (fun v => dot (shadow v) (shadow v) == 54) = 20 := by
  decide +kernel

/-! ## 6. 페트리 다각형 -/

/-- k 번째 꼭짓점 : k ≤ n 이면 앞 k 자리가 1 · k > n 이면 앞 k − n 자리가 0 이고 나머지 1 -/
def petrie (n k : Nat) : List Bool := (List.range n).map fun i => if k ≤ n then decide (i < k) else decide (k - n ≤ i)
def common_coord (n : Nat) (vs : List (List Bool)) : Bool :=
  (List.range n).any fun i => vs.all fun v => v.getD i false == (vs.headD []).getD i false
def window (n k len : Nat) : List (List Bool) := (List.range len).map fun j => petrie n ((k + j) % (2 * n))

/-- n = 2 … 6 : 모서리를 따라 닫힌 2n 각형 · 꼭짓점 2n 개 모두 다름 · 잇단 모서리 n − 1 개는 한 면에, n 개는 아님 -/
theorem petrie_polygon : [2, 3, 4, 5, 6].all (fun n =>
    (List.range (2 * n)).all (fun k => hamming (petrie n k) (petrie n ((k + 1) % (2 * n))) == 1) &&
    (dedup ((List.range (2 * n)).map (petrie n))).length == 2 * n &&
    (List.range (2 * n)).all (fun k => common_coord n (window n k n) && !common_coord n (window n k (n + 1)))) = true := by
  decide +kernel

/-- n = 2 … 6 : 페트리 고리의 그림자는 코어를 두 번 (0…0 · 1…1) 지나고, 뒤 절반 = 앞 절반의 보수 = 점 대칭 -/
theorem petrie_shadow_hourglass : [2, 3, 4, 5, 6].all (fun n =>
    shadow (petrie n 0) == List.replicate n 0 && shadow (petrie n n) == List.replicate n 0 &&
    (List.range n).all (fun k => petrie n (k + n) == (petrie n k).map (!·) &&
      shadow (petrie n (k + n)) == vneg (shadow (petrie n k))) &&
    (List.range (2 * n)).all (fun k => k == 0 || k == n || dot (shadow (petrie n k)) (shadow (petrie n k)) != 0)) = true := by
  decide +kernel

#print axioms kepler_six_pyramids
#print axioms sum_of_squares
#print axioms pyramid_staircase
#print axioms one_third_unique
#print axioms hourglass_chain
#print axioms hourglass_ring
#print axioms core_six_ring
#print axioms core_order_six
#print axioms core_rotoreflection
#print axioms core_plane_sixty
#print axioms core_on_cube
#print axioms octahedron_band
#print axioms core_turns_band
#print axioms mobius_band
#print axioms hemi_octahedron
#print axioms parity_flip
#print axioms switch_toggles
#print axioms on_even_weight
#print axioms half_on
#print axioms wiring_bfs
#print axioms square_sum_formula
#print axioms shadow_norm_all
#print axioms shadow_core_binomial
#print axioms shadow_hexagon
#print axioms shadow_four_cube
#print axioms shadow_four_rhombic
#print axioms shadow_five_six
#print axioms petrie_polygon
#print axioms petrie_shadow_hourglass

end Trombo.Hourglass

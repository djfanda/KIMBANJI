/-
태극 아리랑 — 린 4 커널 확인 (Mathlib 없이, 린 코어만)

· 다섯 태극의 점과 상자 : q = 2, 3, 4, 5 의 모든 바이어슈트라스 식 y² + a1·xy + a3·y = x³ + a2·x² + a4·x + a6 (q⁵ 개)에서
  흠(특이점 · F = F_x = F_y = 0 인 점) 있는 식은 정확히 q⁴ 개이고, 매끈한 곡선의 대각합 a = q + 1 − N 은 모두 정해진 목록 안에
  있으며 그 목록의 모든 a 가 a² ≤ 4q 를 만족한다 — 두 영점이 Re s = ½ 위 (상자 안 = 1). 목록의 a 마다 증인 곡선이 있다.
  q = 4 는 F₄ = {0, 1, ω, ω + 1} 의 곱셈표 (ω² = ω + 1). q = 7 은 태극아리랑_칠.lean (49 조각).
· 각도로 맞춘 합집합과 교집합 : a / 2√q 가 같음 ⇔ a² q' = a'² q 이고 부호가 같음 — 합집합 37 · 교집합은 a = 0 하나 · 두 태극씩도 a = 0 뿐.
· 한 층 올라가기 : q = 2, 3 의 매끈한 곡선 모두에서 N(F_q²) = q² + 1 − (a² − 2q) (각도 두 배).
· 정다면체 {p, q} : p, q ≥ 3 에서 (p − 2)(q − 2) < 4 이면 p, q ≤ 5 이고 그런 것은 다섯 · = 4 는 셋 (평면) · {7, 3} 은 > 4 (쌍곡).
  오일러 V − E + F = 2 · 쌍대 {p, q} ↔ {q, p} 는 V 와 F 를 바꾼다.
· 오각형 열둘 : 꼭짓점마다 면 셋, 오각형 p 개와 육각형 h 개뿐인 닫힌 다면체(오일러 V − E + F = 2)는 h 와 상관없이 p = 12.
· 클라인 4 차 곡선 : 칠각형 24 개, 꼭짓점마다 셋 → V 56 · E 84 · 종수 3 · 84(g − 1) = 168.
· 케일리–딕슨 : 8 원수 단위의 곱 e_a e_b = ± e_(a xor b) · 노름 곱 (시험 12 쌍) · (e1 + … + e7)² = −7 ·
  α = (1 + e1 + … + e7)/2 는 α² − α + 2 = 0 · 16 원수의 영인자 (e1 + e10)(e4 − e15) = 0 과 노름 곱이 깨지는 짝.
· F₉ = F₃[i] : g = 1 + i 의 거듭제곱이 0 아닌 여덟 칸을 한 바퀴 돈다 (차수 8) · 짝수 거듭제곱 = 축 위 넷 = 제곱수 ·
  홀수 거듭제곱 = 모서리 넷 · g⁷ · g = 1 · 0 아닌 여덟을 모두 곱하면 −1 (= 원소 2).

검증 : lean 태극아리랑.lean  (린 v4.34.0 · decide +kernel · #print axioms)
-/

namespace Trombo.TaegukArirang

/-! ## 체 -/

structure Fld where
  q : Nat
  add : Nat → Nat → Nat
  mul : Nat → Nat → Nat
  one : Nat → Nat

def primeF (p : Nat) : Fld := ⟨p, fun a b => (a + b) % p, fun a b => (a * b) % p, fun n => n % p⟩
def gf4mul (a b : Nat) : Nat := ([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD a []).getD b 0
def gf4 : Fld := ⟨4, fun a b => a ^^^ b, gf4mul, fun n => n % 2⟩
/-- F₉ = F₃[i] : 원소 u + 3v ↔ u + v·i -/
def gf9add (a b : Nat) : Nat := (a % 3 + b % 3) % 3 + 3 * ((a / 3 + b / 3) % 3)
def gf9mul (a b : Nat) : Nat := (a % 3 * (b % 3) + 2 * (a / 3) * (b / 3)) % 3 + 3 * ((a % 3 * (b / 3) + a / 3 * (b % 3)) % 3)
def gf9 : Fld := ⟨9, gf9add, gf9mul, fun n => n % 3⟩

theorem gf4_is_field : (List.range 4).all (fun a => a == 0 || (List.range 4).any fun b => gf4mul a b == 1) = true ∧
    (List.range 9).all (fun a => a == 0 || (List.range 9).any fun b => gf9mul a b == 1) = true := by decide +kernel

/-! ## 바이어슈트라스 식 -/

def lhs (K : Fld) (a1 a3 x y : Nat) : Nat := K.add (K.add (K.mul y y) (K.mul a1 (K.mul x y))) (K.mul a3 y)
def rhs (K : Fld) (a2 a4 a6 x : Nat) : Nat := K.add (K.add (K.add (K.mul x (K.mul x x)) (K.mul a2 (K.mul x x))) (K.mul a4 x)) a6
def onC (K : Fld) (a1 a2 a3 a4 a6 x y : Nat) : Bool := lhs K a1 a3 x y == rhs K a2 a4 a6 x
def gradZero (K : Fld) (a1 a2 a3 a4 x y : Nat) : Bool :=
  K.mul a1 y == K.add (K.add (K.mul (K.one 3) (K.mul x x)) (K.mul (K.one 2) (K.mul a2 x))) a4 &&
  K.add (K.add (K.mul (K.one 2) y) (K.mul a1 x)) a3 == 0
def countN (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Nat :=
  1 + (List.range K.q).foldl (fun s x => s + (List.range K.q).countP fun y => onC K a1 a2 a3 a4 a6 x y) 0
def singular (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Bool :=
  (List.range K.q).any fun x => (List.range K.q).any fun y => onC K a1 a2 a3 a4 a6 x y && gradZero K a1 a2 a3 a4 x y
def traceA (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Int := ((K.q + 1 : Nat) : Int) - ((countN K a1 a2 a3 a4 a6 : Nat) : Int)

/-- 조각 (a1 고정) : 매끈하면 대각합이 목록 안 -/
def chunkOK (K : Fld) (aset : List Int) (a1 : Nat) : Bool :=
  (List.range K.q).all fun a2 => (List.range K.q).all fun a3 => (List.range K.q).all fun a4 => (List.range K.q).all fun a6 =>
    singular K a1 a2 a3 a4 a6 || aset.contains (traceA K a1 a2 a3 a4 a6)
def chunkSing (K : Fld) (a1 : Nat) : Nat :=
  (List.range K.q).foldl (fun s a2 => s + (List.range K.q).foldl (fun t a3 => t + (List.range K.q).foldl
    (fun u a4 => u + (List.range K.q).countP fun a6 => singular K a1 a2 a3 a4 a6) 0) 0) 0
def boxAll (q : Nat) (aset : List Int) : Bool := aset.all fun a => decide (a * a ≤ 4 * (q : Int))
def witOK (K : Fld) (w : List (Int × List Nat)) : Bool :=
  w.all fun (a, e) => match e with
    | [a1, a2, a3, a4, a6] => !(singular K a1 a2 a3 a4 a6) && traceA K a1 a2 a3 a4 a6 == a
    | _ => false

def A2 : List Int := [-2, -1, 0, 1, 2]
def A3 : List Int := [-3, -2, -1, 0, 1, 2, 3]
def A4 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
def A5 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
def A7 : List Int := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

theorem box_lists : boxAll 2 A2 = true ∧ boxAll 3 A3 = true ∧ boxAll 4 A4 = true ∧ boxAll 5 A5 = true ∧ boxAll 7 A7 = true := by
  decide +kernel

theorem taeguk_two : (List.range 2).all (chunkOK (primeF 2) A2) = true ∧
    (List.range 2).foldl (fun s a1 => s + chunkSing (primeF 2) a1) 0 = 2 ^ 4 := by decide +kernel
theorem taeguk_three : (List.range 3).all (chunkOK (primeF 3) A3) = true ∧
    (List.range 3).foldl (fun s a1 => s + chunkSing (primeF 3) a1) 0 = 3 ^ 4 := by decide +kernel
theorem taeguk_four : (List.range 4).all (chunkOK gf4 A4) = true ∧
    (List.range 4).foldl (fun s a1 => s + chunkSing gf4 a1) 0 = 4 ^ 4 := by decide +kernel
theorem taeguk_five_0 : chunkOK (primeF 5) A5 0 = true ∧ chunkSing (primeF 5) 0 = 125 := by decide +kernel
theorem taeguk_five_1 : chunkOK (primeF 5) A5 1 = true ∧ chunkSing (primeF 5) 1 = 125 := by decide +kernel
theorem taeguk_five_2 : chunkOK (primeF 5) A5 2 = true ∧ chunkSing (primeF 5) 2 = 125 := by decide +kernel
theorem taeguk_five_3 : chunkOK (primeF 5) A5 3 = true ∧ chunkSing (primeF 5) 3 = 125 := by decide +kernel
theorem taeguk_five_4 : chunkOK (primeF 5) A5 4 = true ∧ chunkSing (primeF 5) 4 = 125 := by decide +kernel

/-- 목록의 a 마다 증인 곡선 (a1, a2, a3, a4, a6) -/
theorem witnesses :
    witOK (primeF 2) [(-2, [0, 0, 1, 1, 0]), (-1, [1, 0, 0, 0, 1]), (0, [0, 0, 1, 0, 0]), (1, [1, 0, 1, 0, 1]), (2, [0, 0, 1, 1, 1])] = true ∧
    witOK (primeF 3) [(-3, [0, 0, 0, 2, 1]), (-2, [0, 1, 0, 0, 1]), (-1, [0, 2, 0, 0, 1]), (0, [0, 0, 0, 1, 0]), (1, [0, 1, 0, 0, 2]),
      (2, [0, 2, 0, 0, 2]), (3, [0, 0, 0, 2, 2])] = true ∧
    witOK gf4 [(-4, [0, 0, 1, 0, 0]), (-3, [1, 0, 0, 0, 1]), (-2, [0, 0, 2, 0, 1]), (-1, [1, 0, 2, 0, 0]), (0, [0, 0, 1, 1, 0]),
      (1, [1, 0, 0, 0, 2]), (2, [0, 0, 2, 0, 0]), (3, [1, 0, 2, 0, 2]), (4, [0, 0, 1, 0, 2])] = true ∧
    witOK (primeF 5) [(-4, [0, 0, 0, 3, 0]), (-3, [0, 0, 0, 1, 1]), (-2, [0, 0, 0, 4, 0]), (-1, [0, 0, 0, 2, 1]), (0, [0, 0, 0, 0, 1]),
      (1, [0, 0, 0, 3, 2]), (2, [0, 0, 0, 1, 0]), (3, [0, 0, 0, 4, 2]), (4, [0, 0, 0, 2, 0])] = true ∧
    witOK (primeF 7) [(-5, [0, 0, 0, 0, 3]), (-4, [0, 0, 0, 0, 1]), (-3, [0, 0, 0, 1, 6]), (-2, [0, 0, 0, 1, 4]), (-1, [0, 0, 0, 0, 2]),
      (0, [0, 0, 0, 1, 0]), (1, [0, 0, 0, 0, 5]), (2, [0, 0, 0, 1, 3]), (3, [0, 0, 0, 1, 1]), (4, [0, 0, 0, 0, 6]), (5, [0, 0, 0, 0, 4])] = true := by
  decide +kernel

/-! ## 합집합과 교집합 (각도 a / 2√q) -/

def aL : List (Nat × List Int) := [(2, A2), (3, A3), (4, A4), (5, A5), (7, A7)]
def sgn (a : Int) : Int := if a > 0 then 1 else if a < 0 then -1 else 0
def sameAngle (q1 : Nat) (a1 : Int) (q2 : Nat) (a2 : Int) : Bool := a1 * a1 * (q2 : Int) == a2 * a2 * (q1 : Int) && sgn a1 == sgn a2
def allPairs : List (Nat × Int) := aL.flatMap fun (q, l) => l.map fun a => (q, a)
def reps : List (Nat × Int) :=
  allPairs.foldl (fun acc (q, a) => if acc.any (fun (q2, a2) => sameAngle q a q2 a2) then acc else acc ++ [(q, a)]) []
def inAll (q : Nat) (a : Int) : Bool := aL.all fun (q2, l) => l.any fun a2 => sameAngle q a q2 a2

theorem union_37 : reps.length = 37 := by decide +kernel
theorem intersection_center : reps.filter (fun (q, a) => inAll q a) = [(2, 0)] := by decide +kernel
theorem pairwise_center : aL.all (fun (q1, l1) => aL.all fun (q2, l2) =>
    q1 == q2 || l1.filter (fun a => l2.any fun b => sameAngle q1 a q2 b) == [0]) = true := by decide +kernel

/-! ## 한 층 올라가기 F_q → F_q² -/

def riseOK (K U : Fld) : Bool :=
  (List.range K.q).all fun a1 => (List.range K.q).all fun a2 => (List.range K.q).all fun a3 =>
  (List.range K.q).all fun a4 => (List.range K.q).all fun a6 =>
    singular K a1 a2 a3 a4 a6 ||
      (((countN U a1 a2 a3 a4 a6 : Nat) : Int) ==
        ((K.q * K.q + 1 : Nat) : Int) - (traceA K a1 a2 a3 a4 a6 * traceA K a1 a2 a3 a4 a6 - 2 * (K.q : Int)))

theorem rise_two_three : riseOK (primeF 2) gf4 = true ∧ riseOK (primeF 3) gf9 = true := by decide +kernel

/-! ## 정다면체 {p, q} -/

theorem sphere_bound (p q : Nat) (hp : 3 ≤ p) (hq : 3 ≤ q) (h : (p - 2) * (q - 2) < 4) : p ≤ 5 ∧ q ≤ 5 := by
  constructor
  · by_cases hc : p ≤ 5
    · exact hc
    · exfalso
      have h1 : 4 ≤ p - 2 := by omega
      have h2 : 1 ≤ q - 2 := by omega
      have h3 : 4 * 1 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul h1 h2
      omega
  · by_cases hc : q ≤ 5
    · exact hc
    · exfalso
      have h1 : 1 ≤ p - 2 := by omega
      have h2 : 4 ≤ q - 2 := by omega
      have h3 : 1 * 4 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul h1 h2
      omega

theorem flat_bound (p q : Nat) (hp : 3 ≤ p) (hq : 3 ≤ q) (h : (p - 2) * (q - 2) = 4) : p ≤ 6 ∧ q ≤ 6 := by
  constructor
  · by_cases hc : p ≤ 6
    · exact hc
    · exfalso
      have h1 : 5 ≤ p - 2 := by omega
      have h2 : 1 ≤ q - 2 := by omega
      have h3 : 5 * 1 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul h1 h2
      omega
  · by_cases hc : q ≤ 6
    · exact hc
    · exfalso
      have h1 : 1 ≤ p - 2 := by omega
      have h2 : 5 ≤ q - 2 := by omega
      have h3 : 1 * 5 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul h1 h2
      omega

def pq (n : Nat) (c : Nat → Nat → Bool) : List (Nat × Nat) :=
  (List.range n).flatMap fun p => (List.range n).filterMap fun q => if 3 ≤ p ∧ 3 ≤ q ∧ c p q = true then some (p, q) else none
theorem sphere_five : pq 6 (fun p q => decide ((p - 2) * (q - 2) < 4)) = [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] := by decide +kernel
theorem flat_three : pq 7 (fun p q => (p - 2) * (q - 2) == 4) = [(3, 6), (4, 4), (6, 3)] := by decide +kernel
theorem heptagon_hyperbolic : (7 - 2) * (3 - 2) > 4 := by decide

def solid (p q : Nat) : Nat × Nat × Nat :=
  let E := 2 * p * q / (4 - (p - 2) * (q - 2))
  (2 * E / q, E, 2 * E / p)
theorem platonic_numbers :
    [solid 3 3, solid 4 3, solid 3 4, solid 5 3, solid 3 5] = [(4, 6, 4), (8, 12, 6), (6, 12, 8), (20, 30, 12), (12, 30, 20)] := by
  decide +kernel
theorem euler_and_duality :
    [(3, 3), (4, 3), (3, 4), (5, 3), (3, 5)].all (fun (p, q) =>
      (solid p q).1 + (solid p q).2.2 == (solid p q).2.1 + 2 && (solid p q).1 == (solid q p).2.2 && (solid p q).2.1 == (solid q p).2.1) = true := by
  decide +kernel

/-! ## 다섯 대양 여섯 대주 — 오각형은 언제나 열둘 -/

theorem pentagons_twelve (p h V E : Nat) (h1 : 3 * V = 2 * E) (h2 : 2 * E = 5 * p + 6 * h) (h3 : V + (p + h) = E + 2) : p = 12 := by
  omega
theorem soccer_ball : 5 * 12 + 6 * 20 = 2 * 90 ∧ 3 * 60 = 2 * 90 ∧ 60 + (12 + 20) = 90 + 2 := by decide
/-- 골드버그 다면체 T = 1, 3, 4, 7, 9, 12, 13 : 오각형 12 · 육각형 10(T − 1) · V 20T · E 30T -/
theorem goldberg : [1, 3, 4, 7, 9, 12, 13].all (fun T =>
    3 * (20 * T) == 2 * (30 * T) && 2 * (30 * T) == 5 * 12 + 6 * (10 * (T - 1)) && 20 * T + (12 + 10 * (T - 1)) == 30 * T + 2) = true := by
  decide +kernel

/-! ## 일곱 — 클라인 4 차 곡선의 칠각형 -/

theorem klein_tiling : 7 * 24 = 2 * 84 ∧ 7 * 24 = 3 * 56 ∧ (56 : Int) - 84 + 24 = 2 - 2 * 3 ∧ 84 * (3 - 1) = 168 := by decide

/-! ## 여덟 — 케일리–딕슨 -/

def conjL : List Int → List Int
  | [] => []
  | x :: xs => x :: xs.map (fun t => -t)
def cdMul : Nat → List Int → List Int → List Int
  | 0, x, y => [x.headD 0 * y.headD 0]
  | n + 1, x, y =>
    let h := 2 ^ n
    List.zipWith (· - ·) (cdMul n (x.take h) (y.take h)) (cdMul n (conjL (y.drop h)) (x.drop h)) ++
      List.zipWith (· + ·) (cdMul n (y.drop h) (x.take h)) (cdMul n (x.drop h) (conjL (y.take h)))
def eU (n k : Nat) : List Int := (List.range n).map fun i => if i == k then 1 else 0
def nsq (x : List Int) : Int := x.foldl (fun s t => s + t * t) 0
def addL (x y : List Int) : List Int := List.zipWith (· + ·) x y
def negL (x : List Int) : List Int := x.map (fun t => -t)

theorem octonion_table : (List.range 8).all (fun a => (List.range 8).all fun b =>
    cdMul 3 (eU 8 a) (eU 8 b) == eU 8 (a ^^^ b) || cdMul 3 (eU 8 a) (eU 8 b) == negL (eU 8 (a ^^^ b))) = true := by decide +kernel
theorem octonion_norm : [([-1, -2, 0, 2, -3, -3, 3, 1], [-3, -1, 1, -3, 1, -2, -3, -3]), ([0, 0, -3, -2, -3, 1, 0, -3], [3, 1, -3, -2, 2, 2, 1, -3]),
    ([1, 1, 0, -3, -2, -3, 1, 3], [-2, -1, 0, -2, 1, -3, 1, -1]), ([1, 3, 2, -2, -3, 1, 1, 2], [-2, -1, -3, 1, 2, -3, 1, -3]),
    ([1, -2, 0, 2, 1, 0, 3, -1], [0, 1, 0, -1, -1, -2, 3, -2]), ([2, 3, -2, -3, 1, -1, 1, 0], [-1, 2, 0, -1, 1, -3, -3, 1]),
    ([0, -2, 3, -1, -2, 0, 0, -3], [2, -3, 3, 1, 1, 3, 3, -1]), ([-1, 2, -1, 1, 0, 1, 3, 0], [-3, 3, -3, -1, 0, 2, 2, -3]),
    ([-3, 2, 2, -1, 2, 1, 2, 3], [0, -1, 2, 0, 2, -1, -3, 0]), ([-1, -2, 1, -3, 0, -3, -2, 3], [-1, -2, 2, -2, 0, 0, 3, 0]),
    ([-3, -2, 0, 0, 1, -1, -2, 3], [0, 3, 1, -1, 2, 0, -1, 2]), ([0, -2, -2, -3, -2, -2, -2, 2], [-2, -3, 0, 3, 1, -2, -1, -1])].all
    (fun (x, y) => nsq (cdMul 3 x y) == nsq x * nsq y) = true := by decide +kernel
theorem seven_units_square : cdMul 3 [0, 1, 1, 1, 1, 1, 1, 1] [0, 1, 1, 1, 1, 1, 1, 1] = [-7, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
/-- 2α = 1 + e1 + … + e7 : (2α)² = 2(2α) − 8 ⇔ α² − α + 2 = 0 -/
theorem half_ones_frobenius : cdMul 3 [1, 1, 1, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1] = [-6, 2, 2, 2, 2, 2, 2, 2] := by decide +kernel
theorem sedenion_zero_divisor :
    cdMul 4 (addL (eU 16 1) (eU 16 10)) (addL (eU 16 4) (negL (eU 16 15))) = List.replicate 16 0 := by decide +kernel
theorem sedenion_norm_breaks :
    nsq (cdMul 4 [-2, -1, 1, 2, 0, 2, 2, 0, -1, 2, 2, -2, 1, 2, 1, 1] [1, 1, -2, 1, 1, -2, -1, -2, -1, 1, -1, -2, 0, 2, -2, -2]) ≠
      nsq [-2, -1, 1, 2, 0, 2, 2, 0, -1, 2, 2, -2, 1, 2, 1, 1] * nsq [1, 1, -2, 1, 1, -2, -1, -2, -1, 1, -1, -2, 0, 2, -2, -2] := by
  decide +kernel

/-! ## 아홉 — 가운데 하나와 여덟 고리 (F₉ = F₃[i]) -/

def g9pow : Nat → Nat
  | 0 => 1
  | k + 1 => gf9mul (g9pow k) 4
theorem nine_loop : (List.range 9).map g9pow = [1, 4, 6, 7, 2, 8, 3, 5, 1] ∧
    (List.range 9).all (fun z => z == 0 || ((List.range 8).map g9pow).contains z) = true ∧
    (List.range 8).all (fun k => (k % 2 == 0) == (g9pow k % 3 == 0 || g9pow k / 3 == 0)) = true ∧
    (List.range 8).all (fun k => (k % 2 == 0) == (List.range 9).any fun z => z != 0 && gf9mul z z == g9pow k) = true ∧
    gf9mul (g9pow 7) 4 = 1 := by decide +kernel

theorem nine_product_minus_one : (List.range 9).foldl (fun s z => if z == 0 then s else gf9mul s z) 1 = 2 := by decide +kernel

#print axioms gf4_is_field
#print axioms box_lists
#print axioms taeguk_two
#print axioms taeguk_three
#print axioms taeguk_four
#print axioms taeguk_five_0
#print axioms taeguk_five_1
#print axioms taeguk_five_2
#print axioms taeguk_five_3
#print axioms taeguk_five_4
#print axioms witnesses
#print axioms union_37
#print axioms intersection_center
#print axioms pairwise_center
#print axioms rise_two_three
#print axioms sphere_bound
#print axioms flat_bound
#print axioms sphere_five
#print axioms flat_three
#print axioms heptagon_hyperbolic
#print axioms platonic_numbers
#print axioms euler_and_duality
#print axioms pentagons_twelve
#print axioms soccer_ball
#print axioms goldberg
#print axioms klein_tiling
#print axioms octonion_table
#print axioms octonion_norm
#print axioms seven_units_square
#print axioms half_ones_frobenius
#print axioms sedenion_zero_divisor
#print axioms sedenion_norm_breaks
#print axioms nine_loop
#print axioms nine_product_minus_one

end Trombo.TaegukArirang

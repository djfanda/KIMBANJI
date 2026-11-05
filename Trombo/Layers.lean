/-
세 층 — 천장 qⁿ · 바닥 1 · 면 |α| = q^½  (린 4 커널 확인 · Mathlib 없이 · 린 코어만)

유한체 F_q 위 매끈한 사영 곡선(구멍 g 개)의 점 셈은 N n = qⁿ + 1 − (α₁ⁿ + ⋯ + α_{2g}ⁿ) 이고 |αᵢ| = q^½ 이다
(하세 1933–36 · 바일 1948 — 전언). 세 층이 그대로 지수다 : 천장 qⁿ (지수 1) · 바닥 1 (지수 0) · 면 |α| = q^½ (지수 ½ · 리만 선).
영점을 √q 로 나누면 반지름 1 의 원 위에 놓인다 («바닥 둘레 1» — 해석). 구멍 g 개 → 면 위 영점 2g 개 (해석).
이 파일은 무한체의 리만 가설에 대해 아무 주장도 하지 않는다. 전언인 정리는 쓰지 않는다 — 곡선 하나하나를 세고, 정수 항등식은 귀납으로 닫는다.

■ 1 루카스 수열 (모든 정수 a, q · 모든 높이 n · 귀납 + grind)
  U 0 = 0 · U 1 = 1 · V 0 = 2 · V 1 = a · X (n + 2) = a·X (n + 1) − q·X n.
  V n = 2·U (n + 1) − a·U n · 카시니 U (n + 1)² − a·U (n + 1)·U n + q·U n² = qⁿ · V n² − (a² − 4q)·U n² = 4·qⁿ ·
  a² ≤ 4q 이면 모든 n 에서 V n² ≤ 4·qⁿ (모든 높이에서 면 위 · 상자 안) · N n = qⁿ + 1 − V n 이면 (N n − qⁿ − 1)² ≤ 4·qⁿ ·
  함수 방정식 : P(T) = 1 − aT + qT² 의 계수 대칭 c₂ = q·c₀ 과 «T² q P(1/(qT)) = P(T)» 의 분모 없는 꼴 · V 는 P(T) 의 뉴턴 항등식을 따른다.
■ 2 셈과의 일치 (q = 2) : F_2 위 바이어슈트라스 식 y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆ 32 개 가운데 매끈한 것 16 · 흠 16 = 2⁴.
  a = 3 − N 1 은 −2, −1, 0, 1, 2 (곡선 2 · 4 · 4 · 4 · 2) · 매끈한 16 곡선 모두 F_2 · F_4 · F_8 · F_16 위에서 직접 센
  사영 점 수가 N n = 2ⁿ + 1 − V n (n = 1, 2, 3, 4).
  체 : F_4 = F_2[x]/(x² + x + 1) · F_8 = F_2[x]/(x³ + x + 1) · F_16 = F_2[x]/(x⁴ + x + 1) · F_32 = F_2[x]/(x⁵ + x² + 1) ·
  F_64 = F_2[x]/(x⁶ + x + 1) — 원소는 비트 자연수 · 덧셈 xor · 곱은 다항식 곱의 나머지. 법 다항식은 기약이고 0 아닌 원소마다 역원.
■ 3 구멍과 면
  (a) 구멍 0 — 사영 직선 : 모닉 기약 다항식을 전수로 세어 q = 2 : I_1 … I_8 = 2, 1, 2, 3, 6, 9, 18, 30 ·
      q = 3 : I_1 … I_5 = 3, 3, 8, 18, 48 · Σ_{d | n} d·I_d = qⁿ
      (해석 : 아핀 직선의 점 셈 — 무한점 하나를 더해 N n = qⁿ + 1 · 면 위 영점 없음).
  (b) 구멍 1 — 타원곡선 = ■ 2 · ■ 4 · 면 위 영점 둘. 매끈한 곡선마다 a² ≤ 4q 이므로 a 로 적은 N n 꼴은 모든 n 에서
      (N n − qⁿ − 1)² ≤ 4·qⁿ (■ 1 의 상자 · 실제 셈과의 일치는 위에서 센 n 까지 — 그 너머는 전언).
  (c) 구멍 3 — 클라인 4 차 곡선 x³y + y³z + z³x = 0 : F_8 위에 특이점 없음 · F_2, F_4, F_8, F_16, F_32, F_64 위 사영 점 3, 5, 24, 17, 33, 38 ·
      P(T) = 1 + 5T³ + 8T⁶ 의 뉴턴 항등식 s_n = 0, 0, −15, 0, 0, 27 · N n = 2ⁿ + 1 − s_n · 계수 대칭 c₆ = 2³·c₀ ·
      u = T³ 로 8u² + 5u + 1 의 판별식 25 − 32 = −7 · s_{3m} = 3·V(−5, 8, m) (다른 n 에서 0) 은 모든 n 에서 뉴턴 점화식을 따르고
      s_n² ≤ 36·2ⁿ (6 = 2g · 면 위 영점 여섯의 셈 꼴).
■ 4 q = 3 : F_3 · F_9 = F_3[i]/(i² + 1) · F_27 = F_3[t]/(t³ − t − 1) 위 y² = x³ + a₂x² + a₄x + a₆ 27 개 가운데 매끈한 것 18 개 모두
  a = 4 − N 1 에 대해 a² ≤ 12 · N n = 3ⁿ + 1 − V n (n = 1, 2, 3).

전언 : 제타 함수의 유리성 Z(T) = P(T)/((1 − T)(1 − qT)) · 함수 방정식 · |α| = √q (하세 · 바일) · 가우스의 기약 다항식 공식.
전언 : 바이어슈트라스 3 차 곡선의 특이점은 많아야 하나이므로 기초체 위에 있다 — 그래서 매끈함은 F_q 위 전수로 판정한다.
해석 (손 계산) : 클라인 곡선의 기울기 (x²y + z³, x³ + y²z, y³ + z²x) (표수 2) 는 x ≠ 0 에서만 0 이 될 수 있고, x = 1 로 두면 y = z³ · z⁷ = 1 —
  기울기가 0 인 점은 모두 F_8 안에 있으므로 F_8 위 전수로 매끈함을 판정한다.

검증 : lean 세층.lean  (린 v4.34.0 · decide +kernel · grind · omega · #print axioms)
반대 시험 : lean 세층_반대.lean  (거짓 문장은 모두 오류로 거부된다)
-/

namespace Trombo.Layers

/-! ## 1 루카스 수열 — 모든 a, q 와 모든 높이 n -/

/-- U 0 = 0 · U 1 = 1 · U (n + 2) = a·U (n + 1) − q·U n -/
def U (a q : Int) : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => a * U a q (n + 1) - q * U a q n

/-- V 0 = 2 · V 1 = a · V (n + 2) = a·V (n + 1) − q·V n (해석 : 면의 두 영점 α, β 에서 αⁿ + βⁿ · α + β = a · αβ = q) -/
def V (a q : Int) : Nat → Int
  | 0 => 2
  | 1 => a
  | n + 2 => a * V a q (n + 1) - q * V a q n

/-- 면 : U · V 의 두 칸 점화식 (정의 그대로) -/
theorem lucas_step (a q : Int) (n : Nat) :
    U a q (n + 2) = a * U a q (n + 1) - q * U a q n ∧ V a q (n + 2) = a * V a q (n + 1) - q * V a q n := ⟨rfl, rfl⟩

/-- 면 (i) : V n = 2·U (n + 1) − a·U n — 두 영점의 거듭제곱 합이 U 로 적힌다 -/
theorem lucas_v_from_u (a q : Int) (n : Nat) : V a q n = 2 * U a q (n + 1) - a * U a q n := by
  have h : ∀ n, V a q n = 2 * U a q (n + 1) - a * U a q n ∧
      V a q (n + 1) = 2 * U a q (n + 2) - a * U a q (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [U, V], by simp [U, V]; grind⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e1 := (lucas_step a q k).2
      have e2 := (lucas_step a q (k + 1)).1
      have e3 := (lucas_step a q k).1
      have h1 := ih.1
      have h2 := ih.2
      grind
  exact (h n).1

/-- 천장 (ii) 카시니 : U (n + 1)² − a·U (n + 1)·U n + q·U n² = qⁿ — 천장의 거듭제곱이 그대로 나온다 -/
theorem cassini (a q : Int) (n : Nat) :
    U a q (n + 1) ^ 2 - a * U a q (n + 1) * U a q n + q * U a q n ^ 2 = q ^ n := by
  induction n with
  | zero => simp [U]
  | succ k ih =>
    have e := (lucas_step a q k).1
    have p := Int.pow_succ q k
    grind

/-- 천장 · 면 (iii) : V n² − (a² − 4q)·U n² = 4·qⁿ -/
theorem lucas_norm (a q : Int) (n : Nat) : V a q n ^ 2 - (a ^ 2 - 4 * q) * U a q n ^ 2 = 4 * q ^ n := by
  have h1 := lucas_v_from_u a q n
  have h2 := cassini a q n
  grind

/-- 면 (iv) : a² ≤ 4q 이면 모든 n 에서 V n² ≤ 4·qⁿ — 모든 높이에서 면 위 (상자 안) -/
theorem in_box (a q : Int) (h : a ^ 2 ≤ 4 * q) (n : Nat) : V a q n ^ 2 ≤ 4 * q ^ n := by
  have h1 := lucas_norm a q n
  have h2 : 0 ≤ (4 * q - a ^ 2) * U a q n ^ 2 := Int.mul_nonneg (by omega) (Int.sq_nonneg _)
  grind

/-- 점 셈의 꼴 N n = qⁿ + 1 − V n : 천장 qⁿ · 바닥 1 · 면 V n -/
def N (a q : Int) (n : Nat) : Int := q ^ n + 1 - V a q n

/-- 천장 · 바닥 · 면 (v) : a² ≤ 4q 이면 모든 n 에서 (N n − qⁿ − 1)² ≤ 4·qⁿ -/
theorem count_in_box (a q : Int) (h : a ^ 2 ≤ 4 * q) (n : Nat) : (N a q n - q ^ n - 1) ^ 2 ≤ 4 * q ^ n := by
  have h1 := in_box a q h n
  unfold N
  grind

/-- P(T) = 1 − aT + qT² -/
def P (a q T : Int) : Int := 1 - a * T + q * T ^ 2
/-- 뒤집은 다항식 X² P(1/X) = X² − aX + q -/
def Prev (a q X : Int) : Int := X ^ 2 - a * X + q
/-- 계수 대칭 c_{2g−i} = q^{g−i}·c_i (i = 0 … g) -/
def symOK (q : Int) (g : Nat) (c : List Int) : Bool :=
  c.length == 2 * g + 1 && (List.range (g + 1)).all fun i => c.getD (2 * g - i) 0 == q ^ (g - i) * c.getD i 0

/-- 바닥 ↔ 천장 (vi) 함수 방정식 : 계수 대칭 c₂ = q·c₀ · q·T²·[(qT)² P(1/(qT))] = (qT)²·P(T) · (qT)² P(1/(qT)) = q·P(T) -/
theorem functional_equation (a q T : Int) :
    symOK q 1 [1, -a, q] = true ∧ q * T ^ 2 * Prev a q (q * T) = (q * T) ^ 2 * P a q T ∧
    Prev a q (q * T) = q * P a q T := by
  refine ⟨by simp [symOK, List.range, List.range.loop, Int.pow_one], by unfold Prev P; grind, by unfold Prev P; grind⟩

/-- 면 : V 는 P(T) = 1 − aT + qT² 의 뉴턴 항등식을 따른다 (s₁ + c₁ = 0 · s₂ + c₁s₁ + 2c₂ = 0 · s_{n+2} + c₁s_{n+1} + c₂s_n = 0) -/
theorem newton_two (a q : Int) (n : Nat) :
    V a q 1 + (-a) = 0 ∧ V a q 2 + (-a) * V a q 1 + 2 * q = 0 ∧
    V a q (n + 2) + (-a) * V a q (n + 1) + q * V a q n = 0 := by
  refine ⟨by simp only [V]; omega, by simp [V]; grind, by rw [(lucas_step a q n).2]; grind⟩

/-! ## 2 체 — 원소를 자연수로 적는다 -/

/-- 체 : 원소 수 · 덧셈 · 곱셈 · 정수 n 의 상 n·1 -/
structure Fld where
  size : Nat
  add : Nat → Nat → Nat
  mul : Nat → Nat → Nat
  num : Nat → Nat

/-- F_2 위 비트 다항식의 곱 (자리올림 없는 곱 · b 의 아래 k 비트) -/
def clmul (k a b : Nat) : Nat :=
  (List.range k).foldl (fun acc i => if (b >>> i) % 2 == 1 then acc ^^^ (a <<< i) else acc) 0
/-- 차수 k 의 법 다항식 m 으로 나눈 나머지 (c 의 차수 ≤ 2k − 2) -/
def reduce (k m c : Nat) : Nat :=
  (List.range (k - 1)).foldr (fun s acc => if (acc >>> (s + k)) % 2 == 1 then acc ^^^ (m <<< s) else acc) c
/-- F_{2^k} = F_2[x]/(m) : 덧셈 xor · 곱은 다항식 곱의 나머지 -/
def gf2 (k m : Nat) : Fld := ⟨2 ^ k, fun a b => a ^^^ b, fun a b => reduce k m (clmul k a b), fun n => n % 2⟩

def F2 : Fld := gf2 1 3
def F4 : Fld := gf2 2 7
def F8 : Fld := gf2 3 11
def F16 : Fld := gf2 4 19
def F32 : Fld := gf2 5 37
def F64 : Fld := gf2 6 67

/-- F_9 = F_3[i]/(i² + 1) : k = u + 3v ↔ u + v·i -/
def add9 (k l : Nat) : Nat := (k % 3 + l % 3) % 3 + 3 * ((k / 3 + l / 3) % 3)
def mul9 (k l : Nat) : Nat :=
  (k % 3 * (l % 3) + 2 * (k / 3 * (l / 3))) % 3 + 3 * ((k % 3 * (l / 3) + k / 3 * (l % 3)) % 3)
/-- F_27 = F_3[t]/(t³ − t − 1) : k = c₀ + 3c₁ + 9c₂ ↔ c₀ + c₁t + c₂t² (t³ = t + 1 · t⁴ = t² + t) -/
def add27 (k l : Nat) : Nat :=
  (k % 3 + l % 3) % 3 + 3 * ((k / 3 % 3 + l / 3 % 3) % 3) + 9 * ((k / 9 + l / 9) % 3)
def mul27 (k l : Nat) : Nat :=
  let c0 := k % 3; let c1 := k / 3 % 3; let c2 := k / 9
  let d0 := l % 3; let d1 := l / 3 % 3; let d2 := l / 9
  let e0 := c0 * d0; let e1 := c0 * d1 + c1 * d0; let e2 := c0 * d2 + c1 * d1 + c2 * d0
  let e3 := c1 * d2 + c2 * d1; let e4 := c2 * d2
  (e0 + e3) % 3 + 3 * ((e1 + e3 + e4) % 3) + 9 * ((e2 + e4) % 3)

def F3 : Fld := ⟨3, fun a b => (a + b) % 3, fun a b => a * b % 3, fun n => n % 3⟩
def F9 : Fld := ⟨9, add9, mul9, fun n => n % 3⟩
def F27 : Fld := ⟨27, add27, mul27, fun n => n % 3⟩

/-- 0 아닌 원소마다 곱의 역원이 있다 -/
def isField (K : Fld) : Bool :=
  (List.range K.size).all fun a => a == 0 || (List.range K.size).any fun b => K.mul a b == 1

/-- F_2 위 비트 다항식 f (차수 d) 를 g (차수 e) 로 나눈 나머지 -/
def pmod2 (d e f g : Nat) : Nat :=
  (List.range (d - e + 1)).foldr (fun s acc => if (acc >>> (s + e)) % 2 == 1 then acc ^^^ (g <<< s) else acc) f
/-- 기약 (F_2) : 차수 1 … d/2 의 어느 다항식으로도 나누어떨어지지 않는다 -/
def irred2 (d f : Nat) : Bool :=
  (List.range (d / 2)).all fun e => (List.range (2 ^ (e + 1))).all fun r => pmod2 d (e + 1) f (2 ^ (e + 1) + r) != 0

/-- F_p 위 다항식 = 계수 목록 (낮은 차수부터) · 번호 r 의 p 진 자리 -/
def digits (p len r : Nat) : List Nat := (List.range len).map fun i => r / p ^ i % p
/-- 차수 d 의 모닉 다항식 (번호 r < p^d) -/
def monic (p d r : Nat) : List Nat := digits p d r ++ [1]
/-- f − c·xˢ·g (계수마다 mod p) -/
def subShift (p : Nat) (f : List Nat) (c s : Nat) (g : List Nat) : List Nat :=
  (List.range f.length).map fun i => (f.getD i 0 + (p - c) * (if s ≤ i then g.getD (i - s) 0 else 0)) % p
/-- 모닉 g (차수 e) 로 나눈 나머지 -/
def pmodP (p e : Nat) (f g : List Nat) : List Nat :=
  (List.range (f.length - e)).foldr (fun s acc => let c := acc.getD (s + e) 0; if c == 0 then acc else subShift p acc c s g) f
/-- 기약 (F_p) : 차수 1 … d/2 의 어느 모닉 다항식으로도 나누어떨어지지 않는다 -/
def irredP (p d : Nat) (f : List Nat) : Bool :=
  (List.range (d / 2)).all fun e => (List.range (p ^ (e + 1))).all fun r =>
    !((pmodP p (e + 1) f (monic p (e + 1) r)).all (· == 0))

/-- 천장 qⁿ = 체 F_{qⁿ} 의 원소 수 : F_4 … F_64 · F_9 · F_27 은 0 아닌 원소마다 역원이 있고 법 다항식은 기약 -/
theorem fields_ok : [F4, F8, F16, F32, F64, F9, F27].all isField = true ∧
    [(2, 7), (3, 11), (4, 19), (5, 37), (6, 67)].all (fun (k, m) => irred2 k m) = true ∧
    irredP 3 2 [1, 0, 1] = true ∧ irredP 3 3 [2, 2, 0, 1] = true := by
  decide +kernel

/-! ## 3 구멍 1 — 타원곡선의 셈 -/

/-- 바이어슈트라스 식 e = [a₁, a₂, a₃, a₄, a₆] 의 왼쪽 y² + a₁xy + a₃y 와 오른쪽 x³ + a₂x² + a₄x + a₆ -/
def wOn (K : Fld) (e : List Nat) (x y : Nat) : Bool :=
  K.add (K.add (K.mul y y) (K.mul (e.getD 0 0) (K.mul x y))) (K.mul (e.getD 2 0) y) ==
    K.add (K.add (K.add (K.mul x (K.mul x x)) (K.mul (e.getD 1 0) (K.mul x x))) (K.mul (e.getD 3 0) x)) (e.getD 4 0)
/-- 기울기 0 : a₁y = 3x² + 2a₂x + a₄ 이고 2y + a₁x + a₃ = 0 -/
def wGrad (K : Fld) (e : List Nat) (x y : Nat) : Bool :=
  K.mul (e.getD 0 0) y == K.add (K.add (K.mul (K.num 3) (K.mul x x)) (K.mul (K.num 2) (K.mul (e.getD 1 0) x))) (e.getD 3 0) &&
    K.add (K.add (K.mul (K.num 2) y) (K.mul (e.getD 0 0) x)) (e.getD 2 0) == 0
/-- 흠 (특이점) : 곡선 위에서 기울기가 0 인 점 -/
def wSingular (K : Fld) (e : List Nat) : Bool :=
  (List.range K.size).any fun x => (List.range K.size).any fun y => wOn K e x y && wGrad K e x y
/-- 사영 점의 수 : 아핀 점 + 무한점 하나 -/
def wCount (K : Fld) (e : List Nat) : Nat :=
  1 + (List.range K.size).foldl (fun s x => s + (List.range K.size).countP fun y => wOn K e x y) 0
/-- a = q + 1 − N 1 -/
def wTrace (K : Fld) (e : List Nat) : Int := (K.size : Int) + 1 - (wCount K e : Int)
/-- 매끈하면 K (원소 qⁿ 개) 위 점 수가 qⁿ + 1 − V(a, q, n) -/
def layerOK (base K : Fld) (n : Nat) (e : List Nat) : Bool :=
  wSingular base e ||
    (K.size == base.size ^ n && (wCount K e : Int) == (base.size : Int) ^ n + 1 - V (wTrace base e) base.size n)

def eqsTwo : List (List Nat) := (List.range 32).map fun i => [i % 2, i / 2 % 2, i / 4 % 2, i / 8 % 2, i / 16 % 2]
def eqsThree : List (List Nat) := (List.range 27).map fun i => [0, i % 3, 0, i / 3 % 3, i / 9 % 3]
def tracesTwo : List Int := (eqsTwo.filter fun e => !wSingular F2 e).map (wTrace F2)
def tracesThree : List Int := (eqsThree.filter fun e => !wSingular F3 e).map (wTrace F3)

/-- 구멍 1 : F_2 위 식 32 개 가운데 매끈한 것 16 · 흠 16 = 2⁴ · a = 3 − N 1 은 a² ≤ 8 (면 위) 이고 a = −2 … 2 에 곡선 2 · 4 · 4 · 4 · 2 -/
theorem weier_two_smooth : (eqsTwo.filter fun e => !wSingular F2 e).length = 16 ∧ (eqsTwo.filter (wSingular F2)).length = 2 ^ 4 ∧
    tracesTwo.all (fun a => decide (a * a ≤ 8)) = true ∧ [-2, -1, 0, 1, 2].map (fun t => tracesTwo.count t) = [2, 4, 4, 4, 2] := by
  decide +kernel

/-- 천장 · 바닥 · 면 (q = 2 · n = 1, 2, 3) : 매끈한 16 곡선 모두 F_2 · F_4 · F_8 위 N n = 2ⁿ + 1 − V n -/
theorem weier_two_low : eqsTwo.all (layerOK F2 F2 1) = true ∧ eqsTwo.all (layerOK F2 F4 2) = true ∧
    eqsTwo.all (layerOK F2 F8 3) = true := by
  decide +kernel

/-- 천장 · 바닥 · 면 (q = 2 · n = 4) : 매끈한 16 곡선 모두 F_16 위 N 4 = 16 + 1 − V 4 -/
theorem weier_two_f16 : eqsTwo.all (layerOK F2 F16 4) = true := by
  decide +kernel

/-- 구멍 1 (q = 3) : y² = x³ + a₂x² + a₄x + a₆ 27 개 가운데 매끈한 것 18 · a = 4 − N 1 은 a² ≤ 12 (면 위) -/
theorem weier_three_smooth : (eqsThree.filter fun e => !wSingular F3 e).length = 18 ∧
    tracesThree.all (fun a => decide (a * a ≤ 12)) = true := by
  decide +kernel

/-- 천장 · 바닥 · 면 (q = 3) : 매끈한 18 곡선 모두 F_3 · F_9 · F_27 위 N n = 3ⁿ + 1 − V n (n = 1, 2, 3) -/
theorem weier_three_layers : eqsThree.all (layerOK F3 F3 1) = true ∧ eqsThree.all (layerOK F3 F9 2) = true ∧
    eqsThree.all (layerOK F3 F27 3) = true := by
  decide +kernel

/-- 천장 · 바닥 · 면 (모든 높이) : 매끈한 곡선 (q = 2 의 16 · q = 3 의 18) 의 a 로 적은 N n 은 모든 n 에서 (N n − qⁿ − 1)² ≤ 4·qⁿ -/
theorem weier_all_heights (n : Nat) :
    (∀ a ∈ tracesTwo, (N a 2 n - 2 ^ n - 1) ^ 2 ≤ 4 * 2 ^ n) ∧
    (∀ a ∈ tracesThree, (N a 3 n - 3 ^ n - 1) ^ 2 ≤ 4 * 3 ^ n) := by
  constructor
  · intro a ha
    have h := List.all_eq_true.mp weier_two_smooth.2.2.1 a ha
    exact count_in_box a 2 (by simp at h; grind) n
  · intro a ha
    have h := List.all_eq_true.mp weier_three_smooth.2 a ha
    exact count_in_box a 3 (by simp at h; grind) n

/-! ## 4 구멍 0 — 사영 직선 : 기약 다항식의 셈 -/

/-- 차수 d 의 모닉 기약 다항식 수 (F_2 · 비트) -/
def irrCount2 (d : Nat) : Nat := (List.range (2 ^ d)).countP fun r => irred2 d (2 ^ d + r)
/-- 차수 d 의 모닉 기약 다항식 수 (F_p · 계수 목록) -/
def irrCountP (p d : Nat) : Nat := (List.range (p ^ d)).countP fun r => irredP p d (monic p d r)
/-- Σ_{d | n} d·I_d -/
def gaussSum (I : List Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun s d => if n % (d + 1) == 0 then s + (d + 1) * I.getD d 0 else s) 0

/-- 구멍 0 : F_2 위 I_1 … I_8 = 2, 1, 2, 3, 6, 9, 18, 30 이고 Σ_{d | n} d·I_d = 2ⁿ (n ≤ 8) — 면 없이 천장 + 바닥 -/
theorem line_two : (List.range 8).map (fun d => irrCount2 (d + 1)) = [2, 1, 2, 3, 6, 9, 18, 30] ∧
    (List.range 8).all (fun n => gaussSum [2, 1, 2, 3, 6, 9, 18, 30] (n + 1) == 2 ^ (n + 1)) = true := by
  decide +kernel

/-- 구멍 0 : F_3 위 I_1 … I_5 = 3, 3, 8, 18, 48 이고 Σ_{d | n} d·I_d = 3ⁿ (n ≤ 5) — 면 없이 천장 + 바닥 -/
theorem line_three : (List.range 5).map (fun d => irrCountP 3 (d + 1)) = [3, 3, 8, 18, 48] ∧
    (List.range 5).all (fun n => gaussSum [3, 3, 8, 18, 48] (n + 1) == 3 ^ (n + 1)) = true := by
  decide +kernel

/-! ## 5 구멍 3 — 클라인 4 차 곡선 x³y + y³z + z³x = 0 -/

def kleinF (K : Fld) (x y z : Nat) : Nat :=
  K.add (K.add (K.mul (K.mul x (K.mul x x)) y) (K.mul (K.mul y (K.mul y y)) z)) (K.mul (K.mul z (K.mul z z)) x)
/-- 기울기 (3x²y + z³, x³ + 3y²z, y³ + 3z²x) 가 0 -/
def kleinGrad (K : Fld) (x y z : Nat) : Bool :=
  K.add (K.mul (K.num 3) (K.mul (K.mul x x) y)) (K.mul z (K.mul z z)) == 0 &&
    K.add (K.mul x (K.mul x x)) (K.mul (K.num 3) (K.mul (K.mul y y) z)) == 0 &&
    K.add (K.mul y (K.mul y y)) (K.mul (K.num 3) (K.mul (K.mul z z) x)) == 0
/-- 사영 평면 P²(K) 의 점 [x : y : 1] · [x : 1 : 0] · [1 : 0 : 0] 가운데 pr 을 만족하는 것의 수 -/
def projCount (K : Fld) (pr : Nat → Nat → Nat → Bool) : Nat :=
  (List.range K.size).foldl (fun s x => s + (List.range K.size).countP fun y => pr x y 1) 0 +
    (List.range K.size).countP (fun x => pr x 1 0) + (if pr 1 0 0 then 1 else 0)
def kleinCount (K : Fld) : Nat := projCount K fun x y z => kleinF K x y z == 0

/-- 구멍 3 : 클라인 곡선은 F_8 위에 특이점이 없다 — 기울기 0 인 점 일곱 (z⁷ = 1) 은 모두 곡선 밖 -/
theorem klein_smooth : projCount F8 (fun x y z => kleinGrad F8 x y z) = 7 ∧
    projCount F8 (fun x y z => kleinF F8 x y z == 0 && kleinGrad F8 x y z) = 0 := by
  decide +kernel

/-- 구멍 3 · 천장 · 바닥 · 면 : 사영 점 수 F_2 · F_4 · F_8 · F_16 · F_32 = 3, 5, 24, 17, 33 -/
theorem klein_counts : [kleinCount F2, kleinCount F4, kleinCount F8, kleinCount F16, kleinCount F32] = [3, 5, 24, 17, 33] := by
  decide +kernel

/-- 구멍 3 · 천장 · 바닥 · 면 : F_64 위 사영 점 수 38 (= 64 + 1 − 27) -/
theorem klein_count_64 : kleinCount F64 = 38 := by
  decide +kernel

/-- 뉴턴 항등식 한 걸음 : s_k = −(c₁s_{k−1} + ⋯ + c_{k−1}s₁ + k·c_k) -/
def newtonStep (c s : List Int) : List Int :=
  let k := s.length + 1
  s ++ [-((List.range (k - 1)).foldl (fun t i => t + c.getD (i + 1) 0 * s.getD (k - 2 - i) 0) 0 + (k : Int) * c.getD k 0)]
/-- P(T) = Σ cᵢTⁱ (c₀ = 1) 의 영점 역수 거듭제곱 합 s₁, …, s_K -/
def newton (c : List Int) (K : Nat) : List Int := (List.range K).foldl (fun s _ => newtonStep c s) []

/-- s n : 3 ∣ n 이면 3·V(−5, 8, n/3), 아니면 0 (해석 : β = α³ 은 β² + 5β + 8 = 0 의 두 근) -/
def kleinS (n : Nat) : Int := if n % 3 = 0 then 3 * V (-5) 8 (n / 3) else 0

/-- 구멍 3 · 면 : P(T) = 1 + 5T³ + 8T⁶ 의 뉴턴 항등식 s₁ … s₆ = 0, 0, −15, 0, 0, 27 · s₁ … s₁₂ = kleinS · s 0 = 6 = 2g -/
theorem klein_newton : newton [1, 0, 0, 5, 0, 0, 8] 6 = [0, 0, -15, 0, 0, 27] ∧
    newton [1, 0, 0, 5, 0, 0, 8] 12 = (List.range 12).map (fun i => kleinS (i + 1)) ∧ kleinS 0 = 6 := by
  decide +kernel

/-- 구멍 3 · 면 : 모든 n 에서 뉴턴 점화식 s (n + 6) + 5·s (n + 3) + 8·s n = 0 (k > 6 의 뉴턴 항등식) -/
theorem klein_recursion (n : Nat) : kleinS (n + 6) + 5 * kleinS (n + 3) + 8 * kleinS n = 0 := by
  unfold kleinS
  have h1 : (n + 6) % 3 = n % 3 := by omega
  have h2 : (n + 3) % 3 = n % 3 := by omega
  have h3 : (n + 6) / 3 = n / 3 + 2 := by omega
  have h4 : (n + 3) / 3 = n / 3 + 1 := by omega
  rw [h1, h2, h3, h4]
  by_cases h : n % 3 = 0
  · simp only [h, ↓reduceIte]
    have := (lucas_step (-5) 8 (n / 3)).2
    grind
  · simp only [h, ↓reduceIte]
    decide

/-- 천장 · 바닥 · 면 (구멍 3) : N n = 2ⁿ + 1 − s n 이 n = 1 … 6 에서 3, 5, 24, 17, 33, 38 — 위의 셈과 같다 -/
theorem klein_layers : (List.range 6).map (fun i => (2 : Int) ^ (i + 1) + 1 - kleinS (i + 1)) = [3, 5, 24, 17, 33, 38] := by
  decide +kernel

/-- 바닥 ↔ 천장 (구멍 3) : c_{6−i} = 2^{3−i}·c_i · 2³T⁶·[(2T)⁶ P(1/(2T))] = (2T)⁶·P(T) · 8u² + 5u + 1 의 판별식 25 − 32 = −7 -/
theorem klein_symmetry (T : Int) : symOK 2 3 [1, 0, 0, 5, 0, 0, 8] = true ∧
    2 ^ 3 * T ^ 6 * ((2 * T) ^ 6 + 5 * (2 * T) ^ 3 + 8) = (2 * T) ^ 6 * (1 + 5 * T ^ 3 + 8 * T ^ 6) ∧
    (2 * T) ^ 6 + 5 * (2 * T) ^ 3 + 8 = 2 ^ 3 * (1 + 5 * T ^ 3 + 8 * T ^ 6) ∧ (5 : Int) ^ 2 - 4 * 8 * 1 = -7 := by
  refine ⟨by decide, by grind, by grind, by decide⟩

/-- 구멍 3 · 모든 높이 : s n² ≤ 36·2ⁿ — |N n − 2ⁿ − 1| ≤ 2g·2^{n/2} (g = 3 · 면 위 영점 여섯) 의 정수 꼴 -/
theorem klein_all_heights (n : Nat) : kleinS n ^ 2 ≤ 36 * 2 ^ n := by
  unfold kleinS
  by_cases h : n % 3 = 0
  · simp only [h, ↓reduceIte]
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    have hm : 3 * m / 3 = m := by omega
    rw [hm]
    have hb := in_box (-5) 8 (by decide) m
    have hp : (2 : Int) ^ (3 * m) = 8 ^ m := by rw [Int.pow_mul]; rfl
    grind
  · simp only [h, ↓reduceIte]
    have := Int.pow_nonneg (n := 2) (m := n) (by decide)
    grind

end Trombo.Layers

#print axioms Trombo.Layers.lucas_step
#print axioms Trombo.Layers.lucas_v_from_u
#print axioms Trombo.Layers.cassini
#print axioms Trombo.Layers.lucas_norm
#print axioms Trombo.Layers.in_box
#print axioms Trombo.Layers.count_in_box
#print axioms Trombo.Layers.functional_equation
#print axioms Trombo.Layers.newton_two
#print axioms Trombo.Layers.fields_ok
#print axioms Trombo.Layers.weier_two_smooth
#print axioms Trombo.Layers.weier_two_low
#print axioms Trombo.Layers.weier_two_f16
#print axioms Trombo.Layers.weier_three_smooth
#print axioms Trombo.Layers.weier_three_layers
#print axioms Trombo.Layers.weier_all_heights
#print axioms Trombo.Layers.line_two
#print axioms Trombo.Layers.line_three
#print axioms Trombo.Layers.klein_smooth
#print axioms Trombo.Layers.klein_counts
#print axioms Trombo.Layers.klein_count_64
#print axioms Trombo.Layers.klein_newton
#print axioms Trombo.Layers.klein_recursion
#print axioms Trombo.Layers.klein_layers
#print axioms Trombo.Layers.klein_symmetry
#print axioms Trombo.Layers.klein_all_heights

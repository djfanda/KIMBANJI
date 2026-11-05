/-
세 원소의 체 위 27 조각과 16 원수의 영인자 — 린 4 커널 확인 (Mathlib 없이, 린 코어만)

· 27 조각 : y² = x³ + a₂x² + a₄x + a₆ (aᵢ ∈ F₃) 스물일곱 가지.
  매끈함 ⇔ x³ + a₂x² + a₄x + a₆ 와 그 미분 2a₂x + a₄ 이 F₃ 안에서 함께 0 이 되는 점이 없음
  (F₃ 은 완전체라 겹근은 F₃ 안에 있다).
  매끈한 곡선마다 a = 4 − N₁ 에 대해 a² < 12 (하세 한계 |a| ≤ 2√3) 이고,
  원소 9 개 · 27 개의 체에서 센 점의 수가 제타 분자 1 − aT + 3T² 의 예측
  N₂ = 16 − a², N₃ = 28 − a³ + 9a 와 같다.
  (제타 함수가 이 꼴이라는 유리성 정리 자체는 이 파일이 증명하지 않는다 — 고전 정리 · 전언.)
· 16 원수 : 케일리–딕슨 곱 (a, b)(c, d) = (ac − d̄b, da + bc̄) 에서 (e₁ + e₁₀)(e₄ − e₁₅) = 0.

검증 : lean 린_유한체27.lean  (린 v4.34.0 · 커널 계산 decide · #print axioms 출력이 공리 목록)
-/

namespace Trombo.Field27

/-! ## 세 체의 셈 — 원소를 자연수로 적는다 -/

/-- F₃ : 0, 1, 2 -/
def add3 (k l : Nat) : Nat := (k + l) % 3
def mul3 (k l : Nat) : Nat := (k * l) % 3

/-- F₉ = F₃[i]/(i² + 1) : k = u + 3v ↔ u + v·i -/
def add9 (k l : Nat) : Nat := (k % 3 + l % 3) % 3 + 3 * ((k / 3 + l / 3) % 3)
def mul9 (k l : Nat) : Nat :=
  let u1 := k % 3; let v1 := k / 3; let u2 := l % 3; let v2 := l / 3
  (u1 * u2 + 2 * (v1 * v2)) % 3 + 3 * ((u1 * v2 + v1 * u2) % 3)

/-- F₂₇ = F₃[t]/(t³ − t − 1) : k = c₀ + 3c₁ + 9c₂ ↔ c₀ + c₁t + c₂t² ; t³ = t + 1, t⁴ = t² + t -/
def add27 (k l : Nat) : Nat :=
  (k % 3 + l % 3) % 3 + 3 * ((k / 3 % 3 + l / 3 % 3) % 3) + 9 * ((k / 9 + l / 9) % 3)
def mul27 (k l : Nat) : Nat :=
  let c0 := k % 3; let c1 := k / 3 % 3; let c2 := k / 9
  let d0 := l % 3; let d1 := l / 3 % 3; let d2 := l / 9
  let e0 := c0 * d0; let e1 := c0 * d1 + c1 * d0; let e2 := c0 * d2 + c1 * d1 + c2 * d0
  let e3 := c1 * d2 + c2 * d1; let e4 := c2 * d2
  (e0 + e3) % 3 + 3 * ((e1 + e3 + e4) % 3) + 9 * ((e2 + e4) % 3)

/-- 거듭제곱 -/
def powF (mul : Nat → Nat → Nat) (c : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => mul (powF mul c n) c

/-- 이차 지표 : 0 → 0, 제곱 → 1, 아니면 −1 (원소 q 개의 체에서 c^((q−1)/2)) -/
def chi (q : Nat) (mul : Nat → Nat → Nat) (c : Nat) : Int :=
  if c = 0 then 0 else if powF mul c ((q - 1) / 2) = 1 then 1 else -1

/-- 오른쪽 f(x) = x³ + a₂x² + a₄x + a₆ -/
def rhs (add mul : Nat → Nat → Nat) (a2 a4 a6 x : Nat) : Nat :=
  add (add (add (mul (mul x x) x) (mul a2 (mul x x))) (mul a4 x)) a6

/-- 사영 점의 수 N = q + 1 + Σₓ χ(f(x)) -/
def count (q : Nat) (add mul : Nat → Nat → Nat) (a2 a4 a6 : Nat) : Int :=
  (q : Int) + 1 + (List.range q).foldl (fun s x => s + chi q mul (rhs add mul a2 a4 a6 x)) 0

def N1 (a2 a4 a6 : Nat) : Int := count 3 add3 mul3 a2 a4 a6
def N2 (a2 a4 a6 : Nat) : Int := count 9 add9 mul9 a2 a4 a6
def N3 (a2 a4 a6 : Nat) : Int := count 27 add27 mul27 a2 a4 a6

/-- 매끈함 : f(r) = 0 이고 f'(r) = 2a₂r + a₄ = 0 인 r ∈ F₃ 이 없다 -/
def smooth (a2 a4 a6 : Nat) : Bool :=
  (List.range 3).all fun r => !(rhs add3 mul3 a2 a4 a6 r = 0 && (2 * a2 * r + a4) % 3 = 0)

/-- 27 조각 전수 : 매끈하면 a² < 12 · N₂ = 16 − a² · N₃ = 28 − a³ + 9a -/
def check27 : Bool :=
  (List.range 27).all fun k =>
    let a2 := k % 3; let a4 := k / 3 % 3; let a6 := k / 9
    if smooth a2 a4 a6 then
      let a : Int := 4 - N1 a2 a4 a6
      decide (a * a < 12) && decide (N2 a2 a4 a6 = 16 - a * a) && decide (N3 a2 a4 a6 = 28 - a * a * a + 9 * a)
    else true

def smoothCount : Nat := (List.range 27).countP fun k => smooth (k % 3) (k / 3 % 3) (k / 9)

theorem hasse_and_counts_27 : check27 = true := by decide +kernel
theorem smooth_count_18 : smoothCount = 18 := by decide +kernel
/-- y² = x³ − x : F₃ · F₉ · F₂₇ 에서 4 · 16 · 28 점 -/
theorem x3_minus_x_counts : N1 0 2 0 = 4 ∧ N2 0 2 0 = 16 ∧ N3 0 2 0 = 28 := by decide +kernel

/-! ## 16 원수의 영인자 — 케일리–딕슨 곱 -/

def conj : List Int → List Int
  | [] => []
  | a :: t => a :: t.map (fun z => -z)

/-- 길이 2ᵏ 인 두 목록의 케일리–딕슨 곱 (a, b)(c, d) = (ac − d̄b, da + bc̄) -/
def cd : Nat → List Int → List Int → List Int
  | 0, x, y => [x.headD 0 * y.headD 0]
  | k + 1, x, y =>
    let h := 2 ^ k
    let a := x.take h; let b := x.drop h; let c := y.take h; let d := y.drop h
    List.zipWith (· - ·) (cd k a c) (cd k (conj d) b) ++ List.zipWith (· + ·) (cd k d a) (cd k b (conj c))

def unit (i n : Nat) : List Int := (List.range n).map fun j => if j = i then 1 else 0

def sedX : List Int := List.zipWith (· + ·) (unit 1 16) (unit 10 16)
def sedY : List Int := List.zipWith (· - ·) (unit 4 16) (unit 15 16)

theorem sedenion_zero_divisor : cd 4 sedX sedY = List.replicate 16 0 := by decide +kernel
theorem sedenion_norms : (sedX.map fun z => z * z).foldl (· + ·) 0 = 2 ∧ (sedY.map fun z => z * z).foldl (· + ·) 0 = 2 := by
  decide +kernel

#print axioms hasse_and_counts_27
#print axioms smooth_count_18
#print axioms x3_minus_x_counts
#print axioms sedenion_zero_divisor
#print axioms sedenion_norms

/-! ## 16 원수에서 노름 곱셈이 깨진다 — 반례 하나로 «모든 x, y» 의 부정을 닫는다 -/

def normSq (x : List Int) : Int := (x.map fun z => z * z).foldl (· + ·) 0

theorem sedenion_not_composition :
    ¬ (∀ x y : List Int, normSq (cd 4 x y) = normSq x * normSq y) := by
  intro h
  have e := h sedX sedY
  revert e
  decide +kernel

#print axioms sedenion_not_composition

end Trombo.Field27

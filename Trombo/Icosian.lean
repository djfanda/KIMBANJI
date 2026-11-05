/-!
# 이십면체 이중군 (Icosian) — 푸앵카레 호몰로지 구의 기본군, 커널이 확인

고전 사실 (푸앵카레 1904): 정십이면체의 마주 보는 면을 36° 비틀어 붙인 3 차원 다양체
(푸앵카레 호몰로지 구) 의 기본군은 **이십면체 이중군** — 정이십면체 회전군의 두 겹 덮개,
원소 120 개인 단위 사원수의 군이다. 이 군은 **완전군** (교환자들이 군 전체를 낳는다) 이므로
아벨화 = H₁ = 0 이 되어 호몰로지로는 3 차원 구 S³ 와 구별되지 않지만, 군 자체는 자명하지 않다.
그래서 이것은 "호몰로지만 보는" 옛 판 추측의 반례이고, 기본군으로 말하는 푸앵카레 추측
(페렐만이 증명한 정리) 의 반례가 **아니다** — 기본군이 자명하지 않기 때문이다.

이 파일은 파이썬 계산 (`도넛_푸앵카레.py` 3 절) 을 린 커널 확인으로 바꾼다.

* 표현. 좌표 하나는 `(a + bφ)/2` (`φ² = φ + 1`) 꼴이다. 원소 `x` 대신 두 배 값 `X = 2x` 를
  황금 정수 `ℤ[φ]` 의 네 쌍 (`Q`) 으로 저장한다. 그러면 `x·y = z` 는 정수 등식
  `X·Y = 2·Z` (`hmul X Y = smul 2 Z`) 이고, 커널은 정수 산술만 한다. 나눠떨어짐은 이 등식 자체에 들어 있다.
* 목록 `S` (120 개) 는 `a = (1+i+j+k)/2` (위수 6) 와 `b = (φ + φ⁻¹i + j)/2` (위수 10) 의
  왼곱으로 1 에서 넓이 우선 탐색한 차례로 놓였다. 증명서 (부모 · 왼곱 색인 · 켤레 색인 · 교환자 증인 · 위수)
  는 `기어시운전/이십면체_증명서.py` 가 만든다. 커널은 증명서를 **확인** 할 뿐 믿지 않는다.

증명한 것 (■):
1. `S` 는 서로 다른 120 원소, 모두 노름 1 (`|X|² = 4`). 설명 (±1, ±i, ±j, ±k 8 개 ·
   (±1±i±j±k)/2 16 개 · (0, ±1, ±1/φ, ±φ)/2 의 짝치환 96 개) 과 같은 집합.
2. **곱셈 닫힘** (14,400 곱을 다 세지 않고): 1 ∈ S, `a·S ⊆ S`, `b·S ⊆ S` (240 곱) 와
   부모 차례 (`x = a·y` 또는 `b·y`, `y` 가 더 앞) 에서, 일반 정리 (ℤ[φ] 위 사원수 곱의 결합 법칙,
   `grind`) 와 강한 귀납으로 `∀ x y ∈ S, xy ∈ S` 를 끌어낸다 (`closed`).
   덤: 모든 원소는 `a`, `b` 의 낱말 (`words`).
3. 역원: 켤레 `x̄` 가 `S` 에 있고 `x·x̄ = x̄·x = 1` (`inverses`). 그래서 `S` 는 120 원소의 군 (`group`).
4. 중심: `a`, `b` 와 모두 가환인 원소는 정확히 ±1 이고, 군의 중심도 정확히 ±1 (`center`).
5. **완전군**: `a`, `b` 는 각각 `S` 원소들의 교환자 `[x, y] = x y x⁻¹ y⁻¹` 이고, 부모 차례를 따라
   **모든 원소가 교환자들의 곱** (`perfect`). 곧 아벨화 = 0, H₁ = 0.
6. 위수 분포 1:1 · 2:1 · 3:20 · 4:30 · 5:24 · 6:20 · 10:24 (`order_dist`) — 1 아닌 원소가 있으니
   군은 자명하지 않다.

정직한 범위: 다양체 쪽 (호몰로지 구의 짓기, π₁ 이 이 군이라는 것, H₁ = π₁ 의 아벨화) 은 고전 위상수학이며
여기서 **증명하지 않고** 이름만 든다. 이 파일이 확인하는 것은 120 개 사원수의 대수 사실이다.
이 파일은 어떤 미해결 문제에 대해서도 아무것도 말하지 않는다.

Core Lean 4 only: no Mathlib, no `sorry`, no `native_decide`, no `axiom`.
-/

namespace Icosian

/-! ## 황금 정수 ℤ[φ] 와 그 위의 사원수 -/

/-- 황금 정수 `a + bφ`, `φ² = φ + 1` -/
structure G where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace G
def add (x y : G) : G := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : G) : G := ⟨x.a - y.a, x.b - y.b⟩
def neg (x : G) : G := ⟨-x.a, -x.b⟩
/-- `(a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ` -/
def mul (x y : G) : G := ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩
end G

/-- `ℤ[φ]` 위의 사원수 `w + x·i + y·j + z·k` -/
structure Q where
  w : G
  x : G
  y : G
  z : G
deriving DecidableEq, Repr

/-- 짧게 쓰기 : `q a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ = (a₀ + b₀φ) + (a₁ + b₁φ)i + (a₂ + b₂φ)j + (a₃ + b₃φ)k` -/
def q (a0 b0 a1 b1 a2 b2 a3 b3 : Int) : Q := ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩

open G in
/-- 해밀턴 곱 (`i² = j² = k² = ijk = −1`), 계수는 `ℤ[φ]` -/
def hmul (p r : Q) : Q :=
  ⟨sub (sub (sub (mul p.w r.w) (mul p.x r.x)) (mul p.y r.y)) (mul p.z r.z),
   sub (add (add (mul p.w r.x) (mul p.x r.w)) (mul p.y r.z)) (mul p.z r.y),
   add (add (sub (mul p.w r.y) (mul p.x r.z)) (mul p.y r.w)) (mul p.z r.x),
   add (sub (add (mul p.w r.z) (mul p.x r.y)) (mul p.y r.x)) (mul p.z r.w)⟩

/-- 켤레 `w − xi − yj − zk` -/
def conj (p : Q) : Q := ⟨p.w, G.neg p.x, G.neg p.y, G.neg p.z⟩

/-- 정수 배 -/
def smul (c : Int) (p : Q) : Q :=
  ⟨⟨c * p.w.a, c * p.w.b⟩, ⟨c * p.x.a, c * p.x.b⟩, ⟨c * p.y.a, c * p.y.b⟩, ⟨c * p.z.a, c * p.z.b⟩⟩

/-- 노름 `w² + x² + y² + z²` (`ℤ[φ]` 안) -/
def nrm (p : Q) : G := G.add (G.add (G.add (G.mul p.w p.w) (G.mul p.x p.x)) (G.mul p.y p.y)) (G.mul p.z p.z)

/-- 1 (두 배 아님) -/
def one : Q := q 1 0 0 0 0 0 0 0
def zero : Q := q 0 0 0 0 0 0 0 0

/-! ### 일반 정리 (모든 `ℤ[φ]` 사원수에서) -/

theorem hmul_assoc (p r t : Q) : hmul (hmul p r) t = hmul p (hmul r t) := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  rcases r with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  rcases t with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, G.add, G.sub, G.mul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem smul_hmul (c : Int) (p r : Q) : hmul (smul c p) r = smul c (hmul p r) := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  rcases r with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, smul, G.add, G.sub, G.mul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem hmul_smul (c : Int) (p r : Q) : hmul p (smul c r) = smul c (hmul p r) := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  rcases r with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, smul, G.add, G.sub, G.mul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem smul_smul (c d : Int) (p : Q) : smul c (smul d p) = smul (c * d) p := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [smul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem smul_one_left (p : Q) : smul 1 p = p := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [smul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem one_hmul (p : Q) : hmul one p = p := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, one, q, G.add, G.sub, G.mul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

theorem hmul_one (p : Q) : hmul p one = p := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, one, q, G.add, G.sub, G.mul, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

/-- 실수 배 `c·1` 은 모든 원소와 가환 -/
theorem scalar_comm (c : Int) (p : Q) : hmul (smul c one) p = hmul p (smul c one) := by
  rw [smul_hmul, hmul_smul, one_hmul, hmul_one]

/-- `X · X̄ = |X|²` -/
theorem hmul_conj (p : Q) : hmul p (conj p) = ⟨nrm p, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, conj, nrm, G.add, G.sub, G.mul, G.neg, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

/-- `X̄ · X = |X|²` -/
theorem conj_hmul (p : Q) : hmul (conj p) p = ⟨nrm p, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [hmul, conj, nrm, G.add, G.sub, G.mul, G.neg, Q.mk.injEq, G.mk.injEq]
  and_intros <;> grind

/-- 2 배는 지울 수 있다 -/
theorem smul_two_cancel {p r : Q} (h : smul 2 p = smul 2 r) : p = r := by
  rcases p with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  rcases r with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
  simp only [smul, Q.mk.injEq, G.mk.injEq] at h ⊢
  omega

/-- 곱 `X₁ X₂ ⋯ Xₙ` (빈 곱 = 1) -/
def hprod : List Q → Q
  | [] => one
  | x :: l => hmul x (hprod l)

theorem hprod_append (l₁ l₂ : List Q) : hprod (l₁ ++ l₂) = hmul (hprod l₁) (hprod l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, hprod, one_hmul]
  | cons x l ih => simp only [List.cons_append, hprod, ih, hmul_assoc]

/-- 거듭제곱 `Xᵐ` -/
def hpow (p : Q) : Nat → Q
  | 0 => one
  | m + 1 => hmul p (hpow p m)

/-! ## 증명서 데이터 (`이십면체_증명서.py` 가 만듦) -/

/-- 120 원소 (두 배 값 `2x`), 1 에서 `a·` · `b·` 왼곱 넓이 우선 차례 -/
def S : List Q := [
  q 2 0 0 0 0 0 0 0,
  q 1 0 1 0 1 0 1 0,
  q 0 1 (-1) 1 1 0 0 0,
  q (-1) 0 1 0 1 0 1 0,
  q 0 0 0 1 1 0 (-1) 1,
  q 0 0 (-1) 1 0 1 1 0,
  q (-1) 1 1 0 0 1 0 0,
  q (-2) 0 0 0 0 0 0 0,
  q 0 (-1) 1 0 0 0 (-1) 1,
  q 0 (-1) (-1) 1 1 0 0 0,
  q (-1) 0 0 1 (-1) 1 0 0,
  q 0 (-1) 0 0 (-1) 1 1 0,
  q (-1) 0 0 0 0 1 (-1) 1,
  q 1 (-1) 1 0 0 1 0 0,
  q (-1) 0 (-1) 0 (-1) 0 (-1) 0,
  q 0 (-1) 1 (-1) (-1) 0 0 0,
  q 0 (-1) 0 0 1 (-1) (-1) 0,
  q 0 (-1) (-1) 1 (-1) 0 0 0,
  q 0 (-1) (-1) 0 0 0 1 (-1),
  q 0 (-1) 0 0 (-1) 1 (-1) 0,
  q 0 (-1) 1 0 0 0 1 (-1),
  q 0 (-1) 0 0 1 (-1) 1 0,
  q 0 (-1) (-1) 0 0 0 (-1) 1,
  q 0 (-1) 1 (-1) 1 0 0 0,
  q 1 0 (-1) 0 (-1) 0 (-1) 0,
  q 0 0 0 (-1) (-1) 0 1 (-1),
  q 0 0 1 (-1) 0 (-1) (-1) 0,
  q 1 (-1) (-1) 0 0 (-1) 0 0,
  q 0 0 (-1) 0 1 (-1) 0 (-1),
  q 1 (-1) 0 0 (-1) 0 0 (-1),
  q (-1) 0 0 0 0 (-1) 1 (-1),
  q (-1) 0 0 (-1) 1 (-1) 0 0,
  q 1 (-1) 0 (-1) 0 0 (-1) 0,
  q (-1) 0 1 (-1) 0 0 0 (-1),
  q (-1) 0 0 0 0 (-1) (-1) 1,
  q (-1) 0 (-1) 0 (-1) 0 1 0,
  q 0 1 (-1) 0 0 0 1 (-1),
  q 0 1 1 (-1) (-1) 0 0 0,
  q 1 0 0 (-1) 1 (-1) 0 0,
  q 0 1 0 0 1 (-1) (-1) 0,
  q 1 0 0 0 0 (-1) 1 (-1),
  q (-1) 1 (-1) 0 0 (-1) 0 0,
  q (-1) 1 0 (-1) 0 0 (-1) 0,
  q 1 0 1 (-1) 0 0 0 (-1),
  q (-1) 1 0 0 (-1) 0 0 (-1),
  q 0 0 0 (-1) (-1) 0 (-1) 1,
  q 0 0 (-2) 0 0 0 0 0,
  q 0 0 (-1) 1 0 (-1) (-1) 0,
  q 0 0 0 0 (-2) 0 0 0,
  q 0 0 1 (-1) 0 (-1) 1 0,
  q 0 1 0 0 (-1) 1 1 0,
  q 0 1 1 (-1) 1 0 0 0,
  q 0 1 1 0 0 0 (-1) 1,
  q 0 1 0 0 1 (-1) 1 0,
  q 0 1 (-1) 0 0 0 (-1) 1,
  q 0 1 0 0 (-1) 1 (-1) 0,
  q 0 1 1 0 0 0 1 (-1),
  q 0 1 (-1) 1 (-1) 0 0 0,
  q 1 0 0 (-1) (-1) 1 0 0,
  q 1 0 (-1) 0 1 0 (-1) 0,
  q 1 0 0 0 0 (-1) (-1) 1,
  q 1 0 (-1) 0 (-1) 0 1 0,
  q (-1) 1 0 (-1) 0 0 1 0,
  q 1 0 (-1) 1 0 0 0 (-1),
  q 1 0 1 0 (-1) 0 (-1) 0,
  q (-1) 1 1 0 0 (-1) 0 0,
  q 0 0 1 0 (-1) 1 0 1,
  q (-1) 1 0 0 1 0 0 1,
  q 1 0 0 0 0 1 (-1) 1,
  q 1 0 0 1 (-1) 1 0 0,
  q (-1) 1 0 1 0 0 1 0,
  q 1 0 (-1) 1 0 0 0 1,
  q 1 0 0 0 0 1 1 (-1),
  q 1 0 1 0 1 0 (-1) 0,
  q 1 0 1 (-1) 0 0 0 1,
  q 1 0 (-1) 0 1 0 1 0,
  q (-1) 1 (-1) 0 0 1 0 0,
  q 1 0 0 1 1 (-1) 0 0,
  q 1 0 1 0 (-1) 0 1 0,
  q (-1) 1 0 0 (-1) 0 0 1,
  q (-1) 1 0 0 1 0 0 (-1),
  q (-1) 1 0 1 0 0 (-1) 0,
  q 1 (-1) 0 1 0 0 1 0,
  q (-1) 0 (-1) 1 0 0 0 1,
  q 1 (-1) 0 0 1 0 0 1,
  q 0 0 0 1 1 0 1 (-1),
  q 0 0 2 0 0 0 0 0,
  q 0 0 1 (-1) 0 1 1 0,
  q 0 0 0 0 2 0 0 0,
  q 0 0 (-1) 1 0 1 (-1) 0,
  q 0 0 1 0 1 (-1) 0 1,
  q 0 0 0 0 0 0 2 0,
  q 0 0 (-1) 0 (-1) 1 0 1,
  q 0 0 0 1 (-1) 0 (-1) 1,
  q 0 0 1 (-1) 0 1 (-1) 0,
  q 0 0 1 0 (-1) 1 0 (-1),
  q (-1) 0 0 1 1 (-1) 0 0,
  q (-1) 0 1 0 (-1) 0 1 0,
  q (-1) 0 0 0 0 1 1 (-1),
  q (-1) 0 1 0 1 0 (-1) 0,
  q 1 (-1) 0 1 0 0 (-1) 0,
  q (-1) 0 1 (-1) 0 0 0 1,
  q (-1) 0 (-1) 0 1 0 1 0,
  q 1 (-1) (-1) 0 0 1 0 0,
  q 1 (-1) 0 0 (-1) 0 0 1,
  q 0 0 0 1 (-1) 0 1 (-1),
  q 0 0 0 (-1) 1 0 (-1) 1,
  q 1 (-1) 0 0 1 0 0 (-1),
  q (-1) 0 (-1) 1 0 0 0 (-1),
  q (-1) 0 1 0 (-1) 0 (-1) 0,
  q 1 (-1) 1 0 0 (-1) 0 0,
  q (-1) 0 0 (-1) (-1) 1 0 0,
  q (-1) 0 (-1) 0 1 0 (-1) 0,
  q 1 (-1) 0 (-1) 0 0 1 0,
  q 0 0 (-1) 1 0 (-1) 1 0,
  q 0 0 1 0 1 (-1) 0 (-1),
  q 0 0 (-1) 0 1 (-1) 0 1,
  q 0 0 0 (-1) 1 0 1 (-1),
  q 0 0 (-1) 0 (-1) 1 0 (-1),
  q 0 0 0 0 0 0 (-2) 0
]

/-- 부모 : `(p, f)` 이면 `x_n = g_f · x_p` (`f = false` 는 `a`, `true` 는 `b`), `p < n` -/
def parent : List (Nat × Bool) := [
  (0, false), (0, false), (0, true), (1, false), (1, true), (2, false), (2, true), (3, false), (3, true), (4, false),
  (4, true), (5, false), (6, false), (6, true), (7, false), (7, true), (8, false), (8, true), (9, false), (10, false),
  (10, true), (11, true), (12, false), (13, false), (14, false), (14, true), (15, false), (15, true), (16, false), (17, false),
  (17, true), (18, true), (19, false), (20, false), (21, true), (22, true), (24, true), (25, false), (25, true), (26, false),
  (27, false), (27, true), (28, true), (29, false), (30, false), (31, true), (32, true), (34, false), (34, true), (35, true),
  (36, false), (36, true), (37, false), (38, false), (38, true), (39, true), (40, false), (41, false), (42, true), (43, true),
  (45, false), (45, true), (46, true), (47, false), (48, false), (49, false), (50, false), (51, false), (51, true), (52, true),
  (53, false), (54, false), (55, true), (56, true), (58, false), (58, true), (59, true), (60, false), (61, false), (62, false),
  (63, true), (65, false), (66, true), (67, false), (68, false), (69, true), (70, true), (72, false), (72, true), (73, true),
  (74, false), (75, false), (76, false), (79, false), (80, true), (81, true), (82, true), (83, true), (85, false), (85, true),
  (86, true), (87, false), (88, false), (89, false), (92, false), (93, true), (94, false), (95, true), (96, false), (96, true),
  (97, true), (98, false), (99, false), (103, false), (104, true), (105, true), (106, false), (107, false), (108, false), (109, false)
]

/-- `a · x_i = x_(idxA i)` -/
def idxA : List Nat := [
  1, 3, 5, 7, 9, 11, 12, 14, 16, 18, 19, 15, 22, 23, 24, 26, 28, 29, 25, 32,
  33, 30, 27, 31, 0, 37, 39, 40, 36, 43, 44, 41, 38, 42, 47, 48, 50, 52, 53, 2,
  56, 57, 54, 51, 55, 60, 61, 63, 64, 65, 66, 67, 4, 70, 71, 68, 6, 69, 74, 75,
  77, 78, 79, 72, 73, 81, 8, 83, 84, 13, 10, 82, 87, 88, 90, 91, 92, 85, 86, 93,
  76, 89, 20, 17, 21, 98, 99, 101, 102, 103, 96, 97, 104, 100, 106, 94, 108, 109, 111, 112,
  107, 34, 35, 113, 110, 95, 116, 117, 118, 119, 115, 45, 46, 49, 105, 80, 114, 62, 58, 59
]

/-- `b · x_i = x_(idxB i)` -/
def idxB : List Nat := [
  2, 4, 6, 8, 10, 3, 13, 15, 17, 7, 20, 21, 11, 9, 25, 27, 14, 30, 31, 18,
  16, 34, 35, 22, 36, 38, 24, 41, 42, 28, 26, 45, 46, 32, 48, 49, 51, 0, 54, 55,
  39, 37, 58, 59, 43, 61, 62, 44, 40, 60, 1, 68, 69, 52, 50, 72, 73, 56, 75, 76,
  57, 53, 74, 80, 63, 64, 82, 66, 5, 85, 86, 70, 88, 89, 71, 67, 87, 81, 77, 78,
  94, 95, 96, 97, 83, 99, 100, 84, 12, 98, 93, 90, 91, 105, 103, 107, 109, 110, 23, 19,
  108, 104, 101, 102, 114, 115, 92, 112, 33, 29, 47, 113, 111, 116, 65, 119, 79, 106, 117, 118
]

/-- `x̄_i = x_(idxConj i)` -/
def idxConj : List Nat := [
  0, 24, 37, 14, 25, 26, 41, 7, 18, 15, 31, 16, 30, 27, 3, 9, 11, 23, 8, 21,
  22, 19, 20, 17, 1, 4, 5, 13, 66, 84, 12, 10, 82, 83, 98, 99, 52, 2, 69, 50,
  68, 6, 70, 71, 67, 85, 86, 87, 88, 89, 39, 57, 36, 55, 56, 53, 54, 51, 77, 78,
  72, 73, 81, 74, 75, 76, 28, 44, 40, 38, 42, 43, 60, 61, 63, 64, 65, 58, 59, 80,
  79, 62, 32, 33, 29, 45, 46, 47, 48, 49, 118, 119, 115, 117, 114, 116, 111, 112, 34, 35,
  113, 108, 109, 110, 107, 106, 105, 104, 101, 102, 103, 96, 97, 100, 94, 92, 95, 93, 90, 91
]

/-- 원소의 위수 -/
def ord : List Nat := [
  1, 6, 10, 3, 4, 4, 5, 2, 5, 5, 3, 5, 3, 10, 3, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 6, 4, 4, 10, 4, 10, 3, 3, 10, 3, 3, 3, 10, 10, 6, 10,
  6, 5, 5, 6, 5, 4, 4, 4, 4, 4, 10, 10, 10, 10, 10, 10, 10, 10, 6, 6,
  6, 6, 5, 6, 6, 5, 4, 5, 6, 6, 5, 6, 6, 6, 6, 6, 5, 6, 6, 5,
  5, 5, 10, 3, 10, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3,
  10, 3, 3, 10, 10, 4, 4, 10, 3, 3, 10, 3, 3, 10, 4, 4, 4, 4, 4, 4
]

/-- 교환자 증인 : `a = [x_2, x_58]`, `b = [x_16, x_19]` -/
def wA : Nat × Nat := (2, 58)
def wB : Nat × Nat := (16, 19)
/-- 생성원의 색인 -/
def iA : Nat := 1
def iB : Nat := 2
/-- 중심 후보의 색인 (1 · −1) -/
def iNeg : Nat := 7

/-- `i` 번째 원소의 두 배 값 `X_i = 2x_i` -/
def s (i : Nat) : Q := S.getD i zero

/-- 생성원 (두 배 값) : `gen false = 2a`, `gen true = 2b` -/
def gen (f : Bool) : Q := if f then s iB else s iA

/-- `2a = 1 + i + j + k` -/
theorem s_a : s iA = q 1 0 1 0 1 0 1 0 := by decide
/-- `2b = φ + (φ − 1)i + j` (`φ − 1 = 1/φ`) -/
theorem s_b : s iB = q 0 1 (-1) 1 1 0 0 0 := by decide
/-- 첫 원소는 1 -/
theorem s_zero : s 0 = smul 2 one := by decide
/-- `iNeg` 번째 원소는 −1 -/
theorem s_neg : s iNeg = smul (-2) one := by decide

/-! ## 1. 120 개 · 서로 다름 · 노름 1 · 설명과 같은 집합 -/

theorem card : S.length = 120 := by decide

theorem nodup : S.Nodup := by decide +kernel

/-- 모든 원소가 단위 사원수 : `|X|² = 4`, 곧 `|x|² = 1` -/
theorem norm_one : ∀ x ∈ S, nrm x = ⟨4, 0⟩ := by decide +kernel

def bools : List Bool := [false, true]
def sg (b : Bool) (x : G) : G := if b then G.neg x else x
def lst (l : List G) : Q := ⟨l.getD 0 ⟨0, 0⟩, l.getD 1 ⟨0, 0⟩, l.getD 2 ⟨0, 0⟩, l.getD 3 ⟨0, 0⟩⟩

/-- 넷의 치환 24 개 -/
def perms4 : List (List Nat) :=
  (List.range 4).flatMap fun a => (List.range 4).flatMap fun b => (List.range 4).flatMap fun c =>
    (List.range 4).filterMap fun d => if [a, b, c, d].Nodup then some [a, b, c, d] else none
/-- 뒤바뀜 수 -/
def inversions (p : List Nat) : Nat :=
  ((List.range 4).flatMap fun i => (List.range 4).filter fun j =>
    decide (i < j) && decide (p.getD j 0 < p.getD i 0)).length
/-- 짝치환 12 개 -/
def evenPerms : List (List Nat) := perms4.filter fun p => inversions p % 2 == 0

theorem perms_count : perms4.length = 24 ∧ evenPerms.length = 12 := by decide

/-- ±1, ±i, ±j, ±k (두 배 : ±2) -/
def desc8 : List Q :=
  (List.range 4).flatMap fun i => bools.map fun b =>
    lst ((List.range 4).map fun t => if t = i then sg b ⟨2, 0⟩ else ⟨0, 0⟩)
/-- (±1 ± i ± j ± k)/2 -/
def desc16 : List Q :=
  bools.flatMap fun b0 => bools.flatMap fun b1 => bools.flatMap fun b2 => bools.map fun b3 =>
    lst [sg b0 ⟨1, 0⟩, sg b1 ⟨1, 0⟩, sg b2 ⟨1, 0⟩, sg b3 ⟨1, 0⟩]
/-- (0, ±1, ±1/φ, ±φ)/2 의 짝치환 (두 배 : 0, ±1, ±(φ − 1), ±φ) -/
def desc96 : List Q :=
  bools.flatMap fun b1 => bools.flatMap fun b2 => bools.flatMap fun b3 => evenPerms.map fun p =>
    let base : List G := [⟨0, 0⟩, sg b1 ⟨1, 0⟩, sg b2 ⟨-1, 1⟩, sg b3 ⟨0, 1⟩]
    lst (p.map fun t => base.getD t ⟨0, 0⟩)
def desc : List Q := desc8 ++ desc16 ++ desc96

theorem desc_count : desc8.length = 8 ∧ desc16.length = 16 ∧ desc96.length = 96 := by decide

/-- 설명의 120 개와 `S` 는 같은 집합 -/
theorem desc_eq_S : desc.Nodup ∧ (∀ x ∈ desc, x ∈ S) ∧ (∀ x ∈ S, x ∈ desc) := by decide +kernel

/-! ## 2. 곱셈 닫힘 — 증명서 240 곱 + 부모 차례 + 결합 법칙 -/

/-- 증명서 (ii) : `a · x_i = x_(idxA i)` (120 곱) -/
theorem left_a : ∀ i, i < 120 → idxA.getD i 0 < 120 ∧ hmul (s iA) (s i) = smul 2 (s (idxA.getD i 0)) := by
  decide +kernel

/-- 증명서 (ii) : `b · x_i = x_(idxB i)` (120 곱) -/
theorem left_b : ∀ i, i < 120 → idxB.getD i 0 < 120 ∧ hmul (s iB) (s i) = smul 2 (s (idxB.getD i 0)) := by
  decide +kernel

/-- 증명서 (iii) : 1 이 아닌 원소마다 더 앞선 부모가 있다 — `x_n = g · x_p`, `p < n` -/
theorem parents : ∀ n, n < 120 → n = 0 ∨
    ((parent.getD n (0, false)).1 < n ∧
      hmul (gen (parent.getD n (0, false)).2) (s (parent.getD n (0, false)).1) = smul 2 (s n)) := by
  decide +kernel

theorem left_gen (f : Bool) (i : Nat) (hi : i < 120) : ∃ k, k < 120 ∧ hmul (gen f) (s i) = smul 2 (s k) := by
  cases f
  · exact ⟨_, (left_a i hi).1, (left_a i hi).2⟩
  · exact ⟨_, (left_b i hi).1, (left_b i hi).2⟩

/-- 부모 차례를 따른 귀납 : 1 에서 성립하고, 부모에서 자식으로 옮겨 가면 모든 원소에서 성립 -/
theorem parent_ind (P : Nat → Prop) (h0 : P 0)
    (hs : ∀ n p f, n < 120 → p < n → hmul (gen f) (s p) = smul 2 (s n) → P p → P n) :
    ∀ n, n < 120 → P n := by
  have key : ∀ N n, n ≤ N → n < 120 → P n := by
    intro N
    induction N with
    | zero => intro n hn _; have : n = 0 := by omega
              subst this; exact h0
    | succ N ih =>
      intro n hn hlt
      rcases parents n hlt with h | ⟨hp, heq⟩
      · subst h; exact h0
      · exact hs n _ _ hlt hp heq (ih _ (by omega) (by omega))
  exact fun n hn => key n n (Nat.le_refl n) hn

/-- **닫힘** : `x_i · x_j = x_k` (두 배 값으로 `X_i X_j = 2 X_k`) — 14,400 곱 모두 -/
theorem closed : ∀ i j, i < 120 → j < 120 → ∃ k, k < 120 ∧ hmul (s i) (s j) = smul 2 (s k) := by
  intro i j hi hj
  revert j
  refine parent_ind (fun i => ∀ j, j < 120 → ∃ k, k < 120 ∧ hmul (s i) (s j) = smul 2 (s k)) ?_ ?_ i hi
  · intro j hj
    exact ⟨j, hj, by rw [s_zero, smul_hmul, one_hmul]⟩
  · intro n p f _ _ heq ih j hj
    obtain ⟨k, hk, hpk⟩ := ih j hj
    obtain ⟨k', hk', hgk⟩ := left_gen f k hk
    refine ⟨k', hk', smul_two_cancel ?_⟩
    rw [← smul_hmul, ← heq, hmul_assoc, hpk, hmul_smul, hgk]

/-- 덤 : 모든 원소는 `a`, `b` 의 낱말 — `x_n = g_{f₁} ⋯ g_{fₘ}` (두 배 값으로 `2·∏ G = 2^m X_n`) -/
theorem words : ∀ n, n < 120 → ∃ w : List Bool,
    smul 2 (hprod (w.map gen)) = smul ((2 : Int) ^ w.length) (s n) := by
  refine parent_ind (fun n => ∃ w : List Bool,
    smul 2 (hprod (w.map gen)) = smul ((2 : Int) ^ w.length) (s n)) ⟨[], ?_⟩ ?_
  · simp only [List.map_nil, hprod, List.length_nil, Int.pow_zero, smul_one_left, s_zero]
  · intro n p f _ _ heq ⟨w, hw⟩
    refine ⟨f :: w, ?_⟩
    simp only [List.map_cons, hprod, List.length_cons]
    rw [← hmul_smul, hw, hmul_smul, heq, smul_smul, Int.pow_succ]

/-! ## 3. 역원 — 그래서 군 -/

/-- 켤레 색인 -/
theorem conj_mem : ∀ i, i < 120 → idxConj.getD i 0 < 120 ∧ s (idxConj.getD i 0) = conj (s i) := by
  decide +kernel

theorem s_mem (i : Nat) (hi : i < 120) : s i ∈ S := by
  have h : i < S.length := by rw [card]; exact hi
  unfold s
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- **역원** : `x̄_i ∈ S` 이고 `x_i x̄_i = x̄_i x_i = 1` -/
theorem inverses : ∀ i, i < 120 → ∃ k, k < 120 ∧ s k = conj (s i) ∧
    hmul (s i) (s k) = smul 2 (s 0) ∧ hmul (s k) (s i) = smul 2 (s 0) := by
  intro i hi
  obtain ⟨hk, hc⟩ := conj_mem i hi
  have hn := norm_one _ (s_mem i hi)
  refine ⟨_, hk, hc, ?_, ?_⟩
  · rw [hc, hmul_conj, hn, s_zero, smul_smul]; decide
  · rw [hc, conj_hmul, hn, s_zero, smul_smul]; decide

/-- **군** : 1 을 담고, 곱에 닫히고, 역원이 있고, 곱이 결합적인 120 원소 -/
theorem group :
    S.length = 120 ∧ S.Nodup ∧ s 0 = smul 2 one ∧
    (∀ i j, i < 120 → j < 120 → ∃ k, k < 120 ∧ hmul (s i) (s j) = smul 2 (s k)) ∧
    (∀ i, i < 120 → ∃ k, k < 120 ∧ hmul (s i) (s k) = smul 2 (s 0) ∧ hmul (s k) (s i) = smul 2 (s 0)) ∧
    (∀ x y z : Q, hmul (hmul x y) z = hmul x (hmul y z)) :=
  ⟨card, nodup, s_zero, closed,
   fun i hi => let ⟨k, hk, _, h1, h2⟩ := inverses i hi; ⟨k, hk, h1, h2⟩, hmul_assoc⟩

/-! ## 4. 중심 = ±1 -/

/-- `a`, `b` 와 모두 가환인 원소는 정확히 `1` (색인 0) 과 `−1` (색인 `iNeg`) -/
theorem centralizer_gens : ∀ i, i < 120 →
    ((hmul (s i) (s iA) = hmul (s iA) (s i) ∧ hmul (s i) (s iB) = hmul (s iB) (s i)) ↔
      (i = 0 ∨ i = iNeg)) := by
  decide +kernel

/-- **중심** : 모든 원소와 가환인 원소는 정확히 ±1 -/
theorem center : ∀ i, i < 120 →
    ((∀ j, j < 120 → hmul (s i) (s j) = hmul (s j) (s i)) ↔ (s i = smul 2 one ∨ s i = smul (-2) one)) := by
  intro i hi
  constructor
  · intro h
    have hA : iA < 120 := by decide
    have hB : iB < 120 := by decide
    rcases (centralizer_gens i hi).mp ⟨h iA hA, h iB hB⟩ with h0 | h7
    · subst h0; exact Or.inl s_zero
    · subst h7; exact Or.inr s_neg
  · intro h j _
    rcases h with h | h <;> rw [h, scalar_comm]

/-! ## 5. 완전군 — 모든 원소가 교환자들의 곱 (아벨화 = 0, H₁ = 0) -/

/-- 교환자 낱말 : `(i, j)` 마다 `[x_i, x_j] = x_i x_j x̄_i x̄_j` (`x̄ = x⁻¹`, 3 절) 의 네 인수 -/
def commWord (w : List (Nat × Nat)) : List Q :=
  w.flatMap fun ij => [s ij.1, s ij.2, conj (s ij.1), conj (s ij.2)]

/-- 증인 : `a = [x_2, x_58]`, `b = [x_16, x_19]` (두 배 값 : `2·∏ = 16·G`) -/
theorem comm_a : smul 2 (hprod (commWord [wA])) = smul 16 (gen false) := by decide
theorem comm_b : smul 2 (hprod (commWord [wB])) = smul 16 (gen true) := by decide

theorem comm_gen (f : Bool) : ∃ w : List (Nat × Nat), (∀ ij ∈ w, ij.1 < 120 ∧ ij.2 < 120) ∧
    smul 2 (hprod (commWord w)) = smul ((16 : Int) ^ w.length) (gen f) := by
  cases f
  · exact ⟨[wA], by decide, comm_a⟩
  · exact ⟨[wB], by decide, comm_b⟩

/-- **완전군** : 모든 원소 `x_n` 은 `S` 원소들의 교환자 곱 `∏ [x_i, x_j]`
(두 배 값으로 `2·∏ = 16^m X_n`, `m` = 교환자 수) -/
theorem perfect : ∀ n, n < 120 → ∃ w : List (Nat × Nat), (∀ ij ∈ w, ij.1 < 120 ∧ ij.2 < 120) ∧
    smul 2 (hprod (commWord w)) = smul ((16 : Int) ^ w.length) (s n) := by
  refine parent_ind (fun n => ∃ w : List (Nat × Nat), (∀ ij ∈ w, ij.1 < 120 ∧ ij.2 < 120) ∧
    smul 2 (hprod (commWord w)) = smul ((16 : Int) ^ w.length) (s n)) ⟨[], by simp, ?_⟩ ?_
  · simp only [commWord, List.flatMap_nil, hprod, List.length_nil, Int.pow_zero, smul_one_left, s_zero]
  · intro n p f _ _ heq ⟨w, hw, hpw⟩
    obtain ⟨u, hu, hgu⟩ := comm_gen f
    refine ⟨u ++ w, ?_, ?_⟩
    · intro ij hij
      rcases List.mem_append.mp hij with h | h
      · exact hu ij h
      · exact hw ij h
    · apply smul_two_cancel
      simp only [commWord, List.flatMap_append, List.length_append] at hpw hgu ⊢
      rw [hprod_append, show ∀ P W : Q, smul 2 (smul 2 (hmul P W)) = hmul (smul 2 P) (smul 2 W) from
          fun P W => by rw [smul_hmul, hmul_smul], hgu, hpw, smul_hmul, hmul_smul, heq,
        smul_smul, smul_smul, smul_smul, Int.pow_add]
      congr 1
      grind

/-! ## 6. 위수 분포 -/

/-- `ord i` 는 정말 `x_i` 의 위수 : `x^o = 1` 이고 `1 ≤ m < o` 에서 `x^m ≠ 1`
(두 배 값으로 `X^m = 2^m x^m`) -/
theorem orders : ∀ i, i < 120 → 1 ≤ ord.getD i 0 ∧
    hpow (s i) (ord.getD i 0) = smul ((2 : Int) ^ ord.getD i 0) one ∧
    ∀ m, m < ord.getD i 0 → 1 ≤ m → hpow (s i) m ≠ smul ((2 : Int) ^ m) one := by
  decide +kernel

/-- **위수 분포** 1:1 · 2:1 · 3:20 · 4:30 · 5:24 · 6:20 · 10:24 (합 120), `a` 의 위수 6, `b` 의 위수 10 -/
theorem order_dist :
    ord.length = 120 ∧
    [1, 2, 3, 4, 5, 6, 10].map (fun o => (ord.filter (· == o)).length) = [1, 1, 20, 30, 24, 20, 24] ∧
    ord.getD iA 0 = 6 ∧ ord.getD iB 0 = 10 := by
  decide

end Icosian

import Trombo.WindowBox

/-!
# 두 배 사다리 (Doubling) — 1, √2, 2, 2√2 와 케일리–딕슨 두 배 짓기

√2 사다리 1, √2, 2, 2√2 = √1, √2, √4, √8 은 네 노름 나눗셈 대수 ℝ, ℂ, ℍ, 𝕆
(차원 1, 2, 4, 8) 에서 "모든 성분이 1 인 원소" 의 크기와 정확히 같다.
이 파일은 그 고전 사실들을 **정수만으로** 적고 린 커널로 확인한다 (■).

* 노름 `N` 은 크기의 제곱 `|·|²` 이다. 그래서 `N = 1, 2, 4, 8` 이 곧 `|·| = 1, √2, 2, 2√2`.
  √ 는 해석일 뿐이고, 파일은 정수 등식만 증명한다.
* 1 부. 가우스 정수 `G` (a + bi): 두 제곱 항등식 `N (z*w) = N z * N w`,
  `(1+i)² = 2i`, `(1+i)⁴ = −4` (사다리 네 칸에 부호 뒤집힘), `(1+i)⁸ = 16`,
  `N (1+i) = 2`, 모든 k 에서 `N ((1+i)^k) = 2^k`, 그리고 `(1+i)^(k+4) = −4·(1+i)^k`.
  `(1+i)` 를 곱하는 것은 `(a, b) ↦ (a − b, a + b)` — 크기 √2 배와 45° 돌림 (해석).
* 2 부. 사원수 `H` (해밀턴 곱): 오일러 네 제곱 항등식 `N (q*r) = N q * N r`,
  결합 법칙, 비가환 증인 `i*j = k ≠ −k = j*i`, `N (1+i+j+k) = 4`,
  그리고 해밀턴 곱이 `G` 의 케일리–딕슨 두 배 곱 `(a,b)(c,d) = (ac − d̄b, da + bc̄)` 과 같음.
* 3 부. 팔원수 `O` = `H` 의 케일리–딕슨 두 배: 디건 여덟 제곱 항등식 (16 변수 정수 다항식 등식)
  과 구조판 `N (x*y) = N x * N y`, 비결합 증인, `N (1+e₁+…+e₇) = 8`.
  사다리 맞물림: `N ((1+i)^k) = N (모두-1 원소, 차원 2^k)` (k = 0, 1, 2, 3).
* 4 부. 복소 에르미트 꼴의 두 배 짓기: `z = x + iy`, `M = A + iB` 이면
  `Re (z* M z) = [x;y]ᵀ [[A, −B],[B, A]] [x;y]` — 모든 n 에서 (대칭 가정조차 없이) 성립.
  `A` 대칭 · `B` 반대칭이면 `Im (z* M z) = 0`.
  따름 정리: 두 배 실행렬이 `PSD.check` / `PSD.checkStrict` 를 통과하면 에르미트 꼴이
  `≥ 0` / `> 0`. 창 상자 (`WindowBox.box_sound`) 도 복소 상자로 옮긴다.
  견본 `M = [[2, i], [−i, 2]]` 을 `decide` 로 확인.

정직한 범위: 두·네·여덟 제곱 항등식과 케일리–딕슨 짓기는 오래된 고전 사실이며,
후르비츠 정리 (노름 나눗셈 대수는 이 넷뿐) 는 여기서 **증명하지 않고** 이름만 든다.
이 파일은 어떤 미해결 문제에 대해서도 아무것도 말하지 않는다.

Core Lean 4 only: no Mathlib, no `sorry`, no `native_decide`, no `axiom`.
-/

namespace Doubling

open PSD WindowBox

/-! ## 1 부. 가우스 정수 G = ℤ[i] — 정수의 두 배 -/

/-- 가우스 정수 `re + im·i` -/
structure G where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace G

theorem ext' {z w : G} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := by
  cases z; cases w; simp only at h1 h2; subst h1; subst h2; rfl

/-- 곱 `(a + bi)(c + di) = (ac − bd) + (ad + bc)i` -/
def mul (z w : G) : G := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
instance : Mul G := ⟨mul⟩

/-- 합 -/
def add (z w : G) : G := ⟨z.re + w.re, z.im + w.im⟩
instance : Add G := ⟨add⟩

/-- 차 -/
def sub (z w : G) : G := ⟨z.re - w.re, z.im - w.im⟩
instance : Sub G := ⟨sub⟩

@[simp] theorem mul_re (z w : G) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : G) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem add_re (z w : G) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : G) : (z + w).im = z.im + w.im := rfl
@[simp] theorem sub_re (z w : G) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : G) : (z - w).im = z.im - w.im := rfl

/-- 켤레 `a − bi` -/
def conj (z : G) : G := ⟨z.re, -z.im⟩
@[simp] theorem conj_re (z : G) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : G) : (conj z).im = -z.im := rfl

/-- 노름 `N (a + bi) = a² + b²` (= |z|²) -/
def N (z : G) : Int := z.re * z.re + z.im * z.im

/-- 1 -/
def one : G := ⟨1, 0⟩

/-- 정수 배 -/
def smul (c : Int) (z : G) : G := ⟨c * z.re, c * z.im⟩

/-- 거듭제곱 `z^k` -/
def pow (z : G) : Nat → G
  | 0 => one
  | k + 1 => pow z k * z

/-- `ω = 1 + i` — √2 사다리의 한 칸 -/
def ω : G := ⟨1, 1⟩

/-- **두 제곱 항등식** (디오판토스 · 브라마굽타 · 피보나치) — 다항식 꼴 -/
theorem two_square (a b c d : Int) :
    (a * a + b * b) * (c * c + d * d)
      = (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c) := by
  grind

/-- **노름은 곱을 지킨다**: `N (z*w) = N z * N w` -/
theorem N_mul (z w : G) : N (z * w) = N z * N w := by
  simp only [N, mul_re, mul_im]; grind

/-- 곱은 결합적 -/
theorem mul_assoc (z w u : G) : z * w * u = z * (w * u) := by
  apply ext' <;> simp only [mul_re, mul_im] <;> grind

theorem mul_one (z : G) : z * one = z := by
  apply ext' <;> simp only [mul_re, mul_im, one] <;> grind

/-- `G` 는 정수의 케일리–딕슨 두 배: 정수의 켤레는 항등이므로
`(a,b)(c,d) = (ac − d̄b, da + bc̄) = (ac − db, da + bc)` -/
theorem mul_eq_cd (z w : G) :
    z * w = ⟨z.re * w.re - w.im * z.im, w.im * z.re + z.im * w.re⟩ := by
  apply ext' <;> simp only [mul_re, mul_im] <;> grind

/-- `(1+i)` 를 곱하면 `(a, b) ↦ (a − b, a + b)` — 크기 √2 배, 45° 돌림 (해석) -/
theorem ω_mul (z : G) : z * ω = ⟨z.re - z.im, z.re + z.im⟩ := by
  apply ext' <;> simp only [mul_re, mul_im, ω] <;> grind

/-- `N (1+i) = 2` — `|1+i| = √2` -/
theorem N_ω : N ω = 2 := by decide

/-- `(1+i)² = 2i` -/
theorem ω_sq : pow ω 2 = ⟨0, 2⟩ := by decide

/-- `(1+i)³ = −2 + 2i` -/
theorem ω_cube : pow ω 3 = ⟨-2, 2⟩ := by decide

/-- `(1+i)⁴ = −4` — 사다리 네 칸 (45° × 4 = 180°) 에 부호가 뒤집힌다 -/
theorem ω_four : pow ω 4 = ⟨-4, 0⟩ := by decide

/-- `(1+i)⁸ = 16` — 여덟 칸 (360°) 에 제자리, 크기는 (√2)⁸ = 16 -/
theorem ω_eight : pow ω 8 = ⟨16, 0⟩ := by decide

/-- 모든 `k` 에서 `N ((1+i)^k) = 2^k` — `|(1+i)^k| = (√2)^k` -/
theorem N_ω_pow (k : Nat) : N (pow ω k) = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow, N_mul, ih, N_ω, Int.pow_succ]

/-- 지수 법칙 `z^(k+m) = z^k · z^m` -/
theorem pow_add (z : G) (k m : Nat) : pow z (k + m) = pow z k * pow z m := by
  induction m with
  | zero => exact (mul_one _).symm
  | succ m ih =>
    show pow z (k + m) * z = pow z k * (pow z m * z)
    rw [ih, mul_assoc]

/-- 모든 `k` 에서 `(1+i)^(k+4) = −4 · (1+i)^k` — 네 칸마다 부호 뒤집힘 -/
theorem ω_pow_add_four (k : Nat) : pow ω (k + 4) = smul (-4) (pow ω k) := by
  rw [pow_add, ω_four]
  apply ext' <;> simp only [mul_re, mul_im, smul] <;> grind

/-- 모든 `k` 에서 `(1+i)^(k+8) = 16 · (1+i)^k` — 여덟 칸마다 같은 방향 -/
theorem ω_pow_add_eight (k : Nat) : pow ω (k + 8) = smul 16 (pow ω k) := by
  rw [pow_add, ω_eight]
  apply ext' <;> simp only [mul_re, mul_im, smul] <;> grind

end G

/-! ## 2 부. 사원수 H — 가우스 정수의 두 배 -/

/-- 정수 사원수 `a + b·i + c·j + d·k` -/
structure H where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace H

theorem ext' {p q : H} (h1 : p.a = q.a) (h2 : p.b = q.b) (h3 : p.c = q.c) (h4 : p.d = q.d) :
    p = q := by
  cases p; cases q; simp only at h1 h2 h3 h4; subst h1; subst h2; subst h3; subst h4; rfl

/-- 해밀턴 곱 (`i² = j² = k² = ijk = −1`) -/
def mul (p q : H) : H :=
  ⟨p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d,
   p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c,
   p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b,
   p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a⟩
instance : Mul H := ⟨mul⟩

def add (p q : H) : H := ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d⟩
def sub (p q : H) : H := ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩
/-- 켤레 `a − bi − cj − dk` -/
def conj (p : H) : H := ⟨p.a, -p.b, -p.c, -p.d⟩

/-- 노름 `a² + b² + c² + d²` (= |q|²) -/
def N (p : H) : Int := p.a * p.a + p.b * p.b + p.c * p.c + p.d * p.d

theorem mul_def (p q : H) : p * q = mul p q := rfl

def i : H := ⟨0, 1, 0, 0⟩
def j : H := ⟨0, 0, 1, 0⟩
def k : H := ⟨0, 0, 0, 1⟩

/-- **오일러 네 제곱 항등식** — 다항식 꼴 -/
theorem four_square (a1 b1 c1 d1 a2 b2 c2 d2 : Int) :
    (a1 * a1 + b1 * b1 + c1 * c1 + d1 * d1) * (a2 * a2 + b2 * b2 + c2 * c2 + d2 * d2)
      = (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2) * (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2)
      + (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2) * (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2)
      + (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2) * (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2)
      + (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2) * (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2) := by
  grind

/-- **사원수 노름은 곱을 지킨다**: `N (p*q) = N p * N q` -/
theorem N_mul (p q : H) : N (p * q) = N p * N q := by
  simp only [mul_def, mul, N]; grind

/-- 사원수 곱은 결합적 -/
theorem mul_assoc (p q r : H) : p * q * r = p * (q * r) := by
  simp only [mul_def, mul]
  apply ext' <;> grind

/-- `i*j = k` -/
theorem i_mul_j : i * j = k := by decide
/-- `j*i = −k` -/
theorem j_mul_i : j * i = ⟨0, 0, 0, -1⟩ := by decide
/-- **비가환 증인**: `i*j ≠ j*i` -/
theorem not_comm : i * j ≠ j * i := by decide

/-- 모두-1 사원수 `1 + i + j + k` -/
def ones : H := ⟨1, 1, 1, 1⟩

/-- `N (1+i+j+k) = 4` — `|1+i+j+k| = 2` -/
theorem N_ones : N ones = 4 := by decide

/-- `q = (a + bi) + (c + di)·j` 의 두 가우스 성분 -/
def toPair (p : H) : G × G := (⟨p.a, p.b⟩, ⟨p.c, p.d⟩)

/-- 케일리–딕슨 두 배 곱 `(a,b)(c,d) = (ac − d̄b, da + bc̄)` (G 위) -/
def cdG (x y : G × G) : G × G :=
  (x.1 * y.1 - G.conj y.2 * x.2, y.2 * x.1 + x.2 * G.conj y.1)

/-- **해밀턴 곱 = G 의 케일리–딕슨 두 배 곱** -/
theorem mul_eq_cd (p q : H) : toPair (p * q) = cdG (toPair p) (toPair q) := by
  simp only [toPair, cdG, mul_def, mul, Prod.mk.injEq]
  constructor <;> apply G.ext' <;>
    simp only [G.mul_re, G.mul_im, G.sub_re, G.sub_im, G.add_re, G.add_im,
      G.conj_re, G.conj_im] <;> grind

/-- 두 배의 노름은 두 노름의 합: `N (z + w·j) = N z + N w` -/
theorem N_toPair (p : H) : N p = G.N (toPair p).1 + G.N (toPair p).2 := by
  simp only [N, G.N, toPair]; grind

end H

/-! ## 3 부. 팔원수 O — 사원수의 두 배 -/

/-- 정수 팔원수 `lo + hi·ℓ` (`lo hi : H`) — 성분 `1, e₁, …, e₇` -/
structure O where
  lo : H
  hi : H
deriving DecidableEq, Repr

namespace O

/-- 케일리–딕슨 곱 `(a,b)(c,d) = (ac − d̄b, da + bc̄)` -/
def mul (x y : O) : O :=
  ⟨H.sub (H.mul x.lo y.lo) (H.mul (H.conj y.hi) x.hi),
   H.add (H.mul y.hi x.lo) (H.mul x.hi (H.conj y.lo))⟩
instance : Mul O := ⟨mul⟩

theorem mul_def (x y : O) : x * y = mul x y := rfl

/-- 노름 `N (a, b) = N a + N b` — 여덟 제곱의 합 -/
def N (x : O) : Int := H.N x.lo + H.N x.hi

/-- **디건 여덟 제곱 항등식** — 16 변수 정수 다항식 등식 -/
theorem eight_square (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : Int) :
    (x0^2 + x1^2 + x2^2 + x3^2 + x4^2 + x5^2 + x6^2 + x7^2) *
      (y0^2 + y1^2 + y2^2 + y3^2 + y4^2 + y5^2 + y6^2 + y7^2) =
      (x0*y0 - x1*y1 - x2*y2 - x3*y3 - x4*y4 - x5*y5 - x6*y6 - x7*y7)^2 +
      (x0*y1 + x1*y0 + x2*y3 - x3*y2 + x4*y5 - x5*y4 - x6*y7 + x7*y6)^2 +
      (x0*y2 - x1*y3 + x2*y0 + x3*y1 + x4*y6 + x5*y7 - x6*y4 - x7*y5)^2 +
      (x0*y3 + x1*y2 - x2*y1 + x3*y0 + x4*y7 - x5*y6 + x6*y5 - x7*y4)^2 +
      (x0*y4 - x1*y5 - x2*y6 - x3*y7 + x4*y0 + x5*y1 + x6*y2 + x7*y3)^2 +
      (x0*y5 + x1*y4 - x2*y7 + x3*y6 - x4*y1 + x5*y0 - x6*y3 + x7*y2)^2 +
      (x0*y6 + x1*y7 + x2*y4 - x3*y5 - x4*y2 + x5*y3 + x6*y0 - x7*y1)^2 +
      (x0*y7 - x1*y6 + x2*y5 + x3*y4 - x4*y3 - x5*y2 + x6*y1 + x7*y0)^2 := by
  grind

/-- **팔원수 노름은 곱을 지킨다** (구조판): `N (x*y) = N x * N y` -/
theorem N_mul (x y : O) : N (x * y) = N x * N y := by
  simp only [mul_def, mul, N, H.N, H.mul, H.add, H.sub, H.conj]
  grind

/-- 단위 `e₁ = (i, 0)`, `e₂ = (j, 0)`, `e₄ = (0, 1)` -/
def e1 : O := ⟨H.i, ⟨0, 0, 0, 0⟩⟩
def e2 : O := ⟨H.j, ⟨0, 0, 0, 0⟩⟩
def e4 : O := ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩

/-- **비결합 증인**: `(e₁e₂)e₄ ≠ e₁(e₂e₄)` -/
theorem not_assoc : (e1 * e2) * e4 ≠ e1 * (e2 * e4) := by decide

/-- 모두-1 팔원수 `1 + e₁ + … + e₇` -/
def ones : O := ⟨H.ones, H.ones⟩

/-- `N (1 + e₁ + … + e₇) = 8` — `|·| = √8 = 2√2` -/
theorem N_ones : N ones = 8 := by decide

end O

/-! ### 사다리 맞물림 -/

/-- 모두-1 원소의 노름: ℝ·ℂ·ℍ·𝕆 에서 `1, 2, 4, 8 = 2⁰, 2¹, 2², 2³` (크기 `1, √2, 2, 2√2`) -/
theorem ladder :
    (1 : Int) * 1 = 2 ^ 0 ∧ G.N G.ω = 2 ^ 1 ∧ H.N H.ones = 2 ^ 2 ∧ O.N O.ones = 2 ^ 3 := by
  decide

/-- `(1+i)` 를 `k` 번 곱한 크기 = 차원 `2^k` 모두-1 원소의 크기 (k = 0, 1, 2, 3) -/
theorem ladder_meets :
    G.N (G.pow G.ω 0) = 1 * 1 ∧ G.N (G.pow G.ω 1) = G.N G.ω ∧
    G.N (G.pow G.ω 2) = H.N H.ones ∧ G.N (G.pow G.ω 3) = O.N O.ones := by
  decide

/-- 두 배 짓기에서 대각 `(x, x)` 의 노름은 두 배 -/
theorem double_diag_G (a : Int) : G.N ⟨a, a⟩ = 2 * (a * a) := by
  simp only [G.N]; grind
theorem double_diag_H (z : G) : H.N ⟨z.re, z.im, z.re, z.im⟩ = 2 * G.N z := by
  simp only [H.N, G.N]; grind
theorem double_diag_O (p : H) : O.N ⟨p, p⟩ = 2 * H.N p := by
  simp only [O.N]; grind

/-! ## 4 부. 복소 에르미트 꼴 = 두 배 크기의 실 이차 꼴 -/

/-- 복소 행렬 `M = A + iB` -/
def cmat (A B : Nat → Nat → Int) : Nat → Nat → G := fun i j => ⟨A i j, B i j⟩

/-- `Re (z* M z) = Σ_i Σ_j Re (conj z_i · M_ij · z_j)` -/
def hRe (n : Nat) (M : Nat → Nat → G) (z : Nat → G) : Int :=
  sum n (fun i => sum n (fun j => (G.conj (z i) * M i j * z j).re))

/-- `Im (z* M z)` -/
def hIm (n : Nat) (M : Nat → Nat → G) (z : Nat → G) : Int :=
  sum n (fun i => sum n (fun j => (G.conj (z i) * M i j * z j).im))

/-- 두 배 실행렬 `[[A, −B], [B, A]]` (2n × 2n) -/
def dbl (n : Nat) (A B : Nat → Nat → Int) : Nat → Nat → Int := fun i j =>
  if i < n then (if j < n then A i j else -B i (j - n))
  else (if j < n then B (i - n) j else A (i - n) (j - n))

/-- 쌓은 벡터 `[x; y]` -/
def stack (n : Nat) (x y : Nat → Int) : Nat → Int := fun k =>
  if k < n then x k else y (k - n)

theorem sum_append (n m : Nat) (f : Nat → Int) :
    sum (n + m) f = sum n f + sum m (fun k => f (n + k)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 from rfl, sum_succ, ih, sum_succ]
    omega

theorem sum_neg (n : Nat) (f : Nat → Int) : sum n (fun k => -f k) = -sum n f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_succ, ih]; omega

/-- **두 배 짓기 항등식**: 모든 `n`, 모든 정수 `A, B, x, y` 에서
`Re ((x+iy)* (A+iB) (x+iy)) = [x;y]ᵀ [[A, −B],[B, A]] [x;y]`. -/
theorem doubling (n : Nat) (A B : Nat → Nat → Int) (x y : Nat → Int) :
    hRe n (cmat A B) (fun k => ⟨x k, y k⟩) = quad (n + n) (dbl n A B) (stack n x y) := by
  unfold quad hRe
  rw [sum_append]
  simp only [sum_append]
  rw [← sum_add]
  apply sum_congr; intro i hi
  rw [← sum_add, ← sum_add, ← sum_add]
  apply sum_congr; intro j hj
  have h1 : ¬ (n + i < n) := by omega
  have h2 : ¬ (n + j < n) := by omega
  simp only [dbl, stack, cmat, hi, hj, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left,
    G.mul_re, G.mul_im, G.conj_re, G.conj_im]
  grind

/-- 반대칭 이중합은 0 -/
theorem sum_antisym (n : Nat) (f : Nat → Nat → Int) (h : ∀ i j, f j i = -f i j) :
    sum n (fun i => sum n (fun j => f i j)) = 0 := by
  have e := sum_comm n n f
  have e2 : sum n (fun j => sum n (fun i => f i j))
      = -sum n (fun i => sum n (fun j => f i j)) := by
    rw [← sum_neg]
    apply sum_congr; intro i _
    rw [← sum_neg]
    apply sum_congr; intro j _
    exact h i j
  omega

/-- **에르미트이면 실수**: `A` 대칭 · `B` 반대칭이면 `Im (z* M z) = 0` -/
theorem hIm_zero (n : Nat) (A B : Nat → Nat → Int) (hA : ∀ i j, A j i = A i j)
    (hB : ∀ i j, B j i = -B i j) (z : Nat → G) : hIm n (cmat A B) z = 0 := by
  unfold hIm
  apply sum_antisym
  intro i j
  simp only [cmat, G.mul_re, G.mul_im, G.conj_re, G.conj_im]
  rw [hA i j, hB i j]
  grind

/-- **따름 정리 (반정치)**: 두 배 실행렬의 인증서가 `PSD.check` 를 통과하면
모든 복소 벡터 `z` 에서 `Re (z* M z) ≥ 0`. -/
theorem herm_psd (C : Cert) (hC : check C = true) (n : Nat) (A B : Nat → Nat → Int)
    (hn : C.n = n + n)
    (hmat : ∀ i, i < n + n → ∀ j, j < n + n → C.mat i j = dbl n A B i j) :
    ∀ z : Nat → G, 0 ≤ hRe n (cmat A B) z := by
  intro z
  have h0 := sound C hC (stack n (fun k => (z k).re) (fun k => (z k).im))
  rw [hn, quad_congr hmat, ← doubling] at h0
  exact h0

theorem stack_nonzero (n : Nat) (z : Nat → G)
    (hz : ∃ k, k < n ∧ ((z k).re ≠ 0 ∨ (z k).im ≠ 0)) :
    ∃ k, k < n + n ∧ stack n (fun k => (z k).re) (fun k => (z k).im) k ≠ 0 := by
  obtain ⟨k, hk, h | h⟩ := hz
  · exact ⟨k, by omega, by simp only [stack, hk, ↓reduceIte]; exact h⟩
  · refine ⟨n + k, by omega, ?_⟩
    have h1 : ¬ (n + k < n) := by omega
    simp only [stack, h1, ↓reduceIte, Nat.add_sub_cancel_left]
    exact h

/-- **따름 정리 (양정치)**: 엄격 검사기를 통과하면 `z ≠ 0` 에서 `Re (z* M z) > 0`. -/
theorem herm_pd (C : Cert) (hC : checkStrict C = true) (n : Nat) (A B : Nat → Nat → Int)
    (hn : C.n = n + n)
    (hmat : ∀ i, i < n + n → ∀ j, j < n + n → C.mat i j = dbl n A B i j) :
    ∀ z : Nat → G, (∃ k, k < n ∧ ((z k).re ≠ 0 ∨ (z k).im ≠ 0)) →
      0 < hRe n (cmat A B) z := by
  intro z hz
  have h0 := sound_strict C hC (stack n (fun k => (z k).re) (fun k => (z k).im))
    (by rw [hn]; exact stack_nonzero n z hz)
  rw [hn, quad_congr hmat, ← doubling] at h0
  exact h0

theorem iabs_neg (a : Int) : iabs (-a) = iabs a := by unfold iabs; omega

/-- **복소 창 상자**: 가운데 `A₀ + iB₀`, 반지름 `e` 의 상자
(`|A − A₀| ≤ e`, `|B − B₀| ≤ e` 성분마다) 안의 모든 `A + iB` 에서 `Re (z* M z) ≥ 0` —
두 배 실행렬 `dbl A₀ B₀ − 2n·e·I` 의 인증서 하나로 (`WindowBox.box_sound` 를 두 배 크기에 적용). -/
theorem herm_box_sound (C : Cert) (hC : check C = true) (n : Nat)
    (A0 B0 : Nat → Nat → Int) (e : Int) (he : 0 ≤ e) (hn : C.n = n + n)
    (hmat : ∀ i, i < n + n → ∀ j, j < n + n →
      C.mat i j = dbl n A0 B0 i j - (if i = j then ((n + n : Nat) : Int) * e else 0))
    (A B : Nat → Nat → Int)
    (hA : ∀ i, i < n → ∀ j, j < n → iabs (A i j - A0 i j) ≤ e)
    (hB : ∀ i, i < n → ∀ j, j < n → iabs (B i j - B0 i j) ≤ e) :
    ∀ z : Nat → G, 0 ≤ hRe n (cmat A B) z := by
  intro z
  have hM : ∀ i, i < n + n → ∀ j, j < n + n → iabs (dbl n A B i j - dbl n A0 B0 i j) ≤ e := by
    intro i hi j hj
    unfold dbl
    by_cases hi' : i < n <;> by_cases hj' : j < n <;>
      simp only [hi', hj', ↓reduceIte]
    · exact hA i hi' j hj'
    · rw [show -B i (j - n) - -B0 i (j - n) = -(B i (j - n) - B0 i (j - n)) by omega, iabs_neg]
      exact hB i hi' (j - n) (by omega)
    · exact hB (i - n) (by omega) j hj'
    · exact hA (i - n) (by omega) (j - n) (by omega)
  have h0 := box_sound C hC (n + n) (dbl n A0 B0) e he hn hmat (dbl n A B) hM
    (stack n (fun k => (z k).re) (fun k => (z k).im))
  rw [← doubling] at h0
  exact h0

/-! ### 견본: `M = [[2, i], [−i, 2]]` (고윳값 1, 3) -/

/-- 실수부 `A = [[2,0],[0,2]]` -/
def A2 : Nat → Nat → Int := fun i j => if i = j then 2 else 0
/-- 허수부 `B = [[0,1],[−1,0]]` -/
def B2 : Nat → Nat → Int := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

/-- 두 배 실행렬 `[[2,0,0,−1],[0,2,1,0],[0,1,2,0],[−1,0,0,2]]` 의 뒤집은 LDLᵀ 인증서:
`2·D = 3·e₀e₀ᵀ + 3·e₁e₁ᵀ + (0,1,2,0)(…)ᵀ + (−1,0,0,2)(…)ᵀ` -/
def certHerm2 : Cert where
  n := 4
  A := [[2, 0, 0, -1], [0, 2, 1, 0], [0, 1, 2, 0], [-1, 0, 0, 2]]
  c := 2
  rows := [(3, [1, 0, 0, 0]), (3, [0, 1, 0, 0]), (1, [0, 1, 2, 0]), (1, [-1, 0, 0, 2])]

theorem demo_check : check certHerm2 = true := by decide
theorem demo_strict : checkStrict certHerm2 = true := by decide

theorem demo_mat : ∀ i, i < 2 + 2 → ∀ j, j < 2 + 2 → certHerm2.mat i j = dbl 2 A2 B2 i j := by
  decide

theorem demo_hermitian : ∀ z : Nat → G, hIm 2 (cmat A2 B2) z = 0 :=
  hIm_zero 2 A2 B2 (fun i j => by unfold A2; by_cases h : i = j <;> simp [h, eq_comm])
    (fun i j => by unfold B2; by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      by_cases h2 : j = 0 <;> by_cases h3 : j = 1 <;> simp_all)

/-- 모든 `z ∈ ℤ[i]²` 에서 `z* M z ≥ 0` -/
theorem demo_psd : ∀ z : Nat → G, 0 ≤ hRe 2 (cmat A2 B2) z :=
  herm_psd certHerm2 demo_check 2 A2 B2 rfl demo_mat

/-- `z ≠ 0` 이면 `z* M z > 0` -/
theorem demo_pd : ∀ z : Nat → G, (∃ k, k < 2 ∧ ((z k).re ≠ 0 ∨ (z k).im ≠ 0)) →
    0 < hRe 2 (cmat A2 B2) z :=
  herm_pd certHerm2 demo_strict 2 A2 B2 rfl demo_mat

/-- 직접 셈: `z = (1, i)` 에서 `z* M z = 2` -/
theorem demo_value :
    hRe 2 (cmat A2 B2) (fun k => if k = 0 then ⟨1, 0⟩ else ⟨0, 1⟩) = 2 := by decide

end Doubling

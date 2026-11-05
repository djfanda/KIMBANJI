import Mathlib.Tactic.Ring
/-! 쌍고리 몫 가족의 거울 정리 (모든 a).
E₁(a) : y² = x³ − 3x² + (−6a−12)x + (a²+20a+36)   (= w² = (u+2)(u³−3u+a) 의 바이어슈트라스 꼴)
P = (4, a−2) 은 위수 3 점, 벨루 몫 Q(a) : y² = x³ − 3x² + (54a−132)x + (−27a²+324a−460).
정리: c₄(E₁(−a)) = c₄(Q)/9, c₆(E₁(−a)) = −c₆(Q)/27 — 곧 E₁(−a) 는 Q(a) 의 꼬임 인자 d = −1/3 ≡ −3 (mod 제곱) 꼬임. -/
namespace Kimbanji.MirrorTwist

def b2 (a2 : ℤ) : ℤ := 4*a2
def c4 (a2 a4 : ℤ) : ℤ := (4*a2)^2 - 24*(2*a4)
def c6 (a2 a4 a6 : ℤ) : ℤ := -(4*a2)^3 + 36*(4*a2)*(2*a4) - 216*(4*a6)

/-- E₁(a) 의 계수 -/
def eA4 (a : ℤ) : ℤ := -6*a - 12
def eA6 (a : ℤ) : ℤ := a^2 + 20*a + 36
/-- 벨루 몫의 계수 -/
def qA4 (a : ℤ) : ℤ := 54*a - 132
def qA6 (a : ℤ) : ℤ := -27*a^2 + 324*a - 460

/-- P = (4, a−2) 가 E₁(a) 위에 있다. -/
theorem P_on_curve (a : ℤ) : (a-2)^2 = 4^3 + (-3)*4^2 + eA4 a * 4 + eA6 a := by
  unfold eA4 eA6; ring

/-- P 는 3-분할 다항식 ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈ 의 근 (x = 4). -/
theorem P_order_three (a : ℤ) :
    3*4^4 + (4*(-3))*4^3 + 3*(2*eA4 a)*4^2 + 3*(4*eA6 a)*4
      + (4*(-3)*eA6 a - (eA4 a)^2) = 0 := by
  unfold eA4 eA6; ring

/-- 벨루 공식: A₄ = a₄ − 5v, A₆ = a₆ − 4a₂v − 7w, v = 2(3x_P²+2a₂x_P+a₄), w = 4y_P² + x_P v. -/
theorem velu (a : ℤ) :
    qA4 a = eA4 a - 5*(2*(3*4^2 + 2*(-3)*4 + eA4 a)) ∧
    qA6 a = eA6 a - 4*(-3)*(2*(3*4^2 + 2*(-3)*4 + eA4 a))
              - 7*(4*(a-2)^2 + 4*(2*(3*4^2 + 2*(-3)*4 + eA4 a))) := by
  unfold qA4 qA6 eA4 eA6; constructor <;> ring

/-- 거울 정리: E₁(−a) 의 c₄, c₆ 는 몫 Q(a) 의 것의 d², d³ 배, d = −1/3. -/
theorem mirror_twist (a : ℤ) :
    9 * c4 (-3) (eA4 (-a)) = c4 (-3) (qA4 a) ∧
    -27 * c6 (-3) (eA4 (-a)) (eA6 (-a)) = c6 (-3) (qA4 a) (qA6 a) := by
  unfold c4 c6 eA4 eA6 qA4 qA6; constructor <;> ring

end Kimbanji.MirrorTwist

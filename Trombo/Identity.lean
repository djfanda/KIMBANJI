/-
두 · 네 · 여덟 제곱 항등식 — 모든 정수에서 (린 4 코어 · grind)
두 제곱 = 복소수의 노름 곱셈 · 네 제곱 = 사원수(오일러) · 여덟 제곱 = 팔원수(23.1 절의 케일리–딕슨 곱을 성분으로 펼친 꼴)
-/

namespace Trombo.Identity

theorem two_sq (a b c d : Int) :
    (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 := by grind

theorem four_sq (a1 a2 a3 a4 b1 b2 b3 b4 : Int) :
    (a1^2 + a2^2 + a3^2 + a4^2) * (b1^2 + b2^2 + b3^2 + b4^2) =
      (a1*b1 - a2*b2 - a3*b3 - a4*b4)^2 + (a1*b2 + a2*b1 + a3*b4 - a4*b3)^2 +
      (a1*b3 - a2*b4 + a3*b1 + a4*b2)^2 + (a1*b4 + a2*b3 - a3*b2 + a4*b1)^2 := by grind

#print axioms two_sq
#print axioms four_sq

end Trombo.Identity

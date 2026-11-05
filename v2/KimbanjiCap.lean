import Mathlib
/-! AG(2,3) 의 반대쌍 없는 4-모자 불가 (부호 형태). 0 아닌 여덟 점은 원점을 지나는 네 직선
    {±(1,0)}, {±(0,1)}, {±(1,1)}, {±(1,2)} 위에 있으므로 반대쌍 없는 네 점은 (전체 부호를 맞춘 뒤)
    (1,0), s₂(0,1), s₃(1,1), s₄(1,2) 꼴이다. 부호 s ∈ {1, 2} 의 모든 경우에 세 점 합이 0. -/
namespace Kimbanji.Cap
theorem cap4_signs : ∀ s2 s3 s4 : ZMod 3, s2 ≠ 0 → s3 ≠ 0 → s4 ≠ 0 →
    let a : ZMod 3 × ZMod 3 := (1, 0)
    let b : ZMod 3 × ZMod 3 := (0, s2)
    let c : ZMod 3 × ZMod 3 := (s3, s3)
    let d : ZMod 3 × ZMod 3 := (s4, 2 * s4)
    a + b + c = 0 ∨ a + b + d = 0 ∨ a + c + d = 0 ∨ b + c + d = 0 := by decide
/-- D₂(ℤ/3) 쪽 조각: ℤ/3 의 0 아닌 세 원소는 영합 부분을 갖는다(같은 셋 3g = 0, 아니면 g + (−g) = 0). -/
theorem zs3 : ∀ a b c : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    a + b = 0 ∨ a + c = 0 ∨ b + c = 0 ∨ a + b + c = 0 := by decide
end Kimbanji.Cap
#print axioms Kimbanji.Cap.cap4_signs
#print axioms Kimbanji.Cap.zs3

/-
Π₁ 문장의 뼈대 — «모든 n 에서 P n» (P 는 결정 가능) 꼴의 문장은, 반박할 수 없으면 참이다.
가정 하나 : 거짓인 사례 n 이 있으면 그 사례가 «모든 n 에서 P n» 의 부정을 증명한다(Σ₁ 완전성 — 표준 메타정리, 이 파일 밖).
리만 가설은 이 꼴의 문장과 같다(데이비스–마티야세비치–로빈슨 1976 · 라가리아스 2002 — 이 파일 밖의 정리).
그래서 리만 가설에 대해 «증명할 수 없다» 는 증명은 곧 «참이다» 의 증명이 된다.
-/

namespace Trombo.PiOne

theorem pi1_unrefutable_is_true (P : Nat → Prop) [DecidablePred P] (Provable : Prop → Prop)
    (sigma1 : ∀ n, ¬ P n → Provable (¬ ∀ m, P m))
    (unrefutable : ¬ Provable (¬ ∀ m, P m)) : ∀ m, P m := by
  intro m
  by_cases h : P m
  · exact h
  · exact absurd (sigma1 m h) unrefutable

/-- 거꾸로 : 거짓이면 반례가 있고, 그 반례는 결정 절차로 확인된다 -/
theorem pi1_false_has_witness (P : Nat → Prop) [DecidablePred P] (h : ¬ ∀ m, P m) : ∃ n, ¬ P n := by
  apply Classical.byContradiction
  intro hn
  exact h (fun m => Decidable.byContradiction (fun hm => hn ⟨m, hm⟩))

#print axioms pi1_unrefutable_is_true
#print axioms pi1_false_has_witness

end Trombo.PiOne

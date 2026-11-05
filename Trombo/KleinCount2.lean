import Trombo.KleinCount

/-!
클라인 4 차 곡선의 점 세기 — 둘째 묶음 : 167 ≤ p < 307 의 커널 확인

정의 · 건전성 정리 · 머리말 (증명하지 않은 고전 사실의 이름, 유한 범위만 확인한다는 한계) 은
`Trombo.KleinCount` 에 있다. 커널 확인 하나가 메모리를 2 GB 넘게 쓰므로 모듈을 나눴다.
-/
namespace Trombo.KleinCount

-- 커널 확인을 한 번에 하나씩 하도록 병렬 정교화를 끈다 (메모리 상한 때문)
set_option Elab.async false

theorem chunk_167_211 : checkFrom 167 44 = true := by decide +kernel
theorem chunk_211_239 : checkFrom 211 28 = true := by decide +kernel
theorem chunk_239_263 : checkFrom 239 24 = true := by decide +kernel
theorem chunk_263_281 : checkFrom 263 18 = true := by decide +kernel
theorem chunk_281_307 : checkFrom 281 26 = true := by decide +kernel

end Trombo.KleinCount

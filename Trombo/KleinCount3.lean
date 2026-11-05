import Trombo.KleinCount2

/-!
클라인 4 차 곡선의 점 세기 — 셋째 묶음 : 307 ≤ p < 400 의 커널 확인과 모아 놓은 정리

`klein_count_lt_400` : 2 ≤ p < 400 인 모든 소수 p ≠ 7 (77 개) 에서
    #C(F_p) = p + 1 − a_p(E) · (1 + χ(p) + χ(p)²) .
이것은 유한 범위의 확인일 뿐이다. 야코비안의 분해 (고전 사실) 는 여기서 증명하지 않으며,
모든 소수에 대한 등식도, 호지 추측도 다루지 않는다. 자세한 것은 `Trombo.KleinCount` 의 머리말.
-/
namespace Trombo.KleinCount

-- 커널 확인을 한 번에 하나씩 하도록 병렬 정교화를 끈다 (메모리 상한 때문)
set_option Elab.async false

theorem chunk_307_317 : checkFrom 307 10 = true := by decide +kernel
theorem chunk_317_337 : checkFrom 317 20 = true := by decide +kernel
theorem chunk_337_349 : checkFrom 337 12 = true := by decide +kernel
theorem chunk_349_359 : checkFrom 349 10 = true := by decide +kernel
theorem chunk_359_373 : checkFrom 359 14 = true := by decide +kernel
theorem chunk_373_383 : checkFrom 373 10 = true := by decide +kernel
theorem chunk_383_397 : checkFrom 383 14 = true := by decide +kernel
theorem chunk_397_400 : checkFrom 397 3 = true := by decide +kernel

/-- 2 ≤ p < 400 인 모든 소수 p ≠ 7 에서 #C(F_p) = p + 1 − a_p(E) · (1 + χ(p) + χ(p)²) -/
theorem klein_count_lt_400 (p : Nat) (hp : Prime p) (hlt : p < 400) (h7 : p ≠ 7) :
    (kleinN p : Int) = (p : Int) + 1 - ap p * chiSumInt p := by
  have h2 := hp.1
  by_cases h167 : p < 167
  · exact checkFrom_sound 2 165 chunk_2_167 p (by omega) (by omega) hp h7
  by_cases h211 : p < 211
  · exact checkFrom_sound 167 44 chunk_167_211 p (by omega) (by omega) hp h7
  by_cases h239 : p < 239
  · exact checkFrom_sound 211 28 chunk_211_239 p (by omega) (by omega) hp h7
  by_cases h263 : p < 263
  · exact checkFrom_sound 239 24 chunk_239_263 p (by omega) (by omega) hp h7
  by_cases h281 : p < 281
  · exact checkFrom_sound 263 18 chunk_263_281 p (by omega) (by omega) hp h7
  by_cases h307 : p < 307
  · exact checkFrom_sound 281 26 chunk_281_307 p (by omega) (by omega) hp h7
  by_cases h317 : p < 317
  · exact checkFrom_sound 307 10 chunk_307_317 p (by omega) (by omega) hp h7
  by_cases h337 : p < 337
  · exact checkFrom_sound 317 20 chunk_317_337 p (by omega) (by omega) hp h7
  by_cases h349 : p < 349
  · exact checkFrom_sound 337 12 chunk_337_349 p (by omega) (by omega) hp h7
  by_cases h359 : p < 359
  · exact checkFrom_sound 349 10 chunk_349_359 p (by omega) (by omega) hp h7
  by_cases h373 : p < 373
  · exact checkFrom_sound 359 14 chunk_359_373 p (by omega) (by omega) hp h7
  by_cases h383 : p < 383
  · exact checkFrom_sound 373 10 chunk_373_383 p (by omega) (by omega) hp h7
  by_cases h397 : p < 397
  · exact checkFrom_sound 383 14 chunk_383_397 p (by omega) (by omega) hp h7
  exact checkFrom_sound 397 3 chunk_397_400 p (by omega) (by omega) hp h7

/-- 같은 등식을 ℤ[ω] 값의 χ 로 : #C(F_p) = p + 1 − a_p (1 + χ(p) + χ(p)²) -/
theorem klein_count_lt_400_eis (p : Nat) (hp : Prime p) (hlt : p < 400) (h7 : p ≠ 7) :
    Eis.ofInt (kleinN p) = (Eis.ofInt ((p : Int) + 1)).add (Eis.neg (Eis.mul (Eis.ofInt (ap p)) (chiSum p))) :=
  eis_of_int p (mod7_ne_zero hp h7) (klein_count_lt_400 p hp hlt h7)

end Trombo.KleinCount

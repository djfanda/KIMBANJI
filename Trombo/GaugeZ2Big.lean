/-
3 × 3 원환면 Z₂ 격자 게이지 — 고리 배치 2^18 = 262,144 가지 전부를 서른두 토막 (바깥 줄 16 개씩) 으로 나누어 커널이 셈.
토막마다 «음의 판 수» 막대 그림 (칸 k 는 2^{20k} 자리) 을 확인하고, 서른두 토막의 합이 정확한 답 expect 9
(칸 k 에 2^10 · C(9, k), k 짝수) 과 같음을 보인다. 토막을 나눈 까닭은 메모리 (한 토막 약 1.8 GB).
-/
import Trombo.GaugeZ2
set_option Elab.async false
namespace GaugeZ2

theorem chunk_0 : histChunk 3 3 0 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_1 : histChunk 3 3 16 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_2 : histChunk 3 3 32 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_3 : histChunk 3 3 48 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_4 : histChunk 3 3 64 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_5 : histChunk 3 3 80 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_6 : histChunk 3 3 96 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_7 : histChunk 3 3 112 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_8 : histChunk 3 3 128 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_9 : histChunk 3 3 144 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_10 : histChunk 3 3 160 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_11 : histChunk 3 3 176 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_12 : histChunk 3 3 192 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_13 : histChunk 3 3 208 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_14 : histChunk 3 3 224 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_15 : histChunk 3 3 240 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_16 : histChunk 3 3 256 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_17 : histChunk 3 3 272 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_18 : histChunk 3 3 288 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_19 : histChunk 3 3 304 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_20 : histChunk 3 3 320 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_21 : histChunk 3 3 336 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_22 : histChunk 3 3 352 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_23 : histChunk 3 3 368 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_24 : histChunk 3 3 384 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_25 : histChunk 3 3 400 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_26 : histChunk 3 3 416 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_27 : histChunk 3 3 432 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_28 : histChunk 3 3 448 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_29 : histChunk 3 3 464 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_30 : histChunk 3 3 480 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel
theorem chunk_31 : histChunk 3 3 496 16 = 420912471554873005295335960077559630490411949096992 := by decide +kernel

/-- 서른두 토막 (바깥 줄 0 … 511 · 안쪽 0 … 511 = 고리 배치 2^18 가지 전부) 의 합 = 정확한 분배함수의 계수 -/
theorem count_3x3 :
    histChunk 3 3 0 16 +
    histChunk 3 3 16 16 +
    histChunk 3 3 32 16 +
    histChunk 3 3 48 16 +
    histChunk 3 3 64 16 +
    histChunk 3 3 80 16 +
    histChunk 3 3 96 16 +
    histChunk 3 3 112 16 +
    histChunk 3 3 128 16 +
    histChunk 3 3 144 16 +
    histChunk 3 3 160 16 +
    histChunk 3 3 176 16 +
    histChunk 3 3 192 16 +
    histChunk 3 3 208 16 +
    histChunk 3 3 224 16 +
    histChunk 3 3 240 16 +
    histChunk 3 3 256 16 +
    histChunk 3 3 272 16 +
    histChunk 3 3 288 16 +
    histChunk 3 3 304 16 +
    histChunk 3 3 320 16 +
    histChunk 3 3 336 16 +
    histChunk 3 3 352 16 +
    histChunk 3 3 368 16 +
    histChunk 3 3 384 16 +
    histChunk 3 3 400 16 +
    histChunk 3 3 416 16 +
    histChunk 3 3 432 16 +
    histChunk 3 3 448 16 +
    histChunk 3 3 464 16 +
    histChunk 3 3 480 16 +
    histChunk 3 3 496 16 = expect 9 := by
  rw [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28, chunk_29, chunk_30, chunk_31]
  decide +kernel

end GaugeZ2

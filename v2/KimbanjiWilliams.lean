import Mathlib
/-! Williams 1982 (Canad. Math. Bull. 25, p. 368) Theorem 1 의 인쇄 부호 점검.
    T₀ = Σ_k C(p,5k). 인쇄: 5F_p ≡ ε(5T₀ − 2^p − 2) (mod p²). 바른 꼴: 5F_p ≡ ε(5T₀ − 2^p + 2).
    p = 7: F_7 = 13, T₀ = C(7,0)+C(7,5) = 22, ε = −1. -/
theorem williams_T0_7 : (Nat.choose 7 0 + Nat.choose 7 5 : ℤ) = 22 := by decide
theorem williams_fib_7 : (Nat.fib 7 : ℤ) = 13 := by decide
-- 바른 꼴은 p = 7 에서 성립
theorem williams_corrected_7 : (49:ℤ) ∣ (5*13 - (-1)*(5*22 - 2^7 + 2)) := by norm_num
-- 인쇄된 꼴은 p = 7 에서 깨진다 (반례)
theorem williams_printed_fails_7 : ¬ (49:ℤ) ∣ (5*13 - (-1)*(5*22 - 2^7 - 2)) := by norm_num
-- p = 11: F_11 = 89, T₀ = C(11,0)+C(11,5)+C(11,10) = 1+462+11 = 474, ε = +1
theorem williams_T0_11 : (Nat.choose 11 0 + Nat.choose 11 5 + Nat.choose 11 10 : ℤ) = 474 := by decide
theorem williams_fib_11 : (Nat.fib 11 : ℤ) = 89 := by decide
theorem williams_corrected_11 : (121:ℤ) ∣ (5*89 - (5*474 - 2^11 + 2)) := by norm_num
theorem williams_printed_fails_11 : ¬ (121:ℤ) ∣ (5*89 - (5*474 - 2^11 - 2)) := by norm_num

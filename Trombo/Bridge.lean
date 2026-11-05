/-
다리 — 너비 × 높이 × 창 (린 4 코어만 · Mathlib 없음)

y² = x³ − x 와 그 가족 y² = x³ − kx 의 모든 홀수 소수 p · 모든 높이 n · 모든 창 N 에서 바일 창이 양의 준정부호.
  · 너비 (모든 p) : HasseAll.hasse (a_p² < 4p) · HasseAll.hasse_family
  · 높이 (모든 n) : 뤼카 항등식 4qⁿ − V_n² = (4q − a²) U_n² (여기서 다시 증명)
  · 창 (모든 N)  : WeilAll.psd_all
V_n = αⁿ + ᾱⁿ 이 F_{pⁿ} 위의 대각합이라는 것(제타의 유리성)은 전언이다 — 여기 정리는 수열 V 에 대한 문장이다.
-/
import Trombo.WeilAll
import Trombo.HasseAll

namespace Trombo.Bridge

open Trombo.WeilAll in
theorem cassini (q a : Int) (n : Nat) :
    U q a (n + 1) ^ 2 - a * U q a (n + 1) * U q a n + q * U q a n ^ 2 = q ^ n := by
  induction n with
  | zero => simp [U]
  | succ n ih =>
    rw [U_two q a n, Int.pow_succ' q n, ← ih]
    grind

open Trombo.WeilAll in
theorem V_eq_U (q a : Int) (n : Nat) : V q a n = 2 * U q a (n + 1) - a * U q a n ∧
    V q a (n + 1) = 2 * U q a (n + 2) - a * U q a (n + 1) := by
  induction n with
  | zero => simp [U, V]; grind
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [V_two, U_two q a (n + 1), ih.1, ih.2, U_two q a n]
    grind

open Trombo.WeilAll in
/-- 뤼카 항등식 : 4qⁿ − V_n² = (4q − a²) U_n² -/
theorem lucas (q a : Int) (n : Nat) : 4 * q ^ n - V q a n ^ 2 = (4 * q - a ^ 2) * U q a n ^ 2 := by
  rw [(V_eq_U q a n).1, ← cassini q a n]
  grind

theorem sq_pos {u : Int} (h : u ≠ 0) : 0 < u ^ 2 := by
  have e : u ^ 2 = u * u := by grind
  rw [e]
  rcases Int.lt_or_gt_of_ne h with h1 | h1
  · have := Int.mul_pos (Int.neg_pos_of_neg h1) (Int.neg_pos_of_neg h1)
    rwa [Int.neg_mul_neg] at this
  · exact Int.mul_pos h1 h1

/-- 높이 n 의 하세 (수열 V 에 대한 문장) : a² < 4q 이면 V_n² ≤ 4qⁿ, U_n ≠ 0 이면 엄격 -/
theorem height (q a : Int) (h : a ^ 2 < 4 * q) (n : Nat) :
    WeilAll.V q a n ^ 2 ≤ 4 * q ^ n ∧ (WeilAll.U q a n ≠ 0 → WeilAll.V q a n ^ 2 < 4 * q ^ n) := by
  have h2 := lucas q a n
  constructor
  · have := Int.mul_nonneg (by omega : (0 : Int) ≤ 4 * q - a ^ 2) (Int.sq_nonneg (WeilAll.U q a n))
    omega
  · intro hU
    have := Int.mul_pos (by omega : (0 : Int) < 4 * q - a ^ 2) (sq_pos hU)
    omega

/-- ★ 너비 × 높이 × 창 — y² = x³ − x : 모든 홀수 소수 p, 모든 높이 n, 모든 창 N, 모든 정수 벡터 x 에서
    바일 창의 이차 형식 ≥ 0 -/
theorem curve_windows (p : Nat) (hp : HasseAll.IsPrime p) (hodd : p % 2 = 1) (n N : Nat) (x : Nat → Int) :
    0 ≤ WeilAll.QF ((p : Int) ^ n) (WeilAll.V (p : Int) (HasseAll.ap p) n) x N := by
  apply WeilAll.psd_all
  have h1 := HasseAll.hasse hp hodd
  have e : HasseAll.ap p ^ 2 = HasseAll.ap p * HasseAll.ap p := by grind
  exact (height (p : Int) (HasseAll.ap p) (by omega) n).1

/-- ★ 가족 전체 — y² = x³ − kx (p ∤ k) : 모든 홀수 소수 p, 모든 높이 n, 모든 창 N -/
theorem family_windows (p : Nat) (hp : HasseAll.IsPrime p) (hodd : p % 2 = 1) (k : Int) (hk : ¬ (p : Int) ∣ k)
    (n N : Nat) (x : Nat → Int) :
    0 ≤ WeilAll.QF ((p : Int) ^ n) (WeilAll.V (p : Int) (HasseAll.apK p k) n) x N := by
  apply WeilAll.psd_all
  have h1 := HasseAll.hasse_family hp hodd hk
  have e : HasseAll.apK p k ^ 2 = HasseAll.apK p k * HasseAll.apK p k := by grind
  exact (height (p : Int) (HasseAll.apK p k) (by omega) n).1

/-- 높이 1 : FFPrelude 의 주장 C(p, a_p) 가 모든 홀수 소수에서 (모든 창 · 계수 정확히 2) -/
theorem curve_claim (p : Nat) (hp : HasseAll.IsPrime p) (hodd : p % 2 = 1) :
    WeilAll.Claim (p : Int) (HasseAll.ap p) := by
  apply WeilAll.claim_general
  have h1 := HasseAll.hasse hp hodd
  have e : HasseAll.ap p ^ 2 = HasseAll.ap p * HasseAll.ap p := by grind
  omega

/-- 모든 높이에서 계수 2 (U_n ≠ 0 인 높이) -/
theorem curve_claim_height (p : Nat) (hp : HasseAll.IsPrime p) (hodd : p % 2 = 1) (n : Nat)
    (hU : WeilAll.U (p : Int) (HasseAll.ap p) n ≠ 0) :
    WeilAll.Claim ((p : Int) ^ n) (WeilAll.V (p : Int) (HasseAll.ap p) n) := by
  apply WeilAll.claim_general
  have h1 := HasseAll.hasse hp hodd
  have e : HasseAll.ap p ^ 2 = HasseAll.ap p * HasseAll.ap p := by grind
  exact (height (p : Int) (HasseAll.ap p) (by omega) n).2 hU

/-- 초특이 : p ≡ 3 (mod 4) 이면 수열의 높이 2 에서 V₂ = −2p, 곧 V₂² = 4p² — 그 창은 모든 N 에서 양의 준정부호이고
    모든 2 × 2 소행렬식이 0 이며 첫 칸은 2 (계수 정확히 1).
    V₂ 가 F_{p²} 위의 대각합이라는 해석은 제타의 유리성(전언) — 이 정리는 수열 V 에 대한 문장이다. -/
theorem curve_supersingular (p : Nat) (hp : HasseAll.IsPrime p) (hodd : p % 2 = 1) (h3 : p % 4 = 3) :
    WeilAll.V (p : Int) (HasseAll.ap p) 2 = -2 * (p : Int) ∧
    (∀ N : Nat, ∀ x : Nat → Int, 0 ≤ WeilAll.QF ((p : Int) ^ 2) (WeilAll.V (p : Int) (HasseAll.ap p) 2) x N) ∧
    (∀ r0 r1 c0 c1 : Nat,
      WeilAll.det (WeilAll.weil ((p : Int) ^ 2) (WeilAll.V (p : Int) (HasseAll.ap p) 2)) [r0, r1] [c0, c1] = 0) := by
  have h0 := HasseAll.ap_zero hp hodd h3
  have hv : WeilAll.V (p : Int) (HasseAll.ap p) 2 = -2 * (p : Int) := by
    rw [WeilAll.V_two, h0]; simp [WeilAll.V]; grind
  have hb : WeilAll.V (p : Int) (HasseAll.ap p) 2 ^ 2 = 4 * (p : Int) ^ 2 := by rw [hv]; grind
  obtain ⟨h1, h2, _⟩ := WeilAll.boundary _ _ hb
  exact ⟨hv, h1, h2⟩

end Trombo.Bridge

#print axioms Trombo.Bridge.lucas
#print axioms Trombo.Bridge.height
#print axioms Trombo.Bridge.curve_windows
#print axioms Trombo.Bridge.family_windows
#print axioms Trombo.Bridge.curve_claim
#print axioms Trombo.Bridge.curve_claim_height
#print axioms Trombo.Bridge.curve_supersingular

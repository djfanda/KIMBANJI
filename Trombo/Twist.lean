/-
비튼 원기둥 — 곧은 막대를 돌리면 모래시계 (린 4 코어만 · Mathlib 없음)

아래 고리를 두고 위 고리를 θ 만큼 돌린 곧은 막대 다발. 반각 탄젠트 tan(θ/2) = n/m 으로 두면 모든 좌표가 정수다 :
  R = m² + n² (고리 반지름) · 아래 끝 P = (R, 0) · 위 끝 Q = (m² − n², 2mn) (|Q| = R) · 막대의 가운데 M = (m², mn).
· 허리 : |M|² = m²R — 허리 반지름 a 는 a² = m²R, 곧 a = R · m/√(m² + n²) = R cos(θ/2).
· 곡면 : 막대 위의 점 X(t) = ((T − t)P + tQ)/T 에서 T²|X|² = T²a² + (R² − a²)(2t − T)²
  — a > 0 이면 한 장 쌍곡면 · a = 0 이면 꼭짓점을 맞댄 두 원뿔 · a = R 이면 원기둥.
· 허리가 가장 좁다 : 모든 t 에서 |X|² ≥ a² 이고, n ≠ 0 이면 같음은 가운데 2t = T 뿐.
· 0 < a ≤ R : θ < 180° (m ≠ 0) 이면 0 < a² ≤ R² · θ = 0 (n = 0) 이면 a = R · θ = 180° (m = 0) 이면 모든 막대가 축을 지난다 (a = 0).
· 시계 : 돌림이 클수록 (n/m 이 클수록) 허리가 좁다 — 돌림각이 시곗바늘이다.
· 90° (m = n = 1) : a² = R²/2.
· 알갱이 하나 : 지름이 R 인 알갱이가 지름 2a 의 허리를 지나려면 4a² > R² ⇔ 3m² > n² ⇔ θ < 120°.
  정확히 a = R/2 (θ = 120°) 에는 정수 m, n 으로 닿지 않는다 — n² = 3m² 의 정수해는 0 뿐 (√3 은 무리수 · 하세의 유클리드 보조정리).

검증 : lake build (Trombo.HasseAll 을 불러 쓴다)
-/
import Trombo.HasseAll

namespace Trombo.Twist

/-- 고리 반지름 R = m² + n² -/
def R (m n : Int) : Int := m ^ 2 + n ^ 2

/-- 위 끝도 같은 고리 위 : (m² − n²)² + (2mn)² = R² -/
theorem on_circle (m n : Int) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = R m n ^ 2 := by
  unfold R; grind

/-- 막대의 가운데 M = ((R + (m² − n²))/2, 2mn/2) = (m², mn) -/
theorem midpoint (m n : Int) : R m n + (m ^ 2 - n ^ 2) = 2 * m ^ 2 ∧ 2 * m * n = 2 * (m * n) := by
  unfold R; constructor <;> grind

/-- ★ 허리 : |M|² = m⁴ + m²n² = m²R -/
theorem waist_sq (m n : Int) : (m ^ 2) ^ 2 + (m * n) ^ 2 = m ^ 2 * R m n := by
  unfold R; grind

/-- ★ 곡면 : T²|X(t)|² = T²a² + (R² − a²)(2t − T)², a² = m²R -/
theorem surface (m n T t : Int) :
    ((T - t) * R m n + t * (m ^ 2 - n ^ 2)) ^ 2 + (t * (2 * m * n)) ^ 2 =
      T ^ 2 * (m ^ 2 * R m n) + (R m n ^ 2 - m ^ 2 * R m n) * (2 * t - T) ^ 2 := by
  unfold R; grind

theorem gap_eq (m n : Int) : R m n ^ 2 - m ^ 2 * R m n = n ^ 2 * R m n := by
  unfold R; grind

theorem R_nonneg (m n : Int) : 0 ≤ R m n := by
  unfold R; have := Int.sq_nonneg m; have := Int.sq_nonneg n; omega

/-- 허리가 가장 좁다 : 막대 위 모든 점에서 T²|X|² ≥ T²a² -/
theorem waist_min (m n T t : Int) :
    T ^ 2 * (m ^ 2 * R m n) ≤ ((T - t) * R m n + t * (m ^ 2 - n ^ 2)) ^ 2 + (t * (2 * m * n)) ^ 2 := by
  rw [surface, gap_eq]
  have := Int.mul_nonneg (Int.mul_nonneg (Int.sq_nonneg n) (R_nonneg m n)) (Int.sq_nonneg (2 * t - T))
  omega

/-- 같음은 가운데뿐 (n ≠ 0 이면 R ≠ 0 도 따라온다) -/
theorem waist_only_middle (m n T t : Int) (hn : n ≠ 0)
    (h : ((T - t) * R m n + t * (m ^ 2 - n ^ 2)) ^ 2 + (t * (2 * m * n)) ^ 2 = T ^ 2 * (m ^ 2 * R m n)) :
    2 * t = T := by
  have hR : R m n ≠ 0 := by
    intro h0
    apply hn
    have := Int.sq_nonneg m
    have := Int.sq_nonneg n
    unfold R at h0
    have k : n ^ 2 = 0 := by omega
    have e : n ^ 2 = n * n := by grind
    rw [e] at k
    rcases Int.mul_eq_zero.mp k with k1 | k1 <;> exact k1
  rw [surface, gap_eq] at h
  have h0 : n ^ 2 * R m n * (2 * t - T) ^ 2 = 0 := by omega
  rcases Int.mul_eq_zero.mp h0 with h1 | h1
  · rcases Int.mul_eq_zero.mp h1 with h2 | h2
    · exfalso; apply hn
      have e : n ^ 2 = n * n := by grind
      rw [e] at h2
      rcases Int.mul_eq_zero.mp h2 with h3 | h3 <;> exact h3
    · exact absurd h2 hR
  · have e : (2 * t - T) ^ 2 = (2 * t - T) * (2 * t - T) := by grind
    rw [e] at h1
    rcases Int.mul_eq_zero.mp h1 with h3 | h3 <;> omega

/-- ★ 0 ≤ a² ≤ R² -/
theorem waist_bounds (m n : Int) : 0 ≤ m ^ 2 * R m n ∧ m ^ 2 * R m n ≤ R m n ^ 2 := by
  constructor
  · exact Int.mul_nonneg (Int.sq_nonneg m) (R_nonneg m n)
  · have := gap_eq m n
    have := Int.mul_nonneg (Int.sq_nonneg n) (R_nonneg m n)
    omega

/-- θ < 180° (m ≠ 0) 이면 허리는 0 이 아니다 : a² > 0 -/
theorem waist_pos (m n : Int) (hm : m ≠ 0) : 0 < m ^ 2 * R m n := by
  have h1 : 0 < m ^ 2 := by
    have e : m ^ 2 = m * m := by grind
    rw [e]
    rcases Int.lt_or_gt_of_ne hm with h | h
    · have := Int.mul_pos (Int.neg_pos_of_neg h) (Int.neg_pos_of_neg h)
      rwa [Int.neg_mul_neg] at this
    · exact Int.mul_pos h h
  have h2 : 0 < R m n := by unfold R; have := Int.sq_nonneg n; omega
  exact Int.mul_pos h1 h2

/-- θ = 0 (n = 0) : 원기둥 a = R -/
theorem cylinder (m : Int) : m ^ 2 * R m 0 = R m 0 ^ 2 := by unfold R; grind

/-- θ = 180° (m = 0) : 모든 막대의 가운데가 축 위 (0, 0) — 꼭짓점을 맞댄 두 원뿔 -/
theorem cone (n : Int) : (0 : Int) ^ 2 * R 0 n = 0 ∧ R 0 n + ((0 : Int) ^ 2 - n ^ 2) = 0 ∧ 2 * (0 : Int) * n = 0 := by
  unfold R; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- θ = 90° (m = n = 1) : R = 2 · a² = R²/2 -/
theorem ninety : R 1 1 = 2 ∧ 2 * ((1 : Int) ^ 2 * R 1 1) = R 1 1 ^ 2 := by decide

/-- ★ 시계 : n/m < n'/m' (돌림이 더 크면) 이면 (a'/R')² < (a/R)² — m'²R < m²R' 꼴 -/
theorem clock (m n m' n' : Int) (hn : 0 ≤ n) (hm' : 0 ≤ m')
    (h : n * m' < n' * m) : m' ^ 2 * R m n < m ^ 2 * R m' n' := by
  have e : m ^ 2 * R m' n' - m' ^ 2 * R m n = (m * n' - m' * n) * (m * n' + m' * n) := by unfold R; grind
  have h1 : 0 < m * n' - m' * n := by
    have : n * m' = m' * n := Int.mul_comm n m'
    have : n' * m = m * n' := Int.mul_comm n' m
    omega
  have h2 : 0 < m * n' + m' * n := by
    have := Int.mul_nonneg hm' hn
    have : n' * m = m * n' := Int.mul_comm n' m
    have : 0 ≤ n * m' := Int.mul_nonneg hn hm'
    omega
  have := Int.mul_pos h1 h2
  omega

/-- ★ 알갱이 하나 : 4a² > R² ⇔ 3m² > n² (θ < 120°) -/
theorem grain_passes (m n : Int) (hR : 0 < R m n) : R m n ^ 2 < 4 * (m ^ 2 * R m n) ↔ n ^ 2 < 3 * m ^ 2 := by
  have e : 4 * (m ^ 2 * R m n) - R m n ^ 2 = R m n * (3 * m ^ 2 - n ^ 2) := by unfold R; grind
  constructor
  · intro h
    by_cases h2 : n ^ 2 < 3 * m ^ 2
    · exact h2
    · exfalso
      have : R m n * (3 * m ^ 2 - n ^ 2) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  · intro h
    have := Int.mul_pos hR (show 0 < 3 * m ^ 2 - n ^ 2 by omega)
    omega

/-- 3 이 n² 을 나누면 n 을 나눈다 (하세의 유클리드 보조정리 · 3 은 소수) -/
theorem three_dvd (n : Int) (h : (3 : Int) ∣ n * n) : (3 : Int) ∣ n := by
  have hp : HasseAll.IsPrime 3 := by decide
  rcases HasseAll.euclid hp (a := n) (b := n) (by exact_mod_cast h) with h1 | h1 <;> exact_mod_cast h1

/-- ★ √3 은 무리수 : n² = 3m² 의 정수해는 (0, 0) 뿐 -/
theorem sqrt_three : ∀ (N : Nat) (m n : Int), n.natAbs + m.natAbs ≤ N → n ^ 2 = 3 * m ^ 2 → m = 0 ∧ n = 0 := by
  intro N
  induction N with
  | zero => intro m n hN _; omega
  | succ N ih =>
    intro m n hN h
    have hn2 : n * n = 3 * (m * m) := by grind
    have h3 : (3 : Int) ∣ n := three_dvd n ⟨m * m, hn2⟩
    obtain ⟨k, rfl⟩ := h3
    have hm : m ^ 2 = 3 * k ^ 2 := by grind
    by_cases hk : k = 0
    · subst hk
      have : m ^ 2 = 0 := by omega
      have e : m ^ 2 = m * m := by grind
      rw [e] at this
      rcases Int.mul_eq_zero.mp this with h0 | h0 <;> exact ⟨h0, by omega⟩
    · exfalso
      have := ih k m (by omega) hm
      exact hk this.1

/-- ★ 허리가 정확히 R/2 인 정수 돌림은 없다 (R ≠ 0) — θ = 120° 는 √3 이 있어야 닿는다 -/
theorem no_exact_half (m n : Int) (hR : R m n ≠ 0) : R m n ^ 2 ≠ 4 * (m ^ 2 * R m n) := by
  intro h
  have e : 4 * (m ^ 2 * R m n) - R m n ^ 2 = R m n * (3 * m ^ 2 - n ^ 2) := by unfold R; grind
  have h0 : R m n * (3 * m ^ 2 - n ^ 2) = 0 := by omega
  rcases Int.mul_eq_zero.mp h0 with h1 | h1
  · exact hR h1
  · have := sqrt_three (n.natAbs + m.natAbs) m n (Nat.le_refl _) (by omega)
    apply hR
    rw [this.1, this.2]; decide

/-- 작은 돌림의 표 : (m, n) → (a², R²) — 0° · 약 53° · 90° · 약 127° · 180° -/
theorem table :
    ((1 : Int) ^ 2 * R 1 0, R 1 0 ^ 2) = (1, 1) ∧
    ((2 : Int) ^ 2 * R 2 1, R 2 1 ^ 2) = (20, 25) ∧
    ((1 : Int) ^ 2 * R 1 1, R 1 1 ^ 2) = (2, 4) ∧
    ((1 : Int) ^ 2 * R 1 2, R 1 2 ^ 2) = (5, 25) ∧
    ((0 : Int) ^ 2 * R 0 1, R 0 1 ^ 2) = (0, 1) := by decide

end Trombo.Twist

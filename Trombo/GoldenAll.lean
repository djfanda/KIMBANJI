/-
황금비의 모든 거듭제곱 ((1+√5)/2)ⁿ = (Lₙ + Fₙ√5)/2 의 정수 꼴과 노름 ±4 — 모든 n (■)
(린 4 커널 확인 · Mathlib 없이 · 린 코어만 · sorry 없음 · native_decide 없음 · 새 공리 없음)

피보나치 F 0 = 0 · F 1 = 1 · F (n + 2) = F n + F (n + 1)
루카스   L 0 = 2 · L 1 = 1 · L (n + 2) = L n + L (n + 1)

황금비 φ = (1+√5)/2 를 곱하면 (L, F) 가 ((L + 5F)/2, (L + F)/2) 로 간다. 그래서 정수 등식 두 개
  step_F : 2·F (n + 1) = L n + F n
  step_L : 2·L (n + 1) = L n + 5·F n
이 모든 n 에서 성립한다는 것이 곧 φⁿ = (Lₙ + Fₙ√5)/2 의 √ 없는 꼴이다 (해석 : √5 를 쓰지 않고 정수만으로 적는다).
노름 : Lₙ² − 5·Fₙ² = 4·(−1)ⁿ (φ 는 노름 −1 인 단위 · φⁿ 의 노름은 (−1)ⁿ · 분모 2 때문에 4 배).
카시니 : F (n + 2)·F n − F (n + 1)² = (−1)^(n + 1).
루카스 합 : L (n + 1) = F n + F (n + 2).
두 배 : F (2n) = F n · L n.
틈 : Lₙ² − 5·Fₙ² 는 4 또는 −4 (노름의 따름 정리 — 해석 : (Lₙ − Fₙ√5)·(Lₙ + Fₙ√5) = ±4 이고 Lₙ + Fₙ√5 = 2φⁿ 이 커지므로
  |Lₙ − Fₙ√5| = 4/(2φⁿ) 가 0 으로 줄어든다 — 이 줄어듦 자체는 실수에 관한 해석이며 파일은 정수 등식만 증명한다).

모든 정리는 n 에 대한 귀납과 omega · grind 로 닫는다. 끝에 #print axioms 로 쓰인 공리를 보인다.
검증 : lean 황금일반.lean  (린 v4.34.0)
-/

namespace GoldenAll

/-- 피보나치 : F 0 = 0 · F 1 = 1 · F (n + 2) = F n + F (n + 1) -/
def F : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- 루카스 : L 0 = 2 · L 1 = 1 · L (n + 2) = L n + L (n + 1) -/
def L : Nat → Int
  | 0 => 2
  | 1 => 1
  | n + 2 => L n + L (n + 1)

theorem F_zero : F 0 = 0 := rfl
theorem F_one : F 1 = 1 := rfl
theorem L_zero : L 0 = 2 := rfl
theorem L_one : L 1 = 1 := rfl
theorem F_rec (n : Nat) : F (n + 2) = F n + F (n + 1) := rfl
theorem L_rec (n : Nat) : L (n + 2) = L n + L (n + 1) := rfl

/-- φ 를 한 번 곱하기 : 두 등식을 함께 귀납 -/
theorem step_both (n : Nat) :
    2 * F (n + 1) = L n + F n ∧ 2 * L (n + 1) = L n + 5 * F n := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    have e1 : F (k + 1 + 1) = F k + F (k + 1) := rfl
    have e2 : L (k + 1 + 1) = L k + L (k + 1) := rfl
    obtain ⟨h1, h2⟩ := ih
    constructor <;> omega

/-- 1. 2·F (n + 1) = L n + F n -/
theorem step_F (n : Nat) : 2 * F (n + 1) = L n + F n := (step_both n).1

/-- 2. 2·L (n + 1) = L n + 5·F n -/
theorem step_L (n : Nat) : 2 * L (n + 1) = L n + 5 * F n := (step_both n).2

/-- 3. 노름 : L n · L n − 5 · F n · F n = 4 · (−1)ⁿ -/
theorem norm (n : Nat) : L n * L n - 5 * F n * F n = 4 * (-1) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h1 := step_F k
    have h2 := step_L k
    have hp : (-1 : Int) ^ (k + 1) = (-1) ^ k * (-1) := Int.pow_succ _ _
    -- 4 배 한 꼴 : (2x)² − 5(2y)² = (a + 5b)² − 5(a + b)² = −4(a² − 5b²)
    have e : 4 * (L (k + 1) * L (k + 1) - 5 * F (k + 1) * F (k + 1))
        = (2 * L (k + 1)) * (2 * L (k + 1)) - 5 * ((2 * F (k + 1)) * (2 * F (k + 1))) := by
      grind
    rw [h1, h2] at e
    have e' : (L k + 5 * F k) * (L k + 5 * F k) - 5 * ((L k + F k) * (L k + F k))
        = -4 * (L k * L k - 5 * F k * F k) := by grind
    rw [e', ih] at e
    rw [hp]
    have e'' : 4 * (L (k + 1) * L (k + 1) - 5 * F (k + 1) * F (k + 1)) = 4 * (4 * ((-1) ^ k * (-1))) := by
      rw [e]; grind
    exact Int.eq_of_mul_eq_mul_left (by decide) e''

/-- 4. 카시니 : F (n + 2) · F n − F (n + 1) · F (n + 1) = (−1)^(n + 1) -/
theorem cassini (n : Nat) : F (n + 2) * F n - F (n + 1) * F (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have e1 := F_rec k
    have e2 := F_rec (k + 1)
    have hp : (-1 : Int) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) := Int.pow_succ _ _
    rw [hp, ← ih, e2, e1]
    grind

/-- 5. 루카스 합 : L (n + 1) = F n + F (n + 2) -/
theorem lucas_sum (n : Nat) : L (n + 1) = F n + F (n + 2) := by
  have h : 2 * F (n + 2) = L (n + 1) + F (n + 1) := step_F (n + 1)
  have e := F_rec n
  have h1 := step_F n
  have h2 := step_L n
  omega

/-- φ² 를 한 번 곱하기 : 2·F (n + 2) = L n + 3·F n · 2·L (n + 2) = 3·L n + 5·F n -/
theorem step2 (n : Nat) :
    2 * F (n + 2) = L n + 3 * F n ∧ 2 * L (n + 2) = 3 * L n + 5 * F n := by
  have a1 := step_F n
  have a2 := step_L n
  have b1 : 2 * F (n + 2) = L (n + 1) + F (n + 1) := step_F (n + 1)
  have b2 : 2 * L (n + 2) = L (n + 1) + 5 * F (n + 1) := step_L (n + 1)
  constructor <;> omega

/-- 두 배 (함께 귀납) : F (2n) = F n · L n · 2·L (2n) = L n² + 5·F n² -/
theorem double_both (n : Nat) :
    F (2 * n) = F n * L n ∧ 2 * L (2 * n) = L n * L n + 5 * (F n * F n) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    have s := step2 (2 * k)
    have hk : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hk]
    obtain ⟨s1, s2⟩ := s
    have h1 := step_F k
    have h2 := step_L k
    -- 4·F(n+1)·L(n+1) = (a + b)(a + 5b) · 4·(L² + 5F²)(n+1) = (a + 5b)² + 5(a + b)²
    have q1 : 4 * (F (k + 1) * L (k + 1)) = (L k + F k) * (L k + 5 * F k) := by
      rw [← h1, ← h2]; grind
    have q2 : 4 * (L (k + 1) * L (k + 1) + 5 * (F (k + 1) * F (k + 1)))
        = (L k + 5 * F k) * (L k + 5 * F k) + 5 * ((L k + F k) * (L k + F k)) := by
      rw [← h1, ← h2]; grind
    have r1 : (L k + F k) * (L k + 5 * F k)
        = (L k * L k + 5 * (F k * F k)) + 6 * (F k * L k) := by grind
    have r2 : (L k + 5 * F k) * (L k + 5 * F k) + 5 * ((L k + F k) * (L k + F k))
        = 6 * (L k * L k + 5 * (F k * F k)) + 20 * (F k * L k) := by grind
    rw [r1] at q1
    rw [r2] at q2
    rw [← i1, ← i2] at q1
    rw [← i1, ← i2] at q2
    constructor
    · -- 4·F(2k+2) = 2·L(2k) + 6·F(2k)
      have : 4 * F (2 * k + 2) = 4 * (F (k + 1) * L (k + 1)) := by omega
      exact Int.eq_of_mul_eq_mul_left (by decide) this
    · have : 4 * (2 * L (2 * k + 2))
          = 4 * (L (k + 1) * L (k + 1) + 5 * (F (k + 1) * F (k + 1))) := by omega
      exact Int.eq_of_mul_eq_mul_left (by decide) this

/-- 6. 두 배 : F (2n) = F n · L n -/
theorem double (n : Nat) : F (2 * n) = F n * L n := (double_both n).1

/-- 7. 틈 : L n · L n − 5 · F n · F n 는 4 또는 −4 (노름의 따름 정리) -/
theorem golden_power_gap (n : Nat) :
    L n * L n - 5 * F n * F n = 4 ∨ L n * L n - 5 * F n * F n = -4 := by
  rw [norm n]
  have h : ∀ m : Nat, (-1 : Int) ^ m = 1 ∨ (-1 : Int) ^ m = -1 := by
    intro m
    induction m with
    | zero => left; decide
    | succ j ih =>
      rw [Int.pow_succ]
      rcases ih with h | h <;> rw [h]
      · right; decide
      · left; decide
  rcases h n with h | h <;> rw [h]
  · left; decide
  · right; decide

end GoldenAll


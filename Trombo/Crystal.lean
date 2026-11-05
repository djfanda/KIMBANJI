/-
결정과 준결정 — 다섯 겹은 왜 평면 격자에 없는가 (린 4 코어만 · Mathlib 없음)

· 결정학 제한 = 바일 상자의 q = 1 칸 : 2 × 2 정수 행렬 A 가 어떤 n ≥ 1 에서 Aⁿ = I 이면 A⁴ = I 또는 A⁶ = I.
  행렬식 1 (돌림) 이면 대각합 t 는 t² ≤ 4 · 1 — 상자 안의 정수 다섯 −2 · −1 · 0 · 1 · 2 가 차수 2 · 3 · 4 · 6 · 1.
  다섯 · 일곱 · 여덟 · 열 · 열두 겹은 없다.
  길 : 케일리–해밀턴 A² = tA − δI → Aⁿ⁺¹ = U_{n+1} A − δ U_n I (U 는 WeilAll 의 뤼카 수열 · q = δ · a = t)
       → δ = 1 · t² ≥ 4 이면 카시니로 U_n² 이 한 걸음마다 1 이상 자라 U_{n+1} ≠ 0 → A 는 스칼라 → A = ±I.
       δ = −1 이면 A² (행렬식 1 · 대각합 t² + 2) 에 같은 논법 → t = 0 · A² = I.
· 네 차원 · 여섯 차원이면 된다 : 원분 다항식 Φ₅ · Φ₈ · Φ₁₀ · Φ₁₂ 의 동반 행렬 (4 × 4 정수) 과 Φ₇ (6 × 6) 의 차수가
  정확히 5 · 8 · 10 · 12 · 7 · 다섯 칸 순환 치환의 대각합 0 = 1 + 2cos72° + 2cos144° (Z[φ] 에서 합 −1 · 곱 −1).
· 황금비는 바일 상자 밖 (a, q) = (1, −1) : 피보나치 = U(−1, 1) · 뤼카 = V(−1, 1) · L² − 5F² = 4(−1)ⁿ (Bridge.lucas 그대로).
· 2cos72° 는 t² + t − 1 = 0 의 근이고 유리수가 아니다 · 2cos(2π/7) 은 t³ + t² − 2t − 1 = 0 의 근이고 유리근이 없다 (3 차).
· 껍질 : n × n × n 격자 상자에서 겉 칸의 비율은 n 이 커질수록 줄어든다 · 같은 부피의 상자 가운데 겉넓이가 가장 작은 것은
  정육면체 — (ab + bc + ca)³ ≥ 27(abc)² · 정해진 막의 양 M = 두께 t × 겉넓이 S 이면 216 t³ V² ≤ M³ (상자).

검증 : lake build (Trombo.Bridge 를 불러 쓴다)
-/
import Trombo.Bridge

namespace Trombo.Crystal

open Trombo.WeilAll (U V U_two)

/-! ## 1. 2 × 2 정수 행렬 -/

structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace M2

def mul (A B : M2) : M2 :=
  ⟨A.a * B.a + A.b * B.c, A.a * B.b + A.b * B.d, A.c * B.a + A.d * B.c, A.c * B.b + A.d * B.d⟩

def one : M2 := ⟨1, 0, 0, 1⟩
def neg1 : M2 := ⟨-1, 0, 0, -1⟩

def pw (A : M2) : Nat → M2
  | 0 => one
  | n + 1 => mul A (pw A n)

def tr (A : M2) : Int := A.a + A.d
def det (A : M2) : Int := A.a * A.d - A.b * A.c

end M2

open M2

theorem mul_one (A : M2) : mul A one = A := by
  cases A; simp only [mul, one, M2.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem one_mul (A : M2) : mul one A = A := by
  cases A; simp only [mul, one, M2.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_assoc (A B C : M2) : mul (mul A B) C = mul A (mul B C) := by
  cases A; cases B; cases C; simp only [mul, M2.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem det_mul (A B : M2) : det (mul A B) = det A * det B := by
  cases A; cases B; simp only [det, mul]; grind

theorem det_pw (A : M2) (n : Nat) : det (pw A n) = det A ^ n := by
  induction n with
  | zero => simp [pw, det, one]
  | succ n ih => rw [pw, det_mul, ih, Int.pow_succ']

theorem pw_add (A : M2) (m n : Nat) : pw A (m + n) = mul (pw A m) (pw A n) := by
  induction m with
  | zero => simp only [Nat.zero_add, pw, one_mul]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, pw, pw, ih, mul_assoc]

theorem pw_one_eq (n : Nat) : pw one n = one := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pw, ih, mul_one]

/-- 케일리–해밀턴 : A² = tA − δI -/
theorem cayley (A : M2) : mul A A = ⟨tr A * A.a - det A, tr A * A.b, tr A * A.c, tr A * A.d - det A⟩ := by
  cases A; simp only [mul, tr, det, M2.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- ★ Aⁿ⁺¹ = U_{n+1} A − δ U_n I  (t = 대각합 · δ = 행렬식 · U = WeilAll.U δ t — 바일 창과 같은 뤼카 수열) -/
theorem pw_succ (A : M2) (n : Nat) :
    pw A (n + 1) = ⟨U (det A) (tr A) (n + 1) * A.a - det A * U (det A) (tr A) n,
                    U (det A) (tr A) (n + 1) * A.b,
                    U (det A) (tr A) (n + 1) * A.c,
                    U (det A) (tr A) (n + 1) * A.d - det A * U (det A) (tr A) n⟩ := by
  induction n with
  | zero =>
    cases A
    simp only [pw, mul, one, M2.mk.injEq, U]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
  | succ n ih =>
    have h2 : U (det A) (tr A) (n + 1 + 1) = tr A * U (det A) (tr A) (n + 1) - det A * U (det A) (tr A) n :=
      U_two (det A) (tr A) n
    rw [pw, ih, h2]
    generalize U (det A) (tr A) (n + 1) = y
    generalize U (det A) (tr A) n = x
    cases A
    simp only [mul, tr, det, M2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## 2. 자람 — t² ≥ 4 이고 δ = 1 이면 U 는 0 으로 돌아오지 않는다 -/

theorem sq_nonneg' (t : Int) : 0 ≤ t * t := by
  rcases Int.le_total 0 t with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem sq_ge_four (t : Int) (h : 2 ≤ t ∨ t ≤ -2) : 4 ≤ t * t := by
  rcases h with h | h
  · have := Int.mul_le_mul h h (by omega) (by omega)
    omega
  · have := Int.mul_le_mul (show 2 ≤ -t by omega) (show 2 ≤ -t by omega) (by omega) (by omega)
    rw [Int.neg_mul_neg] at this
    omega

/-- 카시니 (q = 1) : U_{n+1}² − t U_{n+1} U_n + U_n² = 1 -/
theorem cassini_one (t : Int) (n : Nat) :
    U 1 t (n + 1) * U 1 t (n + 1) - t * (U 1 t (n + 1) * U 1 t n) + U 1 t n * U 1 t n = 1 := by
  have h := Bridge.cassini 1 t n
  rw [Int.one_pow] at h
  grind

theorem grow (t : Int) (ht : 4 ≤ t * t) (n : Nat) :
    U 1 t n * U 1 t n + 1 ≤ U 1 t (n + 1) * U 1 t (n + 1) := by
  induction n with
  | zero => simp [U]
  | succ n ih =>
    have h2 : U 1 t (n + 1 + 1) = t * U 1 t (n + 1) - 1 * U 1 t n := U_two 1 t n
    have hc := cassini_one t n
    rw [h2]
    generalize U 1 t (n + 1) = y at ih hc ⊢
    generalize U 1 t n = x at ih hc ⊢
    have hp : 0 ≤ (t * t - 4) * (y * y) := Int.mul_nonneg (by omega) (sq_nonneg' y)
    have e1 : (t * y - 1 * x) * (t * y - 1 * x) = (t * t) * (y * y) - 2 * (t * (y * x)) + x * x := by grind
    have e2 : (t * t - 4) * (y * y) = (t * t) * (y * y) - 4 * (y * y) := by grind
    rw [e1]
    omega

theorem U_sq_ge (t : Int) (ht : 4 ≤ t * t) (n : Nat) : (n : Int) ≤ U 1 t n * U 1 t n := by
  induction n with
  | zero => simp [U]
  | succ n ih => have := grow t ht n; push_cast; omega

theorem U_ne_zero (t : Int) (ht : 4 ≤ t * t) (n : Nat) : U 1 t (n + 1) ≠ 0 := by
  intro h
  have := U_sq_ge t ht (n + 1)
  rw [h] at this
  push_cast at this
  omega

/-! ## 3. 결정학 제한 -/

theorem sq_one {x : Int} (h : x * x = 1) : x = 1 ∨ x = -1 := by
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h1 | h1 | h1 | h1 | h1
  · have := sq_ge_four x (Or.inr h1); omega
  · exact Or.inr h1
  · subst h1; simp at h
  · exact Or.inl h1
  · have := sq_ge_four x (Or.inl h1); omega

theorem det_unit (A : M2) (n : Nat) (h : pw A (n + 1) = one) : det A = 1 ∨ det A = -1 := by
  have h1 : det A ^ (n + 1) = 1 := by rw [← det_pw, h]; rfl
  have h2 : (det A).natAbs ^ (n + 1) = 1 := by rw [← Int.natAbs_pow, h1]; rfl
  have h3 : (det A).natAbs = 1 := by
    rcases (show (det A).natAbs = 0 ∨ (det A).natAbs = 1 ∨ 2 ≤ (det A).natAbs by omega) with h4 | h4 | h4
    · rw [h4] at h2; simp at h2
    · exact h4
    · have := Nat.le_self_pow (show n + 1 ≠ 0 by omega) (det A).natAbs
      omega
  omega

/-- U_{n+1} ≠ 0 이고 Aⁿ⁺¹ = I 이면 A 는 스칼라 -/
theorem scalar_of (A : M2) (n : Nat) (h : pw A (n + 1) = one) (hU : U (det A) (tr A) (n + 1) ≠ 0) :
    A.b = 0 ∧ A.c = 0 ∧ A.a = A.d := by
  rw [pw_succ] at h
  simp only [one, M2.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rcases Int.mul_eq_zero.mp h2 with h | h
    · exact absurd h hU
    · exact h
  · rcases Int.mul_eq_zero.mp h3 with h | h
    · exact absurd h hU
    · exact h
  · have e : U (det A) (tr A) (n + 1) * (A.a - A.d) = 0 := by grind
    rcases Int.mul_eq_zero.mp e with h | h
    · exact absurd h hU
    · omega

/-- 행렬식 1 (돌림) : 대각합이 −1 · 0 · 1 이거나 A = ±I -/
theorem det_one_case (A : M2) (hd : det A = 1) (n : Nat) (h : pw A (n + 1) = one) :
    (tr A = -1 ∨ tr A = 0 ∨ tr A = 1) ∨ A = one ∨ A = neg1 := by
  by_cases ht : -1 ≤ tr A ∧ tr A ≤ 1
  · left; omega
  · right
    have h4 : 4 ≤ tr A * tr A := sq_ge_four _ (by omega)
    have hU : U (det A) (tr A) (n + 1) ≠ 0 := by rw [hd]; exact U_ne_zero _ h4 n
    obtain ⟨hb, hc, had⟩ := scalar_of A n h hU
    have haa : A.a * A.a = 1 := by
      have e : det A = A.a * A.d - A.b * A.c := rfl
      rw [hb, hc, ← had] at e
      omega
    cases A with
    | mk a b c d =>
      simp only at hb hc had haa
      subst hb hc had
      rcases sq_one haa with h1 | h1
      · left; subst h1; rfl
      · right; subst h1; rfl

/-- 행렬식 −1 (뒤집기) : 대각합 0 이고 A² = I -/
theorem det_neg_case (A : M2) (hd : det A = -1) (n : Nat) (h : pw A (n + 1) = one) :
    tr A = 0 ∧ mul A A = one := by
  have hN : pw (mul A A) (n + 1) = one := by
    have e : ∀ k, pw (mul A A) k = pw A (k + k) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pw, ih, show k + 1 + (k + 1) = (k + k) + 1 + 1 by omega, pw, pw, ← mul_assoc]
    rw [e, pw_add, h, mul_one]
  have hdN : det (mul A A) = 1 := by rw [det_mul, hd]; rfl
  have htN : tr (mul A A) = tr A * tr A + 2 := by
    rw [cayley]; simp only [tr]; rw [hd]; grind
  have hsq := sq_nonneg' (tr A)
  rcases det_one_case (mul A A) hdN n hN with h1 | h1 | h1
  · omega
  · -- A² = I → tA = 0
    rw [cayley] at h1
    simp only [one, M2.mk.injEq] at h1
    obtain ⟨e1, e2, e3, e4⟩ := h1
    rw [hd] at e1 e4
    have ha : tr A * A.a = 0 := by omega
    have hb : tr A * A.b = 0 := e2
    have hc : tr A * A.c = 0 := e3
    have hdd : tr A * A.d = 0 := by omega
    by_cases t0 : tr A = 0
    · refine ⟨t0, ?_⟩
      rw [cayley]; simp only [one, M2.mk.injEq]; rw [t0, hd]; simp
    · exfalso
      have a0 := (Int.mul_eq_zero.mp ha).resolve_left t0
      have b0 := (Int.mul_eq_zero.mp hb).resolve_left t0
      have c0 := (Int.mul_eq_zero.mp hc).resolve_left t0
      have d0 := (Int.mul_eq_zero.mp hdd).resolve_left t0
      have e : det A = A.a * A.d - A.b * A.c := rfl
      rw [a0, b0, c0, d0] at e
      omega
  · -- A² = −I : 불가능
    exfalso
    rw [cayley] at h1
    simp only [neg1, M2.mk.injEq] at h1
    obtain ⟨e1, e2, e3, e4⟩ := h1
    rw [hd] at e1 e4
    have ha : tr A * A.a = -2 := by omega
    have hdd : tr A * A.d = -2 := by omega
    have hs : tr A * tr A = -4 := by
      have e : tr A * tr A = tr A * A.a + tr A * A.d := by simp only [tr]; grind
      omega
    omega

/-- ★ 결정학 제한 (바일 상자의 q = 1 칸) : 유한 차수의 2 × 2 정수 행렬은 A⁴ = I 또는 A⁶ = I -/
theorem crystal (A : M2) (n : Nat) (h : pw A (n + 1) = one) : pw A 4 = one ∨ pw A 6 = one := by
  rcases det_unit A n h with hd | hd
  · rcases det_one_case A hd n h with ht | ht | ht
    · rcases ht with ht | ht | ht
      · -- t = −1 : A³ = I
        right
        rw [show (6 : Nat) = 5 + 1 from rfl, pw_succ, hd, ht]
        have u6 : U 1 (-1) (5 + 1) = 0 := by decide
        have u5 : U 1 (-1) 5 = -1 := by decide
        rw [u6, u5]; simp [one]
      · -- t = 0 : A² = −I
        left
        rw [show (4 : Nat) = 3 + 1 from rfl, pw_succ, hd, ht]
        have u4 : U 1 0 (3 + 1) = 0 := by decide
        have u3 : U 1 0 3 = -1 := by decide
        rw [u4, u3]; simp [one]
      · -- t = 1 : A³ = −I
        right
        rw [show (6 : Nat) = 5 + 1 from rfl, pw_succ, hd, ht]
        have u6 : U 1 1 (5 + 1) = 0 := by decide
        have u5 : U 1 1 5 = -1 := by decide
        rw [u6, u5]; simp [one]
    · left; rw [ht]; exact pw_one_eq 4
    · left; rw [ht]; decide
  · obtain ⟨ht, _⟩ := det_neg_case A hd n h
    left
    rw [show (4 : Nat) = 3 + 1 from rfl, pw_succ, hd, ht]
    have u4 : U (-1) 0 (3 + 1) = 0 := by decide
    have u3 : U (-1) 0 3 = 1 := by decide
    rw [u4, u3]; simp [one]

/-- 대각합은 −2 … 2 -/
theorem crystal_trace (A : M2) (n : Nat) (h : pw A (n + 1) = one) : -2 ≤ tr A ∧ tr A ≤ 2 := by
  rcases det_unit A n h with hd | hd
  · rcases det_one_case A hd n h with ht | ht | ht
    · omega
    · rw [ht]; decide
    · rw [ht]; decide
  · have := (det_neg_case A hd n h).1; omega

/-- 돌림 (행렬식 1) 은 바일 상자 t² ≤ 4q 의 q = 1 칸에 산다 -/
theorem rotation_box (A : M2) (hd : det A = 1) (n : Nat) (h : pw A (n + 1) = one) :
    tr A * tr A ≤ 4 * det A := by
  rw [hd]
  have := crystal_trace A n h
  rcases (show tr A = -2 ∨ tr A = -1 ∨ tr A = 0 ∨ tr A = 1 ∨ tr A = 2 by omega) with e | e | e | e | e <;>
    rw [e] <;> decide

/-- 다섯 겹은 없다 : A⁵ = I 이면 A = I -/
theorem no_five (A : M2) (h : pw A 5 = one) : A = one := by
  rcases crystal A 4 h with h4 | h6
  · have e : pw A 5 = mul A (pw A 4) := rfl
    rw [h4, mul_one] at e; rw [← e, h]
  · have e : pw A 6 = mul A (pw A 5) := rfl
    rw [h, mul_one] at e; exact e.symm.trans h6

/-- 일곱 겹은 없다 -/
theorem no_seven (A : M2) (h : pw A 7 = one) : A = one := by
  rcases crystal A 6 h with h4 | h6
  · have e : pw A (3 + 4) = mul (pw A 3) (pw A 4) := pw_add A 3 4
    rw [h4, mul_one] at e
    have h3 : pw A 3 = one := by rw [← e]; exact h
    have e2 : pw A 4 = mul A (pw A 3) := rfl
    rw [h3, mul_one] at e2; rw [← e2, h4]
  · have e : pw A 7 = mul A (pw A 6) := rfl
    rw [h6, mul_one] at e; rw [← e, h]

/-- 여덟 겹은 없다 : A⁸ = I 이면 A⁴ = I -/
theorem no_eight (A : M2) (h : pw A 8 = one) : pw A 4 = one := by
  rcases crystal A 7 h with h4 | h6
  · exact h4
  · have e : pw A (2 + 6) = mul (pw A 2) (pw A 6) := pw_add A 2 6
    rw [h6, mul_one] at e
    have h2 : pw A 2 = one := by rw [← e]; exact h
    rw [show (4 : Nat) = 2 + 2 from rfl, pw_add, h2, mul_one]

/-- 열 겹은 없다 : A¹⁰ = I 이면 A² = I -/
theorem no_ten (A : M2) (h : pw A 10 = one) : pw A 2 = one := by
  rcases crystal A 9 h with h4 | h6
  · have e : pw A (2 + (4 + 4)) = mul (pw A 2) (mul (pw A 4) (pw A 4)) := by rw [pw_add, pw_add]
    rw [h4, mul_one, mul_one] at e
    rw [← e]; exact h
  · have e : pw A (4 + 6) = mul (pw A 4) (pw A 6) := pw_add A 4 6
    rw [h6, mul_one] at e
    have h4 : pw A 4 = one := by rw [← e]; exact h
    have e2 : pw A (2 + 4) = mul (pw A 2) (pw A 4) := pw_add A 2 4
    rw [h4, mul_one] at e2
    rw [← e2]; exact h6

/-- 열두 겹 (정확한 차수 12) 은 없다 -/
theorem no_twelve (A : M2) : ¬ (pw A 12 = one ∧ pw A 4 ≠ one ∧ pw A 6 ≠ one) := by
  intro ⟨h, h4, h6⟩
  rcases crystal A 11 h with e | e
  · exact h4 e
  · exact h6 e

/-- 상자의 다섯 정수가 모두 나온다 : 차수 1 · 2 · 3 · 4 · 6 의 증인 (대각합 2 · −2 · −1 · 0 · 1) -/
def r3 : M2 := ⟨0, -1, 1, -1⟩
def r4 : M2 := ⟨0, -1, 1, 0⟩
def r6 : M2 := ⟨1, -1, 1, 0⟩

theorem witnesses :
    tr one = 2 ∧ tr neg1 = -2 ∧ tr r3 = -1 ∧ tr r4 = 0 ∧ tr r6 = 1 ∧
    det r3 = 1 ∧ det r4 = 1 ∧ det r6 = 1 ∧
    pw neg1 2 = one ∧ neg1 ≠ one ∧
    pw r3 3 = one ∧ pw r3 1 ≠ one ∧ pw r3 2 ≠ one ∧
    pw r4 4 = one ∧ pw r4 1 ≠ one ∧ pw r4 2 ≠ one ∧ pw r4 3 ≠ one ∧
    pw r6 6 = one ∧ pw r6 1 ≠ one ∧ pw r6 2 ≠ one ∧ pw r6 3 ≠ one ∧ pw r6 4 ≠ one ∧ pw r6 5 ≠ one := by
  decide

/-! ## 4. 네 차원 · 여섯 차원 — 다섯 · 일곱 · 여덟 · 열 · 열두 겹의 정수 행렬 -/

abbrev Mat := List (List Int)

def ident (n : Nat) : Mat := (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

def col (B : Mat) (j : Nat) : List Int := B.map fun r => r.getD j 0

def dotL (u v : List Int) : Int := (List.zipWith (· * ·) u v).foldl (· + ·) 0

def mmul (A B : Mat) : Mat := A.map fun row => (List.range (B.headD []).length).map fun j => dotL row (col B j)

def mpow (A : Mat) : Nat → Mat
  | 0 => ident A.length
  | n + 1 => mmul A (mpow A n)

/-- 처음으로 Aᵏ = I 가 되는 k (1 ≤ k ≤ 한계) -/
def ord (A : Mat) (lim : Nat) : Option Nat :=
  ((List.range lim).map (· + 1)).find? fun k => mpow A k == ident A.length

def trace (A : Mat) : Int := ((List.range A.length).map fun i => (A.getD i []).getD i 0).foldl (· + ·) 0

/-- 모닉 xᵏ + c_{k−1}x^{k−1} + … + c₀ 의 동반 행렬 (아래 대각 1 · 마지막 열 −c) -/
def companion (c : List Int) : Mat :=
  (List.range c.length).map fun i => (List.range c.length).map fun j =>
    if j + 1 = c.length then -(c.getD i 0) else if i = j + 1 then 1 else 0

def phi5 : Mat := companion [1, 1, 1, 1]          -- x⁴ + x³ + x² + x + 1
def phi8 : Mat := companion [1, 0, 0, 0]          -- x⁴ + 1
def phi10 : Mat := companion [1, -1, 1, -1]       -- x⁴ − x³ + x² − x + 1
def phi12 : Mat := companion [1, 0, -1, 0]        -- x⁴ − x² + 1
def phi7 : Mat := companion [1, 1, 1, 1, 1, 1]    -- x⁶ + … + 1
def cyc5 : Mat := (List.range 5).map fun i => (List.range 5).map fun j => if i = (j + 1) % 5 then 1 else 0

theorem higher_orders :
    ord phi5 20 = some 5 ∧ ord phi8 20 = some 8 ∧ ord phi10 20 = some 10 ∧ ord phi12 20 = some 12 ∧
    ord phi7 20 = some 7 ∧ ord cyc5 20 = some 5 ∧
    phi5.length = 4 ∧ phi7.length = 6 ∧ trace phi5 = -1 ∧ trace cyc5 = 0 := by
  decide +kernel

/-! ## 5. 황금비 Z[φ] — 다섯 겹의 두 대각합 -/

/-- a + bφ (φ² = φ + 1) -/
def zmul (x y : Int × Int) : Int × Int := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)
def zadd (x y : Int × Int) : Int × Int := (x.1 + y.1, x.2 + y.2)

/-- 2cos72° = φ − 1 · 2cos144° = −φ : 합 −1 · 곱 −1 · 1 + 두 값 = 0 = 다섯 칸 순환의 대각합 · 둘 다 t² + t − 1 = 0 -/
theorem five_fold_traces :
    zadd (-1, 1) (0, -1) = (-1, 0) ∧ zmul (-1, 1) (0, -1) = (-1, 0) ∧
    zadd (1, 0) (zadd (-1, 1) (0, -1)) = (0, 0) ∧
    zadd (zadd (zmul (-1, 1) (-1, 1)) (-1, 1)) (-1, 0) = (0, 0) ∧
    zadd (zadd (zmul (0, -1) (0, -1)) (0, -1)) (-1, 0) = (0, 0) := by decide

/-- 황금비는 바일 상자 밖 : (a, q) = (1, −1) 에서 a² ≤ 4q 가 아니다 -/
theorem golden_outside : ¬ ((1 : Int) ^ 2 ≤ 4 * (-1)) := by decide

theorem fib_values : (List.range 13).map (U (-1) 1) = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144] ∧
    (List.range 8).map (V (-1) 1) = [2, 1, 3, 4, 7, 11, 18, 29] := by decide

/-- 뤼카–피보나치 : L_n² − 5F_n² = 4(−1)ⁿ (Bridge.lucas 의 (q, a) = (−1, 1)) -/
theorem fib_lucas (n : Nat) : V (-1) 1 n ^ 2 - 5 * U (-1) 1 n ^ 2 = 4 * (-1) ^ n := by
  have := Bridge.lucas (-1) 1 n
  grind

/-- 카시니 : F_{n+2} F_n − F_{n+1}² = (−1)ⁿ⁺¹ -/
theorem fib_cassini (n : Nat) : U (-1) 1 (n + 2) * U (-1) 1 n - U (-1) 1 (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  have h := Bridge.cassini (-1) 1 n
  have h2 : U (-1) 1 (n + 2) = 1 * U (-1) 1 (n + 1) - (-1) * U (-1) 1 n := U_two (-1) 1 n
  rw [h2, Int.pow_succ]
  grind

/-! ## 6. 다섯 겹은 2 차 무리수 · 일곱 겹은 3 차 -/

theorem even_of_golden (p q : Int) (h : p ^ 2 + p * q - q ^ 2 = 0) : p % 2 = 0 ∧ q % 2 = 0 := by
  have hp : p = 2 * (p / 2) + p % 2 := by omega
  have hq : q = 2 * (q / 2) + q % 2 := by omega
  have rp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  have rq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  generalize p / 2 = u at hp
  generalize q / 2 = v at hq
  generalize p % 2 = r at hp rp ⊢
  generalize q % 2 = s at hq rq ⊢
  subst hp hq
  have key : (2 * u + r) ^ 2 + (2 * u + r) * (2 * v + s) - (2 * v + s) ^ 2 =
      2 * (2 * r * u + r * v + s * u - 2 * s * v + 2 * u ^ 2 + 2 * u * v - 2 * v ^ 2) + (r * r + r * s - s * s) := by
    grind
  rw [key] at h
  rcases rp with rfl | rfl <;> rcases rq with rfl | rfl
  · exact ⟨rfl, rfl⟩
  all_goals (simp only [Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul] at h; omega)

/-- 2cos72° = (√5 − 1)/2 (t² + t − 1 = 0 의 근) 는 유리수가 아니다 -/
theorem golden_irrational : ∀ (N : Nat) (p q : Int), q.natAbs ≤ N → q ≠ 0 → p ^ 2 + p * q - q ^ 2 ≠ 0 := by
  intro N
  induction N with
  | zero => intro p q hN hq; omega
  | succ N ih =>
    intro p q hN hq h
    obtain ⟨hp2, hq2⟩ := even_of_golden p q h
    obtain ⟨p', rfl⟩ : ∃ p', p = 2 * p' := ⟨p / 2, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
    have h' : p' ^ 2 + p' * q' - q' ^ 2 = 0 := by
      have e : (2 * p') ^ 2 + 2 * p' * (2 * q') - (2 * q') ^ 2 = 4 * (p' ^ 2 + p' * q' - q' ^ 2) := by grind
      omega
    exact ih p' q' (by omega) (by omega) h'

theorem even_of_seven (p q : Int) (h : p ^ 3 + p ^ 2 * q - 2 * p * q ^ 2 - q ^ 3 = 0) : p % 2 = 0 ∧ q % 2 = 0 := by
  have hp : p = 2 * (p / 2) + p % 2 := by omega
  have hq : q = 2 * (q / 2) + q % 2 := by omega
  have rp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  have rq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  generalize p / 2 = u at hp
  generalize q / 2 = v at hq
  generalize p % 2 = r at hp rp ⊢
  generalize q % 2 = s at hq rq ⊢
  subst hp hq
  have key : (2 * u + r) ^ 3 + (2 * u + r) ^ 2 * (2 * v + s) - 2 * (2 * u + r) * (2 * v + s) ^ 2 - (2 * v + s) ^ 3 =
      2 * (3 * r ^ 2 * u + r ^ 2 * v - r * s ^ 2 + 2 * r * s * u - 4 * r * s * v + 6 * r * u ^ 2 + 4 * r * u * v
        - 4 * r * v ^ 2 - 2 * s ^ 2 * u - 3 * s ^ 2 * v + 2 * s * u ^ 2 - 8 * s * u * v - 6 * s * v ^ 2 + 4 * u ^ 3
        + 4 * u ^ 2 * v - 8 * u * v ^ 2 - 4 * v ^ 3) + (r * r * r + r * r * s - s * s * s) := by
    grind
  rw [key] at h
  rcases rp with rfl | rfl <;> rcases rq with rfl | rfl
  · exact ⟨rfl, rfl⟩
  all_goals (simp only [Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul] at h; omega)

/-- 2cos(2π/7) (t³ + t² − 2t − 1 = 0 의 근) 는 유리수가 아니다 — 유리근이 없는 3 차식은 유리수 위에서 기약 -/
theorem seven_irrational : ∀ (N : Nat) (p q : Int), q.natAbs ≤ N → q ≠ 0 →
    p ^ 3 + p ^ 2 * q - 2 * p * q ^ 2 - q ^ 3 ≠ 0 := by
  intro N
  induction N with
  | zero => intro p q hN hq; omega
  | succ N ih =>
    intro p q hN hq h
    obtain ⟨hp2, hq2⟩ := even_of_seven p q h
    obtain ⟨p', rfl⟩ : ∃ p', p = 2 * p' := ⟨p / 2, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
    have h' : p' ^ 3 + p' ^ 2 * q' - 2 * p' * q' ^ 2 - q' ^ 3 = 0 := by
      have e : (2 * p') ^ 3 + (2 * p') ^ 2 * (2 * q') - 2 * (2 * p') * (2 * q') ^ 2 - (2 * q') ^ 3 =
          8 * (p' ^ 3 + p' ^ 2 * q' - 2 * p' * q' ^ 2 - q' ^ 3) := by grind
      omega
    exact ih p' q' (by omega) (by omega) h'

/-! ## 7. 껍질 — 겉 칸의 비율과 같은 부피의 가장 두꺼운 막 -/

/-- (m + 2)³ 상자의 겉 칸 = (m + 2)³ − m³ = 6m² + 12m + 8 -/
theorem shell_count (m : Int) : (m + 2) ^ 3 - m ^ 3 = 6 * m ^ 2 + 12 * m + 8 := by grind

/-- 겉/전체 의 비율이 m → m + 1 에서 엄격히 준다 : 차이 = 6m⁴ + 36m³ + 66m² + 36m + 8 -/
theorem shell_fraction_drops (m : Nat) :
    ((m : Int) + 2) ^ 3 * (6 * ((m : Int) + 1) ^ 2 + 12 * ((m : Int) + 1) + 8) <
    ((m : Int) + 3) ^ 3 * (6 * (m : Int) ^ 2 + 12 * (m : Int) + 8) := by
  have e : ((m : Int) + 3) ^ 3 * (6 * (m : Int) ^ 2 + 12 * (m : Int) + 8) -
      ((m : Int) + 2) ^ 3 * (6 * ((m : Int) + 1) ^ 2 + 12 * ((m : Int) + 1) + 8) =
      8 + (m : Int) * (36 + (m : Int) * (66 + (m : Int) * (36 + 6 * (m : Int)))) := by grind
  have h0 : (0 : Int) ≤ (m : Int) := by omega
  have h1 : 0 ≤ (m : Int) * (36 + (m : Int) * (66 + (m : Int) * (36 + 6 * (m : Int)))) := by
    apply Int.mul_nonneg h0
    have : 0 ≤ (m : Int) * (66 + (m : Int) * (36 + 6 * (m : Int))) := by
      apply Int.mul_nonneg h0
      have : 0 ≤ (m : Int) * (36 + 6 * (m : Int)) := Int.mul_nonneg h0 (by omega)
      omega
    omega
  omega

/-- 세 수의 산술–기하 : 27xyz ≤ (x + y + z)³ (x, y, z ≥ 0) -/
theorem amgm3 (x y z : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have e : 2 * ((x + y + z) ^ 3 - 27 * (x * y * z)) =
      (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) + 6 * (x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2) := by
    grind
  have s1 : 0 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by
    have := Int.sq_nonneg (x - y); have := Int.sq_nonneg (y - z); have := Int.sq_nonneg (z - x); omega
  have t1 : 0 ≤ (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := Int.mul_nonneg (by omega) s1
  have t2 : 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
    have := Int.mul_nonneg hx (Int.sq_nonneg (y - z))
    have := Int.mul_nonneg hy (Int.sq_nonneg (z - x))
    have := Int.mul_nonneg hz (Int.sq_nonneg (x - y))
    omega
  omega

/-- 상자 a × b × c : (ab + bc + ca)³ ≥ 27(abc)² — 같은 부피에서 겉넓이가 가장 작은 상자는 정육면체 -/
theorem box_isoperimetric (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ^ 2 ≤ (a * b + b * c + c * a) ^ 3 := by
  have := amgm3 (a * b) (b * c) (c * a) (Int.mul_nonneg ha hb) (Int.mul_nonneg hb hc) (Int.mul_nonneg hc ha)
  have e : (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by grind
  rw [e] at this
  exact this

theorem cube_equality (a : Int) : 27 * (a * a * a) ^ 2 = (a * a + a * a + a * a) ^ 3 := by grind

/-- 산술 · 기하 평균의 같음 : x, y, z > 0 이고 27xyz = (x + y + z)³ 이면 x = y = z -/
theorem amgm3_eq (x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 27 * (x * y * z) = (x + y + z) ^ 3) : x = y ∧ y = z := by
  have e : 2 * ((x + y + z) ^ 3 - 27 * (x * y * z)) =
      (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) + 6 * (x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2) := by
    grind
  have s1 : 0 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by
    have := Int.sq_nonneg (x - y); have := Int.sq_nonneg (y - z); have := Int.sq_nonneg (z - x); omega
  have t1 : 0 ≤ (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := Int.mul_nonneg (by omega) s1
  have u1 : 0 ≤ x * (y - z) ^ 2 := Int.mul_nonneg (by omega) (Int.sq_nonneg (y - z))
  have u2 : 0 ≤ y * (z - x) ^ 2 := Int.mul_nonneg (by omega) (Int.sq_nonneg (z - x))
  have u3 : 0 ≤ z * (x - y) ^ 2 := Int.mul_nonneg (by omega) (Int.sq_nonneg (x - y))
  have w1 : x * (y - z) ^ 2 = 0 := by omega
  have w3 : z * (x - y) ^ 2 = 0 := by omega
  have q1 : (y - z) ^ 2 = 0 := (Int.mul_eq_zero.mp w1).resolve_left (by omega)
  have q3 : (x - y) ^ 2 = 0 := (Int.mul_eq_zero.mp w3).resolve_left (by omega)
  have r1 : y - z = 0 := by
    have e2 : (y - z) ^ 2 = (y - z) * (y - z) := by grind
    rw [e2] at q1
    rcases Int.mul_eq_zero.mp q1 with k | k <;> exact k
  have r3 : x - y = 0 := by
    have e2 : (x - y) ^ 2 = (x - y) * (x - y) := by grind
    rw [e2] at q3
    rcases Int.mul_eq_zero.mp q3 with k | k <;> exact k
  constructor <;> omega

/-- ★ 같음은 정육면체뿐 : a, b, c > 0 이고 27(abc)² = (ab + bc + ca)³ 이면 a = b = c -/
theorem box_equality_only_cube (a b c : Int) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 27 * (a * b * c) ^ 2 = (a * b + b * c + c * a) ^ 3) : a = b ∧ b = c := by
  have e : (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by grind
  rw [← e] at h
  obtain ⟨k1, k2⟩ := amgm3_eq (a * b) (b * c) (c * a) (Int.mul_pos ha hb) (Int.mul_pos hb hc) (Int.mul_pos hc ha) h
  have m1 : b * (a - c) = 0 := by grind
  have m2 : c * (b - a) = 0 := by grind
  have n1 : a - c = 0 := (Int.mul_eq_zero.mp m1).resolve_left (by omega)
  have n2 : b - a = 0 := (Int.mul_eq_zero.mp m2).resolve_left (by omega)
  constructor <;> omega

/-- 막의 양 M = 두께 t × 겉넓이 S (S = 2(ab + bc + ca)) 이면 216 t³ V² ≤ M³ (V = abc) — 부피가 커지면 막은 얇아진다 -/
theorem membrane (a b c t M : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hM : M = t * (2 * (a * b + b * c + c * a))) : 216 * t ^ 3 * (a * b * c) ^ 2 ≤ M ^ 3 := by
  have hb3 := box_isoperimetric a b c ha hb hc
  have t3 : 0 ≤ t ^ 3 := by
    have := Int.mul_nonneg (Int.mul_nonneg ht ht) ht
    have e : t ^ 3 = t * t * t := by grind
    omega
  have := Int.mul_le_mul_of_nonneg_left hb3 t3
  have e : M ^ 3 = 8 * (t ^ 3 * (a * b + b * c + c * a) ^ 3) := by rw [hM]; grind
  have e2 : 216 * t ^ 3 * (a * b * c) ^ 2 = 8 * (t ^ 3 * (27 * (a * b * c) ^ 2)) := by grind
  omega

end Trombo.Crystal

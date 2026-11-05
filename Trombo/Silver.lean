/-
은비 δ = 1 + √2 = (2 + √8)/2 — 모든 거듭제곱 δⁿ = Qₙ + Pₙ √2 와 모든 소수 p 의 합동 (■)
(린 4 코어만 · Mathlib 없음 · sorry 없음 · native_decide 없음 · 새 공리 없음)

황금비 꼴(GoldenAll · GoldenPrimeAll)의 쌍둥이. 내용은 모두 고전 사실(펠 수 · 반 짝 펠 수 · 제2 보충 법칙)을
린 커널로 옮겨 적은 것이다.

펠       P 0 = 0 · P 1 = 1 · P (n + 2) = 2·P (n + 1) + P n
반 짝 펠 Q 0 = 1 · Q 1 = 1 · Q (n + 2) = 2·Q (n + 1) + Q n

δ 를 한 번 곱하면 (Q, P) 가 (Q + 2P, Q + P) 로 간다 (분모 2 가 없다 — 황금비와 다른 점).
  1. step_Q · step_P : Q (n + 1) = Q n + 2·P n · P (n + 1) = Q n + P n
  2. norm            : Qₙ² − 2·Pₙ² = (−1)ⁿ  (δ 는 노름 −1 인 단위)
  3. cassini         : P (n + 2)·P n − P (n + 1)² = (−1)^(n + 1) · cassini_Q : Q (n + 2)·Q n − Q (n + 1)² = 2·(−1)ⁿ
  4. double          : P (2n) = 2·Pₙ·Qₙ · Q (2n) = Qₙ² + 2·Pₙ²
  5. pell_even       : Q (2n)² − 2·P (2n)² = 1  (x² − 2y² = 1 의 풀이)
  6. zpow_delta      : Z[√2] 의 쌍 곱셈으로 (1, 1)ⁿ = (Qₙ, Pₙ) · silver_inv : (1 + √2)(−1 + √2) = 1 (1/δ = δ − 2)
  7. metallic        : 모든 정수 n 에서 x = (n + √(n² + 4))/2 는 x² = n x + 1 (분모 2 를 걷어낸 정수 등식 · n = 1 황금 · n = 2 은)
소수 (길은 GoldenPrimeAll 과 같다 : (1 + √2)ⁿ = Σ C(n, k)(√2)ᵏ 의 두 성분이 곧 Qₙ · Pₙ 이고,
소수 p 에서 가운데 이항 계수가 모두 p 의 배수다 — 분모가 없으므로 2ᵖ ≡ 2 도 쓰지 않는다)
  C. half_pell_prime     : 모든 소수 p 에서 Qₚ ≡ 1 (mod p)
  D. pell_prime          : 모든 홀수 소수 p 에서 Pₚ ≡ 2^((p−1)/2) (mod p)
  E. two_supplement      : 제2 보충 법칙 (오일러 꼴) — 홀수 소수 p 에서
                           p ≡ ±1 (mod 8) 이면 2^((p−1)/2) ≡ 1 , p ≡ ±3 (mod 8) 이면 2^((p−1)/2) ≡ −1 (mod p)
     길 : Z[x]/(x⁴ + 1) (여덟째 단위근) 안의 가우스 합 τ = x − x³ = x (1 − x²) 는 τ² = 2 ,
     그래서 τᵖ = 2^((p−1)/2) τ . 한편 신입생의 꿈으로 τᵖ ≡ xᵖ (1 − x^(2p)) = ±τ (mod p). x 의 계수를 비교한다.
  따름 pell_prime_legendre : Pₚ ≡ (2/p) (mod p) · 2 ∣ P₂
  따름 pell_rank           : p ≡ ±1 (mod 8) 이면 p ∣ P (p − 1) , p ≡ ±3 (mod 8) 이면 p ∣ P (p + 1)
p = 2 에서 D 는 성립하지 않는다 (P₂ = 2 , 2⁰ = 1) — 그래서 D 는 홀수 소수만 말한다.

소수 · 이항 계수 · 합 · 이항 변환 · 합동 보조 정리는 GoldenPrimeAll 의 것을 그대로 쓴다.
-/
import Trombo.GoldenPrimeAll

namespace Silver

open GoldenPrimeAll (Prime bt bt_zero bt_succ bt_mul bt_prime sm sm_succ sm_congr prime_two_or_odd)

/-! ## 0. 정의와 한 걸음 -/

/-- 펠 : P 0 = 0 · P 1 = 1 · P (n + 2) = 2·P (n + 1) + P n -/
def P : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- 반 짝 펠 : Q 0 = 1 · Q 1 = 1 · Q (n + 2) = 2·Q (n + 1) + Q n -/
def Q : Nat → Int
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * Q (n + 1) + Q n

theorem P_zero : P 0 = 0 := rfl
theorem P_one : P 1 = 1 := rfl
theorem Q_zero : Q 0 = 1 := rfl
theorem Q_one : Q 1 = 1 := rfl
theorem P_rec (n : Nat) : P (n + 2) = 2 * P (n + 1) + P n := rfl
theorem Q_rec (n : Nat) : Q (n + 2) = 2 * Q (n + 1) + Q n := rfl

/-- δ 를 한 번 곱하기 : 두 등식을 함께 귀납 -/
theorem step_both (n : Nat) : Q (n + 1) = Q n + 2 * P n ∧ P (n + 1) = Q n + P n := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    have e1 : P (k + 1 + 1) = 2 * P (k + 1) + P k := rfl
    have e2 : Q (k + 1 + 1) = 2 * Q (k + 1) + Q k := rfl
    obtain ⟨h1, h2⟩ := ih
    constructor <;> omega

/-- 1. Q (n + 1) = Q n + 2·P n -/
theorem step_Q (n : Nat) : Q (n + 1) = Q n + 2 * P n := (step_both n).1

/-- 1'. P (n + 1) = Q n + P n -/
theorem step_P (n : Nat) : P (n + 1) = Q n + P n := (step_both n).2

/-- 2. 노름 : Q n · Q n − 2 · P n · P n = (−1)ⁿ -/
theorem norm (n : Nat) : Q n * Q n - 2 * P n * P n = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [step_Q, step_P, Int.pow_succ, ← ih]
    -- (a + 2b)² − 2(a + b)² = −(a² − 2b²)
    grind

/-- 3. 카시니 : P (n + 2) · P n − P (n + 1) · P (n + 1) = (−1)^(n + 1) -/
theorem cassini (n : Nat) : P (n + 2) * P n - P (n + 1) * P (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have e1 := P_rec k
    have e2 := P_rec (k + 1)
    have hp : (-1 : Int) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) := Int.pow_succ _ _
    rw [hp, ← ih, e2, e1]
    grind

/-- 3'. 반 짝 카시니 : Q (n + 2) · Q n − Q (n + 1) · Q (n + 1) = 2 · (−1)ⁿ -/
theorem cassini_Q (n : Nat) : Q (n + 2) * Q n - Q (n + 1) * Q (n + 1) = 2 * (-1) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have e1 := Q_rec k
    have e2 := Q_rec (k + 1)
    have hp : (-1 : Int) ^ (k + 1) = (-1) ^ k * (-1) := Int.pow_succ _ _
    rw [hp]
    have : 2 * ((-1 : Int) ^ k * (-1)) = -(2 * (-1) ^ k) := by grind
    rw [this, ← ih, e2, e1]
    grind

/-- 짝 합 : 2·Q (n + 1) = P n + P (n + 2) · Q (n + 1) = P n + P (n + 1) -/
theorem pell_sum (n : Nat) : 2 * Q (n + 1) = P n + P (n + 2) ∧ Q (n + 1) = P n + P (n + 1) := by
  have e := P_rec n
  have h1 := step_P n
  have h2 := step_Q n
  constructor <;> omega

/-- δ² = 3 + 2√2 를 한 번 곱하기 : Q (n + 2) = 3·Q n + 4·P n · P (n + 2) = 2·Q n + 3·P n -/
theorem step2 (n : Nat) : Q (n + 2) = 3 * Q n + 4 * P n ∧ P (n + 2) = 2 * Q n + 3 * P n := by
  have a1 := step_Q n
  have a2 := step_P n
  have b1 : Q (n + 2) = Q (n + 1) + 2 * P (n + 1) := step_Q (n + 1)
  have b2 : P (n + 2) = Q (n + 1) + P (n + 1) := step_P (n + 1)
  constructor <;> omega

/-- 두 배 (함께 귀납) : P (2n) = 2·P n·Q n · Q (2n) = Q n² + 2·P n² -/
theorem double_both (n : Nat) :
    P (2 * n) = 2 * (P n * Q n) ∧ Q (2 * n) = Q n * Q n + 2 * (P n * P n) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    have hk : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hk]
    obtain ⟨s1, s2⟩ := step2 (2 * k)
    rw [s1, s2, i1, i2, step_Q k, step_P k]
    constructor <;> grind

/-- 4. 두 배 : P (2n) = 2·P n·Q n -/
theorem double_P (n : Nat) : P (2 * n) = 2 * (P n * Q n) := (double_both n).1

/-- 4'. 두 배 : Q (2n) = Q n² + 2·P n² -/
theorem double_Q (n : Nat) : Q (2 * n) = Q n * Q n + 2 * (P n * P n) := (double_both n).2

/-- 틈 : Q n · Q n − 2 · P n · P n 는 1 또는 −1 (노름의 따름 정리) -/
theorem silver_power_gap (n : Nat) :
    Q n * Q n - 2 * P n * P n = 1 ∨ Q n * Q n - 2 * P n * P n = -1 := by
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
  exact h n

theorem neg_one_pow_even (m : Nat) : (-1 : Int) ^ (2 * m) = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Int.pow_succ, Int.pow_succ, ih]; decide

/-- 5. 펠 방정식 : Q (2n)² − 2·P (2n)² = 1 -/
theorem pell_even (n : Nat) : Q (2 * n) * Q (2 * n) - 2 * P (2 * n) * P (2 * n) = 1 := by
  rw [norm, neg_one_pow_even]

/-! ## 6. Z[√2] 의 쌍 산술 — δ = (1, 1) · 1/δ = δ − 2 -/

/-- (a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2 -/
def zmul (u v : Int × Int) : Int × Int := (u.1 * v.1 + 2 * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

def zpow (u : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => zmul (zpow u n) u

/-- δⁿ = Qₙ + Pₙ √2 : (1, 1)ⁿ = (Qₙ, Pₙ) -/
theorem zpow_delta (n : Nat) : zpow (1, 1) n = (Q n, P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show zmul (zpow (1, 1) n) (1, 1) = (Q (n + 1), P (n + 1))
    rw [ih, step_Q, step_P]
    simp only [zmul]
    congr 1 <;> grind

/-- 켤레와의 곱 : (Qₙ + Pₙ√2)(Qₙ − Pₙ√2) = (−1)ⁿ -/
theorem zmul_conj (n : Nat) : zmul (Q n, P n) (Q n, -P n) = ((-1) ^ n, 0) := by
  simp only [zmul]
  rw [← norm n]
  congr 1 <;> grind

/-- 되돌림 : (1 + √2)(−1 + √2) = 1 , 그리고 −1 + √2 = δ − 2 -/
theorem silver_inv : zmul (1, 1) (-1, 1) = (1, 0) ∧ ((-1 : Int), (1 : Int)) = ((1 : Int) - 2, (1 : Int)) := by
  decide

/-- δ² = 2δ + 1 -/
theorem silver_sq : zmul (1, 1) (1, 1) = (2 * 1 + 1, 2 * 1) := by decide

/-! ## 7. 금속비 가족 x = (n + √(n² + 4))/2 — 2x 를 Z[√D] 의 쌍 (n, 1) 로 적는다 (D = n² + 4) -/

/-- Z[√D] 의 곱 -/
def zmulD (D : Int) (u v : Int × Int) : Int × Int := (u.1 * v.1 + D * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- 수 꼴 : s² = n² + 4 이면 (n + s)² = 2n(n + s) + 4 · (n + s)(s − n) = 4
(x = (n + s)/2 에서 x² = n x + 1 · x (x − n) = 1 의 분모를 걷어낸 꼴) -/
theorem metallic (n s : Int) (hs : s * s = n * n + 4) :
    (n + s) * (n + s) = 2 * n * (n + s) + 4 ∧ (n + s) * (s - n) = 4 := by
  constructor <;> grind

/-- 쌍 꼴 : Z[√(n² + 4)] 안에서 (n + √D)² = 2n·(n + √D) + 4 · (n + √D)(−n + √D) = 4 -/
theorem metallic_pair (n : Int) :
    zmulD (n * n + 4) (n, 1) (n, 1) = (2 * n * n + 4, 2 * n) ∧
    zmulD (n * n + 4) (n, 1) (-n, 1) = (4, 0) := by
  simp only [zmulD]
  constructor <;> congr 1 <;> grind

/-- n = 1 황금 (D = 5) · n = 2 은 (D = 8 , (2 + √8)/2 = 1 + √2 : 쌍 (2, 1)_√8 은 (2, 2)_√2 = 2δ) -/
theorem metallic_one_two :
    zmulD 5 (1, 1) (1, 1) = (6, 2) ∧ zmulD 8 (2, 1) (2, 1) = (12, 4) ∧
    zmul (2, 2) (2, 2) = (12, 8) := by
  decide

/-! ## 소수 — (1 + √2)ⁿ 의 이항 전개 -/

/-- (√2)^k = (r2 k).1 + (r2 k).2 · √2 -/
def r2 : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => (2 * (r2 n).2, (r2 n).1)

theorem r2_parity (m : Nat) : r2 (2 * m) = (2 ^ m, 0) ∧ r2 (2 * m + 1) = (0, 2 ^ m) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    have e1 : r2 (2 * (m + 1)) = (2 * (r2 (2 * m + 1)).2, (r2 (2 * m + 1)).1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; rfl
    have e2 : r2 (2 * (m + 1) + 1) = (2 * (r2 (2 * (m + 1))).2, (r2 (2 * (m + 1))).1) := rfl
    have e3 : r2 (2 * (m + 1)) = (2 ^ (m + 1), 0) := by
      rw [e1, ih.2, Int.pow_succ, Int.mul_comm]
    exact ⟨e3, by rw [e2, e3]; simp⟩

/-- (1 + √2)ⁿ = Σ C(n, k)(√2)ᵏ 의 두 성분이 곧 Qₙ · Pₙ -/
theorem QP_binom (n : Nat) : Q n = bt (fun k => (r2 k).1) n ∧ P n = bt (fun k => (r2 k).2) n := by
  induction n with
  | zero => exact ⟨by rw [bt_zero]; rfl, by rw [bt_zero]; rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [bt_succ, bt_succ, step_Q, step_P]
    rw [show (fun k => (r2 (k + 1)).1) = (fun k => 2 * (r2 k).2) from rfl, bt_mul]
    rw [show (fun k => (r2 (k + 1)).2) = (fun k => (r2 k).1) from rfl]
    rw [← h1, ← h2]
    constructor <;> omega

/-- C. 모든 소수 p 에서 Qₚ ≡ 1 (mod p) -/
theorem half_pell_prime {p : Nat} (hp : Prime p) : (p : Int) ∣ Q p - 1 := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · subst h; exact ⟨1, by decide⟩
  · have hA := bt_prime hp (fun k => (r2 k).1)
    have hz : (r2 p).1 = 0 := by rw [h, (r2_parity m).2]
    have h0 : (r2 0).1 = 1 := rfl
    simp only [hz, h0] at hA
    rw [← (QP_binom p).1] at hA
    have e : Q p - 1 - 0 = Q p - 1 := by omega
    rwa [e] at hA

/-- D. 모든 홀수 소수 p 에서 Pₚ ≡ 2^((p−1)/2) (mod p) -/
theorem pell_prime {p : Nat} (hp : Prime p) (h2 : p ≠ 2) : (p : Int) ∣ P p - 2 ^ ((p - 1) / 2) := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · exact absurd h h2
  · have hB := bt_prime hp (fun k => (r2 k).2)
    have hz : (r2 p).2 = 2 ^ m := by rw [h, (r2_parity m).2]
    have h0 : (r2 0).2 = 0 := rfl
    simp only [hz, h0] at hB
    rw [← (QP_binom p).2] at hB
    have hm : (p - 1) / 2 = m := by omega
    rw [hm]
    have e : P p - 0 - 2 ^ m = P p - 2 ^ m := by omega
    rwa [e] at hB

/-! ## E. 제2 보충 법칙 — 가우스 합 τ = x − x³ (Z[x]/(x⁴ + 1) 안에서) -/

/-- Z[x]/(x⁴ + 1) 의 원소 a0 + a1 x + a2 x² + a3 x³ -/
structure R4 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
deriving DecidableEq

namespace R4

theorem ext' {u v : R4} (h0 : u.a0 = v.a0) (h1 : u.a1 = v.a1) (h2 : u.a2 = v.a2)
    (h3 : u.a3 = v.a3) : u = v := by
  cases u; cases v; simp_all

def one : R4 := ⟨1, 0, 0, 0⟩
def X : R4 := ⟨0, 1, 0, 0⟩
def add (u v : R4) : R4 := ⟨u.a0 + v.a0, u.a1 + v.a1, u.a2 + v.a2, u.a3 + v.a3⟩
def smul (c : Int) (u : R4) : R4 := ⟨c * u.a0, c * u.a1, c * u.a2, c * u.a3⟩
/-- x⁴ = −1 이므로 넘치는 항은 부호를 바꿔 접힌다 -/
def mul (u v : R4) : R4 :=
  ⟨u.a0 * v.a0 + u.a1 * (-v.a3) + u.a2 * (-v.a2) + u.a3 * (-v.a1),
   u.a0 * v.a1 + u.a1 * v.a0 + u.a2 * (-v.a3) + u.a3 * (-v.a2),
   u.a0 * v.a2 + u.a1 * v.a1 + u.a2 * v.a0 + u.a3 * (-v.a3),
   u.a0 * v.a3 + u.a1 * v.a2 + u.a2 * v.a1 + u.a3 * v.a0⟩
def pow (u : R4) : Nat → R4
  | 0 => one
  | n + 1 => mul (pow u n) u

theorem mul_comm (u v : R4) : mul u v = mul v u := by
  apply ext' <;> simp only [mul] <;> grind

theorem mul_assoc (u v w : R4) : mul (mul u v) w = mul u (mul v w) := by
  apply ext' <;> simp only [mul] <;> grind

theorem mul_one_add (u y : R4) : mul u (add one y) = add u (mul u y) := by
  apply ext' <;> simp only [mul, add, one] <;> grind

theorem smul_mul (c : Int) (u v : R4) : mul (smul c u) v = smul c (mul u v) := by
  apply ext' <;> simp only [mul, smul] <;> grind

theorem mul_smul (c : Int) (u v : R4) : mul u (smul c v) = smul c (mul u v) := by
  apply ext' <;> simp only [mul, smul] <;> grind

theorem smul_smul (c d : Int) (u : R4) : smul c (smul d u) = smul (c * d) u := by
  apply ext' <;> simp only [smul] <;> grind

theorem pow_mul_distrib (u v : R4) (n : Nat) : pow (mul u v) n = mul (pow u n) (pow v n) := by
  induction n with
  | zero => apply ext' <;> simp [pow, mul, one]
  | succ n ih =>
    simp only [pow]
    rw [ih, mul_assoc, ← mul_assoc (pow v n) u v, mul_comm (pow v n) u, mul_assoc u, ← mul_assoc]

theorem pow_smul (c : Int) (u : R4) (n : Nat) : pow (smul c u) n = smul (c ^ n) (pow u n) := by
  induction n with
  | zero => apply ext' <;> simp [pow, smul, one]
  | succ n ih =>
    simp only [pow]
    rw [ih, smul_mul, mul_smul, smul_smul, Int.pow_succ]

/-- 성분별 합동 -/
def cg (p : Nat) (u v : R4) : Prop :=
  (p : Int) ∣ u.a0 - v.a0 ∧ (p : Int) ∣ u.a1 - v.a1 ∧ (p : Int) ∣ u.a2 - v.a2 ∧
  (p : Int) ∣ u.a3 - v.a3

theorem cg_refl (p : Nat) (u : R4) : cg p u u := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

open GoldenPrimeAll.R (dsub_add dsub_mul)

theorem dsub_neg {d a a' : Int} (h : d ∣ a - a') : d ∣ (-a) - (-a') := by
  have := Int.dvd_neg.mpr h; rwa [show -(a - a') = -a - -a' by omega] at this

theorem cg_mul {p : Nat} {u u' v v' : R4} (hu : cg p u u') (hv : cg p v v') :
    cg p (mul u v) (mul u' v') := by
  obtain ⟨h0, h1, h2, h3⟩ := hu
  obtain ⟨k0, k1, k2, k3⟩ := hv
  have n1 := dsub_neg k1
  have n2 := dsub_neg k2
  have n3 := dsub_neg k3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mul]
  · exact dsub_add (dsub_add (dsub_add (dsub_mul h0 k0) (dsub_mul h1 n3)) (dsub_mul h2 n2)) (dsub_mul h3 n1)
  · exact dsub_add (dsub_add (dsub_add (dsub_mul h0 k1) (dsub_mul h1 k0)) (dsub_mul h2 n3)) (dsub_mul h3 n2)
  · exact dsub_add (dsub_add (dsub_add (dsub_mul h0 k2) (dsub_mul h1 k1)) (dsub_mul h2 k0)) (dsub_mul h3 n3)
  · exact dsub_add (dsub_add (dsub_add (dsub_mul h0 k3) (dsub_mul h1 k2)) (dsub_mul h2 k1)) (dsub_mul h3 k0)

end R4

open R4

/-- 네 항 일차 결합의 합 -/
theorem sm_lin4 (n : Nat) (f0 f1 f2 f3 : Nat → Int) (b0 b1 b2 b3 : Int) :
    sm n (fun i => f0 i * b0 + f1 i * b1 + f2 i * b2 + f3 i * b3)
      = sm n f0 * b0 + sm n f1 * b1 + sm n f2 * b2 + sm n f3 * b3 := by
  induction n with
  | zero => simp [sm]
  | succ n ih => simp only [sm_succ]; rw [ih]; grind

theorem bt_lin4 (n : Nat) (f0 f1 f2 f3 : Nat → Int) (b0 b1 b2 b3 : Int) :
    bt (fun i => f0 i * b0 + f1 i * b1 + f2 i * b2 + f3 i * b3) n
      = bt f0 n * b0 + bt f1 n * b1 + bt f2 n * b2 + bt f3 n * b3 := by
  unfold bt
  rw [← sm_lin4]
  apply sm_congr
  intro i _
  grind

/-- Z[x]/(x⁴ + 1) 안의 이항 정리 (성분별) : (1 + y)ⁿ = Σ C(n, k) yᵏ -/
theorem binomR4 (y : R4) (n : Nat) :
    (pow (add one y) n).a0 = bt (fun k => (pow y k).a0) n ∧
    (pow (add one y) n).a1 = bt (fun k => (pow y k).a1) n ∧
    (pow (add one y) n).a2 = bt (fun k => (pow y k).a2) n ∧
    (pow (add one y) n).a3 = bt (fun k => (pow y k).a3) n := by
  induction n with
  | zero => simp [bt_zero, pow]
  | succ n ih =>
    obtain ⟨i0, i1, i2, i3⟩ := ih
    have e : pow (add one y) (n + 1) = add (pow (add one y) n) (mul (pow (add one y) n) y) := by
      simp only [pow]; rw [mul_one_add]
    rw [e]
    generalize pow (add one y) n = W at i0 i1 i2 i3 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bt_succ, pow, mul, add] <;> rw [bt_lin4] <;>
      rw [i0, i1, i2, i3]

/-- Z[x]/(x⁴ + 1) 안의 신입생의 꿈 : (1 + y)^p ≡ 1 + y^p -/
theorem freshmanR4 {p : Nat} (hp : Prime p) (y : R4) : cg p (pow (add one y) p) (add one (pow y p)) := by
  obtain ⟨i0, i1, i2, i3⟩ := binomR4 y p
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [i0]; have := bt_prime hp (fun k => (pow y k).a0); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i1]; have := bt_prime hp (fun k => (pow y k).a1); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i2]; have := bt_prime hp (fun k => (pow y k).a2); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i3]; have := bt_prime hp (fun k => (pow y k).a3); simp only [add]; simpa [pow, one, Int.sub_sub] using this

/-- xᵏ 은 x^(k mod 8) (x⁴ = −1) -/
def basis : Nat → R4
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

theorem pow_X (k : Nat) : pow X k = basis (k % 8) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow]
    rw [ih]
    have h : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨
        k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
    rcases h with h | h | h | h | h | h | h | h
    · rw [h, show (k + 1) % 8 = 1 by omega]; decide
    · rw [h, show (k + 1) % 8 = 2 by omega]; decide
    · rw [h, show (k + 1) % 8 = 3 by omega]; decide
    · rw [h, show (k + 1) % 8 = 4 by omega]; decide
    · rw [h, show (k + 1) % 8 = 5 by omega]; decide
    · rw [h, show (k + 1) % 8 = 6 by omega]; decide
    · rw [h, show (k + 1) % 8 = 7 by omega]; decide
    · rw [h, show (k + 1) % 8 = 0 by omega]; decide

/-- 가우스 합 τ = x − x³ = x (1 − x²) (x 는 여덟째 단위근 · τ = x + x⁻¹ = √2) -/
def tau : R4 := ⟨0, 1, 0, -1⟩
def hm : R4 := add one (smul (-1) (mul X X))

theorem tau_factor : tau = mul X hm := by decide

/-- τ² = 2 (그래서 τ^(2j+1) = 2ʲ τ) -/
theorem tau_sq : mul tau tau = smul 2 one := by decide

theorem tau_pow_odd (j : Nat) : pow tau (2 * j + 1) = smul (2 ^ j) tau := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [e, show pow tau (2 * j + 1 + 1 + 1) = mul (mul (pow tau (2 * j + 1)) tau) tau from rfl, ih,
      smul_mul, smul_mul]
    have g3 : mul (mul tau tau) tau = smul 2 tau := by decide
    rw [g3, smul_smul, Int.pow_succ]

theorem neg_one_pow_odd (m : Nat) : (-1 : Int) ^ (2 * m + 1) = -1 := by
  rw [Int.pow_succ, neg_one_pow_even]; decide

/-- 프로베니우스 : τ^p ≡ x^p (1 − x^(2p)) (홀수 소수) -/
theorem gauss_frob {p m : Nat} (hp : Prime p) (hm2 : p = 2 * m + 1) :
    cg p (pow tau p)
      (mul (basis (p % 8)) (add one (smul (-1) (mul (basis (p % 8)) (basis (p % 8)))))) := by
  rw [tau_factor, pow_mul_distrib, pow_X]
  have c1 : cg p (pow hm p) (add one (smul (-1) (mul (basis (p % 8)) (basis (p % 8))))) := by
    have := freshmanR4 hp (smul (-1) (mul X X))
    rw [pow_smul, pow_mul_distrib, pow_X, hm2, neg_one_pow_odd, ← hm2] at this
    exact this
  exact cg_mul (cg_refl p _) c1

/-- E. 제2 보충 법칙 (오일러 꼴) : 모든 홀수 소수 p 에서
p ≡ ±1 (mod 8) 이면 2^((p−1)/2) ≡ 1 , p ≡ ±3 (mod 8) 이면 2^((p−1)/2) ≡ −1 (mod p) -/
theorem two_supplement {p : Nat} (hp : Prime p) :
    ((p % 8 = 1 ∨ p % 8 = 7) → (p : Int) ∣ 2 ^ ((p - 1) / 2) - 1) ∧
    ((p % 8 = 3 ∨ p % 8 = 5) → (p : Int) ∣ 2 ^ ((p - 1) / 2) + 1) := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · subst h; exact ⟨fun h => by omega, fun h => by omega⟩
  · have hmm : (p - 1) / 2 = m := by omega
    rw [hmm]
    have hf := gauss_frob hp h
    rw [h, tau_pow_odd, ← h] at hf
    have v : ∀ r, (r = 1 ∨ r = 7 →
          mul (basis r) (add one (smul (-1) (mul (basis r) (basis r)))) = tau) ∧
        (r = 3 ∨ r = 5 →
          mul (basis r) (add one (smul (-1) (mul (basis r) (basis r)))) = smul (-1) tau) := by
      intro r
      constructor
      · intro hr; rcases hr with hr | hr <;> subst hr <;> decide
      · intro hr; rcases hr with hr | hr <;> subst hr <;> decide
    constructor
    · intro hr
      rw [(v (p % 8)).1 hr] at hf
      have key := hf.2.1
      simpa [smul, tau] using key
    · intro hr
      rw [(v (p % 8)).2 hr] at hf
      have key := hf.2.1
      simp only [smul, tau] at key
      have : 2 ^ m * 1 - -1 * 1 = (2 : Int) ^ m + 1 := by omega
      rw [this] at key
      exact key

/-! ## 따름 : 펠 수의 두 줄 (모든 소수) -/

/-- Pₚ ≡ (2/p) (mod p) : p ≡ ±1 (mod 8) 이면 Pₚ ≡ 1 , p ≡ ±3 (mod 8) 이면 Pₚ ≡ −1 , 그리고 2 ∣ P₂ -/
theorem pell_prime_legendre {p : Nat} (hp : Prime p) :
    ((p % 8 = 1 ∨ p % 8 = 7) → (p : Int) ∣ P p - 1) ∧
    ((p % 8 = 3 ∨ p % 8 = 5) → (p : Int) ∣ P p + 1) ∧
    (p = 2 → (p : Int) ∣ P p) := by
  have hE := two_supplement hp
  refine ⟨fun hr => ?_, fun hr => ?_, fun h2 => ?_⟩
  · have hD := pell_prime hp (by omega)
    exact GoldenPrimeAll.R.dsub_trans hD (hE.1 hr)
  · have hD := pell_prime hp (by omega)
    have := Int.dvd_add hD (hE.2 hr)
    rwa [show P p - 2 ^ ((p - 1) / 2) + (2 ^ ((p - 1) / 2) + 1) = P p + 1 by omega] at this
  · subst h2; exact ⟨1, by decide⟩

/-- p ∣ P_{p − (2/p)} : p ≡ ±1 (mod 8) 이면 p ∣ P (p − 1) , p ≡ ±3 (mod 8) 이면 p ∣ P (p + 1) -/
theorem pell_rank {p : Nat} (hp : Prime p) :
    ((p % 8 = 1 ∨ p % 8 = 7) → (p : Int) ∣ P (p - 1)) ∧
    ((p % 8 = 3 ∨ p % 8 = 5) → (p : Int) ∣ P (p + 1)) := by
  have hQ := half_pell_prime hp
  have hF := pell_prime_legendre hp
  have hs := step_P p
  constructor
  · intro hr
    have h1 := hF.1 hr
    have hrec : P (p - 1 + 2) = 2 * P (p - 1 + 1) + P (p - 1) := rfl
    rw [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at hrec
    have := Int.dvd_sub hQ h1
    rwa [show Q p - 1 - (P p - 1) = P (p - 1) by omega] at this
  · intro hr
    have h1 := hF.2.1 hr
    have := Int.dvd_add hQ h1
    rwa [show Q p - 1 + (P p + 1) = P (p + 1) by omega] at this

end Silver

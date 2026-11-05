/-
격자 위의 정다각형 — 정수 좌표에 꼭짓점이 모두 놓이는 정다각형 (린 4 코어만 · Mathlib 없음)

정다각형의 변 벡터 v₀, v₁, … 은 길이² 가 모두 S, 이웃한 두 변의 내적이 모두 c 이다(꺾임 θ, cos θ = c/S).
평면에서 같은 쪽으로 꺾이면(또는 어느 차원이든 한 평면 위에서 같은 각으로 돌면) 돌림 점화식
      S · v_{k+2} = 2c · v_{k+1} − S · v_k
이 성립한다. 이 점화식의 동차 풀이가 바일 창의 뤼카 수열 U(q, a) 를 q = S², a = 2c 로 쓴 것이다:
      S^k · v_{k+1} = U(S², 2c, k + 1) · v₁ − S · U(S², 2c, k) · v₀.
다각형이 n 변에서 닫히면(v_n = v₀) U(S², 2c, n) = 0 이고, 유리근 꼴의 내려가기로 2c/S 가 정수가 된다.
|cos θ| < 1 이므로 2c/S ∈ {−1, 0, 1}, 곧 바깥각 (꺾임) 은 120° · 90° · 60° 뿐 (안각 60° · 90° · 120°) — 한 평면 위의 정삼각형 · 정사각형 · 정육각형.
«한 평면에서 같은 방향으로 돈다» 는 조건은 높은 차원에서는 가정이고, 평면 Z² 에서는 같은 외적에서 증명한다. 꼬인 다각형은 대상이 아니다.
평면 Z² 에서는 라그랑주 항등식 S² = c² + w² (w = 이웃 변의 외적) 때문에 ±1 이 √3 으로 막혀 정사각형만 남는다.

검증 : lake build
-/
import Trombo.Crystal
import Trombo.Twist

namespace Trombo.Polygon

/-- 바일 창의 뤼카 수열 U(q, a) : U₀ = 0 · U₁ = 1 · U_{n+2} = a U_{n+1} − q U_n -/
abbrev V := Trombo.WeilAll.U

theorem V_zero (q a : Int) : V q a 0 = 0 := rfl
theorem V_one (q a : Int) : V q a 1 = 1 := rfl
theorem V_two (q a : Int) (n : Nat) : V q a (n + 2) = a * V q a (n + 1) - q * V q a n := rfl

/-! ## 1. 뤼카 수열의 두 성질 — 동차성과 합동 -/

/-- 동차성 : U(g²q, g a, n + 1) = gⁿ · U(q, a, n + 1) -/
theorem V_homog (g q a : Int) : ∀ n : Nat,
    V (g ^ 2 * q) (g * a) (n + 1) = g ^ n * V q a (n + 1) ∧
    V (g ^ 2 * q) (g * a) (n + 2) = g ^ (n + 1) * V q a (n + 2) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [V_one]
    · rw [V_two, V_two, V_one, V_one, V_zero, V_zero]; grind
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [V_two (g ^ 2 * q) (g * a) (n + 1), V_two q a (n + 1)]
    rw [show n + 1 + 1 = n + 2 from rfl, h2, h1]
    have e1 : g ^ (n + 1) = g ^ n * g := Int.pow_succ g n
    have e2 : g ^ (n + 1 + 1) = g ^ n * g * g := by rw [Int.pow_succ, e1]
    rw [e2, e1]
    grind

/-- 합동 : q ∣ U(q², p, n + 1) − pⁿ -/
theorem V_cong (q p : Int) : ∀ n : Nat,
    q ∣ V (q ^ 2) p (n + 1) - p ^ n ∧ q ∣ V (q ^ 2) p (n + 2) - p ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [V_one]
    · rw [V_two, V_one, V_zero]; exact ⟨0, by grind⟩
  | succ n ih =>
    obtain ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩ := ih
    refine ⟨⟨k2, h2⟩, ?_⟩
    rw [V_two (q ^ 2) p (n + 1), show n + 1 + 1 = n + 2 from rfl]
    refine ⟨p * k2 - q * V (q ^ 2) p (n + 1), ?_⟩
    have e : p ^ (n + 1 + 1) = p * p ^ (n + 1) := by rw [Int.pow_succ]; grind
    rw [e]
    grind

/-! ## 2. 유리근 꼴 : U(S², 2c, n) = 0 이면 S ∣ 2c -/

/-- ★ 0 < S 이고 U(S², 2c, m + 1) = 0 이면 S 가 2c 를 나눈다 (2c/S 는 정수) -/
theorem integral_turn (S c : Int) (hS : 0 < S) (m : Nat) (h : V (S ^ 2) (2 * c) (m + 1) = 0) :
    S ∣ 2 * c := by
  -- g = gcd(|2c|, S) · 2c = g p · S = g q · p, q 서로소
  let G := Nat.gcd (2 * c).natAbs S.natAbs
  have hG : 0 < G := Nat.gcd_pos_of_pos_right _ (by omega)
  have dG1 : (G : Int) ∣ 2 * c := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have dG2 : (G : Int) ∣ S := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨p, hp⟩ := dG1
  obtain ⟨q, hq⟩ := dG2
  have hpa : (2 * c).natAbs = G * p.natAbs := by rw [hp, Int.natAbs_mul]; rfl
  have hqa : S.natAbs = G * q.natAbs := by rw [hq, Int.natAbs_mul]; rfl
  have cop : Nat.Coprime p.natAbs q.natAbs := by
    have := Nat.coprime_div_gcd_div_gcd (m := (2 * c).natAbs) (n := S.natAbs) hG
    have e1 : (2 * c).natAbs / G = p.natAbs := by rw [hpa, Nat.mul_div_cancel_left _ hG]
    have e2 : S.natAbs / G = q.natAbs := by rw [hqa, Nat.mul_div_cancel_left _ hG]
    rw [e1, e2] at this
    exact this
  -- U(S², 2c, m+1) = G^m · U(q², p, m+1)
  have hom := (V_homog (G : Int) (q ^ 2) p m).1
  have e3 : (G : Int) ^ 2 * q ^ 2 = S ^ 2 := by rw [hq]; grind
  rw [e3, ← hp] at hom
  rw [hom] at h
  have hG' : (G : Int) ^ m ≠ 0 := Int.pow_ne_zero (by omega)
  have h0 : V (q ^ 2) p (m + 1) = 0 := by
    rcases Int.mul_eq_zero.mp h with h' | h'
    · exact absurd h' hG'
    · exact h'
  -- q ∣ p^m
  have hd := (V_cong q p m).1
  rw [h0, Int.zero_sub, Int.dvd_neg] at hd
  have hd' : q.natAbs ∣ p.natAbs ^ m := by
    rw [← Int.natAbs_pow]; exact Int.natAbs_dvd_natAbs.mpr hd
  have hq1 : q.natAbs = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m cop.symm) hd'
  have hqpos : 0 < q := by
    rcases Int.lt_or_lt_of_ne (show q ≠ 0 by omega) with h1 | h1
    · exfalso
      have : S < 0 := by rw [hq]; exact Int.mul_neg_of_pos_of_neg (by omega) h1
      omega
    · exact h1
  have hq_one : q = 1 := by omega
  rw [hq, hq_one, Int.mul_one]
  exact ⟨p, hp⟩

/-- ★ 꺾임은 120° · 90° · 60° 뿐 : c² < S² (이웃 변이 평행하지 않음) 이고 U(S², 2c, m + 1) = 0 이면 2c ∈ {−S, 0, S} -/
theorem turn_three (S c : Int) (hS : 0 < S) (hc : c ^ 2 < S ^ 2) (m : Nat)
    (h : V (S ^ 2) (2 * c) (m + 1) = 0) : 2 * c = -S ∨ c = 0 ∨ 2 * c = S := by
  obtain ⟨t, ht⟩ := integral_turn S c hS m h
  -- 4c² = S² t² < 4 S² → t² < 4
  have h4 : S ^ 2 * t ^ 2 < S ^ 2 * 4 := by
    have : (2 * c) ^ 2 = S ^ 2 * t ^ 2 := by rw [ht]; grind
    grind
  have hS2 : 0 < S ^ 2 := by
    have := Int.mul_pos hS hS; grind
  have ht2 : t ^ 2 < 4 := by
    rcases Int.lt_or_le (t ^ 2) 4 with h' | h'
    · exact h'
    · exfalso
      have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hS2)
      omega
  have hsq : t * t < 4 := by grind
  have hb1 : -1 ≤ t := by
    rcases Int.lt_or_le t (-1) with h' | h'
    · have := Int.mul_nonneg (show 0 ≤ -t - 2 by omega) (show 0 ≤ -t by omega)
      have e : (-t - 2) * (-t) = t * t + 2 * t := by grind
      omega
    · exact h'
  have hb2 : t ≤ 1 := by
    rcases Int.lt_or_le 1 t with h' | h'
    · have := Int.mul_nonneg (show 0 ≤ t - 2 by omega) (show 0 ≤ t by omega)
      have e : (t - 2) * t = t * t - 2 * t := by grind
      omega
    · exact h'
  rcases (show t = -1 ∨ t = 0 ∨ t = 1 by omega) with e | e | e <;> subst e
  · left; rw [ht]; grind
  · right; left; omega
  · right; right; rw [ht]; grind

/-! ## 3. 점화식의 풀이와 닫힘 -/

/-- 점화식 S a_{k+2} = 2c a_{k+1} − S a_k 의 풀이 : S^k a_{k+1} = U_{k+1} a₁ − S U_k a₀ (U = U(S², 2c)) -/
theorem solve (S c : Int) (a : Nat → Int) (hr : ∀ k, S * a (k + 2) = 2 * c * a (k + 1) - S * a k) :
    ∀ k : Nat, S ^ k * a (k + 1) = V (S ^ 2) (2 * c) (k + 1) * a 1 - S * V (S ^ 2) (2 * c) k * a 0 ∧
      S ^ (k + 1) * a (k + 2) = V (S ^ 2) (2 * c) (k + 2) * a 1 - S * V (S ^ 2) (2 * c) (k + 1) * a 0 := by
  intro k
  induction k with
  | zero =>
    constructor
    · simp [V_one, V_zero]
    · have h0 := hr 0
      rw [V_two, V_one, V_zero, Int.pow_one]
      grind
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show S ^ (k + 2) * a (k + 3) = V (S ^ 2) (2 * c) (k + 3) * a 1 - S * V (S ^ 2) (2 * c) (k + 2) * a 0
    have hk : S * a (k + 3) = 2 * c * a (k + 2) - S * a (k + 1) := hr (k + 1)
    have v3 : V (S ^ 2) (2 * c) (k + 3) = 2 * c * V (S ^ 2) (2 * c) (k + 2) - S ^ 2 * V (S ^ 2) (2 * c) (k + 1) :=
      V_two _ _ (k + 1)
    have v2 : V (S ^ 2) (2 * c) (k + 2) = 2 * c * V (S ^ 2) (2 * c) (k + 1) - S ^ 2 * V (S ^ 2) (2 * c) k :=
      V_two _ _ k
    have p2 : S ^ (k + 2) = S ^ (k + 1) * S := Int.pow_succ S (k + 1)
    have p1 : S ^ (k + 1) = S ^ k * S := Int.pow_succ S k
    have e : S ^ (k + 2) * a (k + 3) = 2 * c * (S ^ (k + 1) * a (k + 2)) - S ^ 2 * (S ^ k * a (k + 1)) := by
      rw [p2, p1, show S ^ 2 = S * S by grind]
      have m := congrArg (fun x => S ^ k * S * x) hk
      grind
    rw [e, h2, h1, v3]
    rw [v2]
    grind

/-- ★ 닫힘 : 두 내적 수열 a_k = v_k·v₀ · b_k = v_k·v₁ 이 점화식을 따르고 m + 1 걸음에 처음 값으로 돌아오면
    U(S², 2c, m + 1) = 0 -/
theorem closes (S c : Int) (hc : c ^ 2 ≠ S ^ 2) (a b : Nat → Int)
    (ha : ∀ k, S * a (k + 2) = 2 * c * a (k + 1) - S * a k) (hb : ∀ k, S * b (k + 2) = 2 * c * b (k + 1) - S * b k)
    (a0 : a 0 = S) (a1 : a 1 = c) (b0 : b 0 = c) (b1 : b 1 = S) (m : Nat) (am : a (m + 1) = S) (bm : b (m + 1) = c) :
    V (S ^ 2) (2 * c) (m + 1) = 0 := by
  have A := (solve S c a ha m).1
  have B := (solve S c b hb m).1
  have key : (c ^ 2 - S ^ 2) * V (S ^ 2) (2 * c) (m + 1) = 0 := by grind
  rcases Int.mul_eq_zero.mp key with h | h
  · exfalso; apply hc; omega
  · exact h

/-- U(q, a) 의 다섯째 · 일곱째 : a⁴ − 3a²q + q² · a⁶ − 5a⁴q + 6a²q² − q³ -/
theorem V_five_seven (q a : Int) :
    V q a 5 = a ^ 4 - 3 * a ^ 2 * q + q ^ 2 ∧ V q a 7 = a ^ 6 - 5 * a ^ 4 * q + 6 * a ^ 2 * q ^ 2 - q ^ 3 := by
  have h2 : V q a 2 = a * V q a 1 - q * V q a 0 := V_two q a 0
  have h3 : V q a 3 = a * V q a 2 - q * V q a 1 := V_two q a 1
  have h4 : V q a 4 = a * V q a 3 - q * V q a 2 := V_two q a 2
  have h5 : V q a 5 = a * V q a 4 - q * V q a 3 := V_two q a 3
  have h6 : V q a 6 = a * V q a 5 - q * V q a 4 := V_two q a 4
  have h7 : V q a 7 = a * V q a 6 - q * V q a 5 := V_two q a 5
  rw [V_one, V_zero] at h2
  rw [V_one] at h3
  constructor
  · rw [h5, h4, h3, h2]; grind
  · rw [h7, h6, h5, h4, h3, h2]; grind

/-- ★ 다섯 · 일곱 변에서는 닫히지 않는다 : 2c ∈ {−S, 0, S} 이면 U(S², 2c, 5) ≠ 0 · U(S², 2c, 7) ≠ 0 -/
theorem five_seven_open (S c : Int) (hS : 0 < S) (h : 2 * c = -S ∨ c = 0 ∨ 2 * c = S) :
    V (S ^ 2) (2 * c) 5 ≠ 0 ∧ V (S ^ 2) (2 * c) 7 ≠ 0 := by
  obtain ⟨e5, e7⟩ := V_five_seven (S ^ 2) (2 * c)
  rw [e5, e7]
  have s2 : 0 < S * S := Int.mul_pos hS hS
  have s4 : 0 < (S * S) * (S * S) := Int.mul_pos s2 s2
  have s6 : 0 < (S * S) * (S * S) * (S * S) := Int.mul_pos s4 s2
  rcases h with h | h | h
  · rw [h]; constructor <;> intro hh <;> grind
  · rw [show 2 * c = 0 by omega]; constructor <;> intro hh <;> grind
  · rw [h]; constructor <;> intro hh <;> grind

/-! ## 4. 어느 차원이든 — 정수 격자 Zᵈ -/

/-- 정수 벡터 (좌표 0 … d − 1) 의 내적 -/
def dot : Nat → (Nat → Int) → (Nat → Int) → Int
  | 0, _, _ => 0
  | d + 1, u, v => dot d u v + u d * v d

theorem dot_comm (u v : Nat → Int) : ∀ d, dot d u v = dot d v u := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih => simp only [dot, ih]; grind

theorem dot_lin (x y z : Nat → Int) (α β : Int) : ∀ d,
    dot d (fun i => α * x i - β * y i) z = α * dot d x z - β * dot d y z := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih => simp only [dot, ih]; grind

theorem dot_smul (x z : Nat → Int) (α : Int) : ∀ d, dot d (fun i => α * x i) z = α * dot d x z := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih => simp only [dot, ih]; grind

/-- 내적은 앞의 d 좌표만 본다 -/
theorem dot_congr (x y z : Nat → Int) : ∀ d, (∀ i, i < d → x i = y i) → dot d x z = dot d y z := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    simp only [dot]
    rw [ih (fun i hi => h i (by omega)), h d (by omega)]

/-- 한 평면 위 정다각형의 닫힘 (어느 차원이든 · 좌표 0 … d − 1) : 변 벡터 v₀, v₁, … 의 길이² S · 이웃 내적 c ·
    한 평면에서 같은 방향으로 돈다는 조건 (돌림 점화식 S v_{k+2} = 2c v_{k+1} − S v_k · 가정) ·
    m + 1 변에서 변의 방향이 돌아오면 (v_{m+1} = v₀) U(S², 2c, m + 1) = 0.
    평면 Z² 에서는 이 점화식을 같은 외적에서 증명한다 (plane_square). 꼬인 다각형 (정육면체의 페트리 육각형 등) 은 대상이 아니다. -/
theorem lattice_closes (d : Nat) (v : Nat → Nat → Int) (S c : Int) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (rot : ∀ k i, i < d → S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i)
    (m : Nat) (close : ∀ i, i < d → v (m + 1) i = v 0 i) : V (S ^ 2) (2 * c) (m + 1) = 0 := by
  have hrec (z : Nat → Int) : ∀ k, S * dot d (v (k + 2)) z = 2 * c * dot d (v (k + 1)) z - S * dot d (v k) z := by
    intro k
    rw [← dot_smul (v (k + 2)) z S d, ← dot_lin (v (k + 1)) (v k) z (2 * c) S d]
    exact dot_congr _ _ z d (fun i hi => rot k i hi)
  have hv (z : Nat → Int) : dot d (v (m + 1)) z = dot d (v 0) z := dot_congr _ _ z d close
  apply closes S c (by omega) (fun k => dot d (v k) (v 0)) (fun k => dot d (v k) (v 1)) (hrec (v 0)) (hrec (v 1))
  · exact len 0
  · show dot d (v 1) (v 0) = c
    rw [dot_comm]; exact adj 0
  · exact adj 0
  · exact len 1
  · show dot d (v (m + 1)) (v 0) = S
    rw [hv]; exact len 0
  · show dot d (v (m + 1)) (v 1) = c
    rw [hv]; exact adj 0

/-- ★ 어느 차원의 정수 격자든 한 평면 위의 정다각형 (별꼴 포함) 의 바깥각 (꺾임) 은 120° · 90° · 60° 뿐 (2c/S = −1 · 0 · 1) —
    안각으로는 60° · 90° · 120° : 정삼각형 · 정사각형 · 정육각형 -/
theorem lattice_regular (d : Nat) (v : Nat → Nat → Int) (S c : Int) (hS : 0 < S) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (rot : ∀ k i, i < d → S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i)
    (m : Nat) (close : ∀ i, i < d → v (m + 1) i = v 0 i) : 2 * c = -S ∨ c = 0 ∨ 2 * c = S :=
  turn_three S c hS hc m (lattice_closes d v S c hc len adj rot m close)

/-- ★ 그래서 변은 3 · 4 · 6 변마다 되풀이된다 (주기) : 바깥각 120° 면 v_{k+3} = v_k · 90° 면 v_{k+4} = v_k · 60° 면 v_{k+6} = v_k -/
theorem closes_in (S c : Int) (hS : 0 < S) (v : Nat → Nat → Int)
    (rot : ∀ k i, S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i) :
    (2 * c = -S → ∀ k i, v (k + 3) i = v k i) ∧ (c = 0 → ∀ k i, v (k + 4) i = v k i) ∧
    (2 * c = S → ∀ k i, v (k + 6) i = v k i) := by
  have hS0 : S ≠ 0 := by omega
  have cancel : ∀ x y : Int, S * x = S * y → x = y := fun x y h => Int.eq_of_mul_eq_mul_left hS0 h
  refine ⟨fun h k i => ?_, fun h k i => ?_, fun h k i => ?_⟩
  · have r0 : v (k + 2) i = -v (k + 1) i - v k i := cancel _ _ (by rw [rot k i, h]; grind)
    have r1 : v (k + 3) i = -v (k + 2) i - v (k + 1) i := cancel _ _ (by rw [rot (k + 1) i, h]; grind)
    rw [r1, r0]; grind
  · have r0 : v (k + 2) i = -v k i := cancel _ _ (by rw [rot k i, h]; grind)
    have r2 : v (k + 4) i = -v (k + 2) i := cancel _ _ (by rw [rot (k + 2) i, h]; grind)
    rw [r2, r0]; grind
  · have r : ∀ j, v (j + 2) i = v (j + 1) i - v j i := fun j => cancel _ _ (by rw [rot j i, h]; grind)
    have r3 : v (k + 3) i = -v k i := by
      have a1 := r (k + 1); have a0 := r k
      show v (k + 1 + 2) i = -v k i
      rw [a1, a0]; grind
    have r6 : v (k + 6) i = -v (k + 3) i := by
      have a1 := r (k + 4); have a0 := r (k + 3)
      show v (k + 4 + 2) i = -v (k + 3) i
      rw [a1, a0]; grind
    rw [r6, r3]; grind

/-- ★ 한 평면 위의 정오각형 · 정칠각형은 어느 차원의 정수 격자에도 없다 (정오각별 · 정칠각별도) -/
theorem no_pentagon_heptagon (d : Nat) (v : Nat → Nat → Int) (S c : Int) (hS : 0 < S) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (rot : ∀ k i, i < d → S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i) :
    ¬ (∀ i, i < d → v 5 i = v 0 i) ∧ ¬ (∀ i, i < d → v 7 i = v 0 i) := by
  have t3 := fun m close => lattice_regular d v S c hS hc len adj rot m close
  constructor
  · intro h5
    exact (five_seven_open S c hS (t3 4 h5)).1 (lattice_closes d v S c hc len adj rot 4 h5)
  · intro h7
    exact (five_seven_open S c hS (t3 6 h7)).2 (lattice_closes d v S c hc len adj rot 6 h7)

/-! ## 5. 평면 Z² — 정사각형뿐 -/

abbrev P2 := Int × Int
def dt (u v : P2) : Int := u.1 * v.1 + u.2 * v.2
def cr (u v : P2) : Int := u.1 * v.2 - u.2 * v.1

/-- 평면의 두 항등식 : |u|² v = (u·v) u + (u×v) Ju · |u|²|v|² = (u·v)² + (u×v)² (라그랑주) -/
theorem plane_id (u v : P2) :
    dt u u * v.1 = dt u v * u.1 - cr u v * u.2 ∧ dt u u * v.2 = dt u v * u.2 + cr u v * u.1 ∧
    dt u u * dt v v = dt u v ^ 2 + cr u v ^ 2 := by
  simp only [dt, cr]; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- ★ 평면 Z² 의 정다각형은 정사각형뿐 : 변의 길이² S · 이웃 변의 내적 c · 외적 w ≠ 0 이 모두 같고
    m + 1 변에서 닫히면 c = 0 (꺾임 90°) — 120° · 60° 는 √3 이 막는다 -/
theorem plane_square (v : Nat → P2) (S c w : Int) (hS : 0 < S) (hw : w ≠ 0)
    (len : ∀ k, dt (v k) (v k) = S) (adj : ∀ k, dt (v k) (v (k + 1)) = c) (crs : ∀ k, cr (v k) (v (k + 1)) = w)
    (m : Nat) (close : v (m + 1) = v 0) : c = 0 := by
  -- 같은 쪽으로 꺾이면 돌림 점화식
  have rot : ∀ k, S * (v (k + 2)).1 = 2 * c * (v (k + 1)).1 - S * (v k).1 ∧
      S * (v (k + 2)).2 = 2 * c * (v (k + 1)).2 - S * (v k).2 := by
    intro k
    obtain ⟨f1, f2, _⟩ := plane_id (v (k + 1)) (v (k + 2))
    obtain ⟨g1, g2, _⟩ := plane_id (v (k + 1)) (v k)
    have l := len (k + 1); have a1 := adj (k + 1); have c1 := crs (k + 1)
    have a0 := adj k; have c0 := crs k
    have s1 : dt (v (k + 1)) (v k) = c := by rw [← a0]; simp only [dt]; grind
    have s2 : cr (v (k + 1)) (v k) = -w := by rw [← c0]; simp only [cr]; grind
    rw [l, a1, c1] at f1 f2
    rw [l, s1, s2] at g1 g2
    constructor <;> grind
  -- 라그랑주 : S² = c² + w² 이므로 c² < S²
  have lag : S * S = c ^ 2 + w ^ 2 := by
    have := (plane_id (v 0) (v 1)).2.2
    rw [len 0, len 1, adj 0, crs 0] at this; exact this
  have w2 : 0 < w ^ 2 := by
    rcases Int.lt_or_lt_of_ne hw with h | h
    · have := Int.mul_pos_of_neg_of_neg h h; grind
    · have := Int.mul_pos h h; grind
  have hc : c ^ 2 < S ^ 2 := by grind
  -- 내적 수열로 닫힘
  have hrec (z : P2) : ∀ k, S * dt (v (k + 2)) z = 2 * c * dt (v (k + 1)) z - S * dt (v k) z := by
    intro k; obtain ⟨r1, r2⟩ := rot k; simp only [dt]; grind
  have hV := closes S c (by omega) (fun k => dt (v k) (v 0)) (fun k => dt (v k) (v 1)) (hrec (v 0)) (hrec (v 1))
    (len 0) (by show dt (v 1) (v 0) = c; rw [← adj 0]; simp only [dt]; grind) (adj 0) (len 1) m
    (by show dt (v (m + 1)) (v 0) = S; rw [close]; exact len 0)
    (by show dt (v (m + 1)) (v 1) = c; rw [close]; exact adj 0)
  rcases turn_three S c hS hc m hV with h | h | h
  · exfalso
    have e : (2 * w) ^ 2 = 3 * S ^ 2 := by grind
    have := Trombo.Twist.sqrt_three ((2 * w).natAbs + S.natAbs) S (2 * w) (by omega) e
    omega
  · exact h
  · exfalso
    have e : (2 * w) ^ 2 = 3 * S ^ 2 := by grind
    have := Trombo.Twist.sqrt_three ((2 * w).natAbs + S.natAbs) S (2 * w) (by omega) e
    omega

/-- ★ 평면 Z² 에는 정오각형 (정오각별) 이 없다 -/
theorem plane_no_pentagon (v : Nat → P2) (S c w : Int) (hS : 0 < S) (hw : w ≠ 0)
    (len : ∀ k, dt (v k) (v k) = S) (adj : ∀ k, dt (v k) (v (k + 1)) = c) (crs : ∀ k, cr (v k) (v (k + 1)) = w)
    (close : v 5 = v 0) : False := by
  have hc0 := plane_square v S c w hS hw len adj crs 4 close
  -- 정사각형 (90°) 은 네 변에서 닫히고 다섯 변에서는 v₅ = v₁ ≠ v₀
  have rot : ∀ k, S * (v (k + 2)).1 = -(S * (v k).1) ∧ S * (v (k + 2)).2 = -(S * (v k).2) := by
    intro k
    obtain ⟨f1, f2, _⟩ := plane_id (v (k + 1)) (v (k + 2))
    obtain ⟨g1, g2, _⟩ := plane_id (v (k + 1)) (v k)
    have l := len (k + 1); have a1 := adj (k + 1); have c1 := crs (k + 1)
    have a0 := adj k; have c0 := crs k
    have s1 : dt (v (k + 1)) (v k) = c := by rw [← a0]; simp only [dt]; grind
    have s2 : cr (v (k + 1)) (v k) = -w := by rw [← c0]; simp only [cr]; grind
    rw [l, a1, c1, hc0] at f1 f2
    rw [l, s1, s2, hc0] at g1 g2
    constructor <;> grind
  have hS0 : S ≠ 0 := by omega
  have r : ∀ k, v (k + 2) = (-(v k).1, -(v k).2) := by
    intro k
    obtain ⟨r1, r2⟩ := rot k
    have e1 : (v (k + 2)).1 = -(v k).1 := Int.eq_of_mul_eq_mul_left hS0 (by grind)
    have e2 : (v (k + 2)).2 = -(v k).2 := Int.eq_of_mul_eq_mul_left hS0 (by grind)
    exact Prod.ext e1 e2
  have h5 : v 5 = v 1 := by
    have a : v 5 = (-(v 3).1, -(v 3).2) := r 3
    have b : v 3 = (-(v 1).1, -(v 1).2) := r 1
    rw [a, b]; simp
  rw [h5] at close
  have e : dt (v 0) (v 1) = dt (v 0) (v 0) := by rw [close]
  rw [len 0, adj 0] at e
  omega

/-! ## 6. 있는 것 — Z² 의 정사각형 · Z³ 의 정삼각형과 정육각형 -/

/-- 좌표 목록으로 쓴 벡터 -/
def vec (l : List Int) : Nat → Int := fun i => l.getD i 0

/-- Z² 의 정사각형 : 변 (1, 0) · (0, 1) · (−1, 0) · (0, −1) — 길이² 1 · 이웃 내적 0 · 외적 1 · 합 0 -/
theorem square_exists :
    let e : List P2 := [(1, 0), (0, 1), (-1, 0), (0, -1)]
    (List.range 4).all (fun k => dt (e.getD k (0, 0)) (e.getD k (0, 0)) == 1 &&
      dt (e.getD k (0, 0)) (e.getD ((k + 1) % 4) (0, 0)) == 0 &&
      cr (e.getD k (0, 0)) (e.getD ((k + 1) % 4) (0, 0)) == 1) = true ∧
    e.foldl (fun s u => (s.1 + u.1, s.2 + u.2)) (0, 0) = (0, 0) := by
  decide

/-- Z³ 의 정삼각형 — 꼭짓점 (1, 1, 0) · (1, 0, 1) · (0, 1, 1) 의 변 벡터 : 변 길이² 2 · 이웃 내적 −1 (= −S/2 · 바깥각 120°) · 합 0 -/
theorem triangle_in_Z3 :
    let e : List (List Int) := [[0, -1, 1], [-1, 1, 0], [1, 0, -1]]
    (List.range 3).all (fun k => dot 3 (vec (e.getD k [])) (vec (e.getD k [])) == 2 &&
      dot 3 (vec (e.getD k [])) (vec (e.getD ((k + 1) % 3) [])) == -1) = true ∧
    (List.range 3).all (fun i => (e.map fun u => vec u i).foldl (· + ·) 0 == 0) = true := by
  decide

/-- Z³ 의 정육각형 — 평면 x + y + z = 0 위 (1, −1, 0) 의 순열 : 변 길이² 2 · 이웃 내적 1 (= S/2 · 60°) · 합 0 · 변이 모두 그 평면 위 -/
theorem hexagon_in_Z3 :
    let P : List (List Int) := [[1, -1, 0], [1, 0, -1], [0, 1, -1], [-1, 1, 0], [-1, 0, 1], [0, -1, 1]]
    let e : List (List Int) := (List.range 6).map fun k =>
      (List.range 3).map fun i => vec (P.getD ((k + 1) % 6) []) i - vec (P.getD k []) i
    P.all (fun p => p.foldl (· + ·) 0 == 0) = true ∧
    (List.range 6).all (fun k => dot 3 (vec (e.getD k [])) (vec (e.getD k [])) == 2 &&
      dot 3 (vec (e.getD k [])) (vec (e.getD ((k + 1) % 6) [])) == 1) = true := by
  decide

/-! ## 7. 색의 육각형 — RGB 정육면체를 흰–검 대각선으로 보면 -/

/-- 회색 대각선 (1, 1, 1) 에 수직인 평면으로 내린 그림자 × 3 : 3v − (v₀ + v₁ + v₂)(1, 1, 1) -/
def shadow (v : List Int) : List Int :=
  (List.range 3).map fun i => 3 * vec v i - (vec v 0 + vec v 1 + vec v 2)

/-- ★ 색의 육각형 : 빨 (1,0,0) · 노 (1,1,0) · 초 (0,1,0) · 청록 (0,1,1) · 파 (0,0,1) · 자홍 (1,0,1) 의 그림자는
    Z³ 의 정육각형 (평면 x + y + z = 0 · 변 길이² 6 · 이웃 내적 3 = S/2 · 60°) ·
    흰 (1,1,1) 과 검 (0,0,0) 의 그림자는 둘 다 가운데 (0,0,0) ·
    뒤집기 x ↦ (1,1,1) − x 는 흰 ↔ 검 과 함께 초 ↔ 자홍 · 빨 ↔ 청록 · 파 ↔ 노 를 맞바꾸고 그림자에서는 u ↦ −u -/
theorem color_hexagon :
    let C : List (List Int) := [[1, 0, 0], [1, 1, 0], [0, 1, 0], [0, 1, 1], [0, 0, 1], [1, 0, 1]]
    let H := C.map shadow
    let e : List (List Int) := (List.range 6).map fun k =>
      (List.range 3).map fun i => vec (H.getD ((k + 1) % 6) []) i - vec (H.getD k []) i
    H = [[2, -1, -1], [1, 1, -2], [-1, 2, -1], [-2, 1, 1], [-1, -1, 2], [1, -2, 1]] ∧
    H.all (fun h => h.foldl (· + ·) 0 == 0) = true ∧
    (List.range 6).all (fun k => dot 3 (vec (e.getD k [])) (vec (e.getD k [])) == 6 &&
      dot 3 (vec (e.getD k [])) (vec (e.getD ((k + 1) % 6) [])) == 3) = true ∧
    shadow [1, 1, 1] = [0, 0, 0] ∧ shadow [0, 0, 0] = [0, 0, 0] ∧
    (List.range 6).all (fun k =>
      shadow ((C.getD k []).map fun x => 1 - x) == (H.getD k []).map (fun x => -x) &&
      (H.getD ((k + 3) % 6) []) == (H.getD k []).map (fun x => -x)) = true := by
  decide

/-! ## 8. 최소 주기 — 닫히는 변의 수는 3 · 4 · 6 의 배수 -/

/-- 닫힘의 두 식 : U(S², 2c, m + 1) = 0 이고 S²·U(S², 2c, m) = −S^(m+1) -/
theorem closes_full (S c : Int) (hc : c ^ 2 ≠ S ^ 2) (a b : Nat → Int)
    (ha : ∀ k, S * a (k + 2) = 2 * c * a (k + 1) - S * a k) (hb : ∀ k, S * b (k + 2) = 2 * c * b (k + 1) - S * b k)
    (a0 : a 0 = S) (a1 : a 1 = c) (b0 : b 0 = c) (b1 : b 1 = S) (m : Nat) (am : a (m + 1) = S) (bm : b (m + 1) = c) :
    V (S ^ 2) (2 * c) (m + 1) = 0 ∧ S * S * V (S ^ 2) (2 * c) m = -(S ^ m * S) := by
  have h0 := closes S c hc a b ha hb a0 a1 b0 b1 m am bm
  refine ⟨h0, ?_⟩
  have A := (solve S c a ha m).1
  rw [am, a0, a1, h0] at A
  grind

/-- 동차 : U(S², S t, k + 1) = S^k · U(1, t, k + 1) -/
theorem hom1 (S t : Int) (k : Nat) : V (S ^ 2) (S * t) (k + 1) = S ^ k * V 1 t (k + 1) := by
  have := (V_homog S 1 t k).1
  rwa [Int.mul_one] at this

/-- U(1, t) 의 주기 : U(1, t, p) = 0 · U(1, t, p + 1) = 1 이면 U(1, t, n) = U(1, t, n mod p) -/
theorem V1_mod (t : Int) (p : Nat) (h0 : V 1 t p = 0) (h1 : V 1 t (p + 1) = 1) (n : Nat) :
    V 1 t n = V 1 t (n % p) := by
  have key : ∀ k, V 1 t (k + p) = V 1 t k ∧ V 1 t (k + 1 + p) = V 1 t (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simpa [V_zero] using h0, ?_⟩
      rw [show 0 + 1 + p = p + 1 by omega, h1]; rfl
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 + p = (k + p) + 2 by omega, show k + 1 + 1 = k + 2 by omega, V_two, V_two]
      rw [show k + p + 1 = k + 1 + p by omega, ih.1, ih.2]
  have per : ∀ q r, V 1 t (p * q + r) = V 1 t r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [show p * (q + 1) + r = (p * q + r) + p by rw [Nat.mul_succ]; omega, (key _).1, ih]
  have := per (n / p) (n % p)
  rwa [Nat.div_add_mod] at this

/-- ★ 정확한 주기 : 한 평면 위 정다각형이 m + 1 변에서 닫히면 — 바깥각 120° 면 3 ∣ m + 1 · 90° 면 4 ∣ m + 1 · 60° 면 6 ∣ m + 1.
    closes_in 과 함께 : 가장 짧은 닫힘은 정확히 3 · 4 · 6 변 — 정삼각형 · 정사각형 · 정육각형 -/
theorem exact_period (d : Nat) (v : Nat → Nat → Int) (S c : Int) (hS : 0 < S) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (rot : ∀ k i, i < d → S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i)
    (m : Nat) (close : ∀ i, i < d → v (m + 1) i = v 0 i) :
    (2 * c = -S → 3 ∣ m + 1) ∧ (c = 0 → 4 ∣ m + 1) ∧ (2 * c = S → 6 ∣ m + 1) := by
  have hrec (z : Nat → Int) : ∀ k, S * dot d (v (k + 2)) z = 2 * c * dot d (v (k + 1)) z - S * dot d (v k) z := by
    intro k
    rw [← dot_smul (v (k + 2)) z S d, ← dot_lin (v (k + 1)) (v k) z (2 * c) S d]
    exact dot_congr _ _ z d (fun i hi => rot k i hi)
  have hv (z : Nat → Int) : dot d (v (m + 1)) z = dot d (v 0) z := dot_congr _ _ z d close
  obtain ⟨hV, hW⟩ := closes_full S c (by omega) (fun k => dot d (v k) (v 0)) (fun k => dot d (v k) (v 1))
    (hrec (v 0)) (hrec (v 1)) (len 0) (by show dot d (v 1) (v 0) = c; rw [dot_comm]; exact adj 0) (adj 0) (len 1) m
    (by show dot d (v (m + 1)) (v 0) = S; rw [hv]; exact len 0)
    (by show dot d (v (m + 1)) (v 1) = c; rw [hv]; exact adj 0)
  have hS0 : S ≠ 0 := by omega
  have pw : ∀ k : Nat, S ^ k ≠ 0 := fun k => Int.pow_ne_zero hS0
  -- U(1, t, m + 1) = 0
  have zero_of (t : Int) (e : 2 * c = S * t) : V 1 t (m + 1) = 0 := by
    rw [e, hom1] at hV
    rcases Int.mul_eq_zero.mp hV with h | h
    · exact absurd h (pw m)
    · exact h
  -- m = j + 1 이면 U(1, t, j + 1) = −1
  have minus_of (t : Int) (e : 2 * c = S * t) (j : Nat) (hm : m = j + 1) : V 1 t (j + 1) = -1 := by
    subst hm
    rw [e, hom1] at hW
    have e2 : S * S * (S ^ j * V 1 t (j + 1)) = (S ^ (j + 1) * S) * V 1 t (j + 1) := by rw [Int.pow_succ]; grind
    rw [e2] at hW
    have hne : S ^ (j + 1) * S ≠ 0 := Int.mul_ne_zero (pw _) hS0
    have : (S ^ (j + 1) * S) * (V 1 t (j + 1) + 1) = 0 := by grind
    rcases Int.mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have z := zero_of (-1) (by rw [h]; grind)
    rw [V1_mod (-1) 3 (by decide) (by decide)] at z
    have : (m + 1) % 3 = 0 ∨ (m + 1) % 3 = 1 ∨ (m + 1) % 3 = 2 := by omega
    rcases this with r | r | r <;> rw [r] at z
    · exact Nat.dvd_of_mod_eq_zero r
    · exact absurd z (by decide)
    · exact absurd z (by decide)
  · have z := zero_of 0 (by rw [h]; grind)
    rcases m with _ | j
    · exact absurd z (by decide)
    · have w := minus_of 0 (by rw [h]; grind) j rfl
      rw [V1_mod 0 4 (by decide) (by decide)] at z w
      have : (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 ∨ (j + 1) % 4 = 2 ∨ (j + 1) % 4 = 3 := by omega
      rcases this with r | r | r | r <;> rw [r] at w
      · exact absurd w (by decide)
      · exact absurd w (by decide)
      · exact absurd w (by decide)
      · exact Nat.dvd_of_mod_eq_zero (by omega)
  · have z := zero_of 1 (by rw [h]; grind)
    rcases m with _ | j
    · exact absurd z (by decide)
    · have w := minus_of 1 (by rw [h]; grind) j rfl
      rw [V1_mod 1 6 (by decide) (by decide)] at z w
      have hz : (j + 1 + 1) % 6 = 0 ∨ (j + 1 + 1) % 6 = 3 := by
        have : (j + 1 + 1) % 6 < 6 := Nat.mod_lt _ (by omega)
        have : (j + 1 + 1) % 6 = 0 ∨ (j + 1 + 1) % 6 = 1 ∨ (j + 1 + 1) % 6 = 2 ∨ (j + 1 + 1) % 6 = 3 ∨
            (j + 1 + 1) % 6 = 4 ∨ (j + 1 + 1) % 6 = 5 := by omega
        rcases this with r | r | r | r | r | r <;> rw [r] at z <;> first | omega | exact absurd z (by decide)
      have hw : (j + 1) % 6 = 4 ∨ (j + 1) % 6 = 5 := by
        have : (j + 1) % 6 = 0 ∨ (j + 1) % 6 = 1 ∨ (j + 1) % 6 = 2 ∨ (j + 1) % 6 = 3 ∨
            (j + 1) % 6 = 4 ∨ (j + 1) % 6 = 5 := by omega
        rcases this with r | r | r | r | r | r <;> rw [r] at w <;> first | omega | exact absurd w (by decide)
      exact Nat.dvd_of_mod_eq_zero (by omega)

/-! ## 9. 정의에서 점화식으로 — 남은 가정을 없앤다

정다각형의 정의 : 모든 변의 길이² S · 이웃 변의 내적 c (같은 각) · 한 칸 건너 변의 내적 e (같은 각) ·
이웃한 세 변이 한 평면 (그람 행렬식 = 0) · 꼭짓점이 닫힘 (변의 합 = 0).
이것만으로 돌림 점화식 S v_{k+2} = 2c v_{k+1} − S v_k 이 나온다. 같은 평면의 길은 «같은 쪽으로 돌기» 와
«좌우로 번갈아 꺾기 (v_{k+2} = v_k)» 둘뿐이고, 번갈아 꺾는 길은 닫히지 않는다. -/

theorem dot_nonneg (w : Nat → Int) : ∀ d, 0 ≤ dot d w w := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih =>
    simp only [dot]
    have h := Int.sq_nonneg (w d)
    have e : w d ^ 2 = w d * w d := by grind
    omega

/-- 길이² 이 0 이면 벡터가 0 -/
theorem dot_self_zero (w : Nat → Int) : ∀ d, dot d w w = 0 → ∀ i, i < d → w i = 0 := by
  intro d
  induction d with
  | zero => intro _ i hi; omega
  | succ d ih =>
    intro h i hi
    simp only [dot] at h
    have h1 := dot_nonneg w d
    have h2 : 0 ≤ w d * w d := by have := Int.sq_nonneg (w d); grind
    have hd : dot d w w = 0 := by omega
    have hw : w d * w d = 0 := by omega
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
    · exact ih hd i hi'
    · subst hi'
      rcases Int.mul_eq_zero.mp hw with h' | h' <;> exact h'

/-- 세 벡터 결합의 길이² -/
theorem dot_three (x y z : Nat → Int) (A B C : Int) : ∀ d,
    dot d (fun i => A * z i - B * y i - C * x i) (fun i => A * z i - B * y i - C * x i) =
      A * A * dot d z z + B * B * dot d y y + C * C * dot d x x - 2 * A * B * dot d z y
        - 2 * A * C * dot d z x + 2 * B * C * dot d y x := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih => simp only [dot]; rw [ih]; grind

theorem dot_add (x y z : Nat → Int) : ∀ d, dot d (fun i => x i + y i) z = dot d x z + dot d y z := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih => simp only [dot, ih]; grind

theorem dot_zero_left (z : Nat → Int) : ∀ d, dot d (fun _ => 0) z = 0 := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih => simp only [dot, ih]; grind

/-- 변의 합 v₀ + … + v_{n−1} -/
def vsum (v : Nat → Nat → Int) : Nat → Nat → Int
  | 0 => fun _ => 0
  | n + 1 => fun i => vsum v n i + v n i

/-- ★ 같은 쪽으로 돌기 : 같은 변 · 같은 이웃 각 · 같은 한 칸 건너 각 · S e = 2c² − S² 이면 돌림 점화식 -/
theorem rot_of_dots (d : Nat) (v : Nat → Nat → Int) (S c e : Int) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (snd : ∀ k, dot d (v k) (v (k + 2)) = e) (hrot : S * e = 2 * c ^ 2 - S ^ 2) :
    ∀ k i, i < d → S * v (k + 2) i = 2 * c * v (k + 1) i - S * v k i := by
  intro k
  have hA : S ^ 2 - c ^ 2 ≠ 0 := by omega
  have ex := dot_three (v k) (v (k + 1)) (v (k + 2)) (S ^ 2 - c ^ 2) (c * S - e * c) (e * S - c ^ 2) d
  have a1 : dot d (v (k + 2)) (v (k + 1)) = c := by rw [dot_comm]; exact adj (k + 1)
  have a0 : dot d (v (k + 1)) (v k) = c := by rw [dot_comm]; exact adj k
  have s0 : dot d (v (k + 2)) (v k) = e := by rw [dot_comm]; exact snd k
  rw [a1, a0, s0, len, len, len] at ex
  have id1 : (S ^ 2 - c ^ 2) * (S ^ 2 - c ^ 2) * S + (c * S - e * c) * (c * S - e * c) * S +
      (e * S - c ^ 2) * (e * S - c ^ 2) * S - 2 * (S ^ 2 - c ^ 2) * (c * S - e * c) * c -
      2 * (S ^ 2 - c ^ 2) * (e * S - c ^ 2) * e + 2 * (c * S - e * c) * (e * S - c ^ 2) * c =
      (S ^ 2 - c ^ 2) * (-(e - S) * (S * e - 2 * c ^ 2 + S ^ 2)) := by grind
  have w0 := ex.trans id1
  rw [show S * e - 2 * c ^ 2 + S ^ 2 = 0 by omega] at w0
  have hz := dot_self_zero _ d (by rw [w0]; simp)
  intro i hi
  have h := hz i hi
  have : (S ^ 2 - c ^ 2) * (S * v (k + 2) i - (2 * c * v (k + 1) i - S * v k i)) = 0 := by grind
  rcases Int.mul_eq_zero.mp this with h' | h'
  · exact absurd h' hA
  · omega

/-- ★ 남은 가정 없이 : 정다각형의 정의 (같은 변 · 같은 이웃 각 · 같은 한 칸 건너 각 · 이웃 세 변이 한 평면 · 닫힘)
    에서 바깥각 120° · 90° · 60° 뿐 · 닫히는 변의 수는 3 · 4 · 6 의 배수 — 어느 차원의 정수 격자든 -/
theorem planar_regular (d : Nat) (v : Nat → Nat → Int) (S c e : Int) (hS : 0 < S) (hc : c ^ 2 < S ^ 2)
    (len : ∀ k, dot d (v k) (v k) = S) (adj : ∀ k, dot d (v k) (v (k + 1)) = c)
    (snd : ∀ k, dot d (v k) (v (k + 2)) = e)
    (plane : S * (S * S - c * c) - c * (c * S - e * c) + e * (c * c - e * S) = 0)
    (m : Nat) (close : ∀ i, i < d → v (m + 1) i = v 0 i)
    (sum0 : ∀ i, i < d → vsum v (m + 1) i = 0) :
    (2 * c = -S ∨ c = 0 ∨ 2 * c = S) ∧
    (2 * c = -S → 3 ∣ m + 1) ∧ (c = 0 → 4 ∣ m + 1) ∧ (2 * c = S → 6 ∣ m + 1) := by
  have fac : (e - S) * (S * e - 2 * c ^ 2 + S ^ 2) = 0 := by grind
  rcases Int.mul_eq_zero.mp fac with hz | hr
  · -- 좌우로 번갈아 꺾기 : v_{k+2} = v_k · 닫히지 않는다
    exfalso
    have he : e = S := by omega
    have zig : ∀ j i, i < d → v (j + 2) i = v j i := by
      intro j
      have ex := dot_three (v j) (v (j + 1)) (v (j + 2)) 1 0 1 d
      have s0 : dot d (v (j + 2)) (v j) = e := by rw [dot_comm]; exact snd j
      rw [s0, len, len, len] at ex
      have w0 : dot d (fun i => 1 * v (j + 2) i - 0 * v (j + 1) i - 1 * v j i)
          (fun i => 1 * v (j + 2) i - 0 * v (j + 1) i - 1 * v j i) = 0 := by rw [ex, he]; grind
      intro i hi
      have h := dot_self_zero _ d w0 i hi
      omega
    have par : ∀ j i, i < d → v (2 * j) i = v 0 i ∧ v (2 * j + 1) i = v 1 i := by
      intro j
      induction j with
      | zero => intro i _; exact ⟨rfl, rfl⟩
      | succ j ih =>
        intro i hi
        have a := zig (2 * j) i hi
        have b := zig (2 * j + 1) i hi
        constructor
        · rw [show 2 * (j + 1) = 2 * j + 2 by omega, a]; exact (ih i hi).1
        · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega, b]; exact (ih i hi).2
    have each : ∀ n, dot d (v n) (v 0) + dot d (v n) (v 1) = S + c := by
      intro n
      have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have e1 : ∀ z, dot d (v n) z = dot d (v 0) z := fun z =>
          dot_congr _ _ z d (fun i hi => by rw [hn, h, Nat.add_zero]; exact (par (n / 2) i hi).1)
        rw [e1, e1, len, adj 0]
      · have e1 : ∀ z, dot d (v n) z = dot d (v 1) z := fun z =>
          dot_congr _ _ z d (fun i hi => by rw [hn, h]; exact (par (n / 2) i hi).2)
        rw [e1, e1, len, dot_comm, adj 0]; omega
    have tot : ∀ n, dot d (vsum v n) (v 0) + dot d (vsum v n) (v 1) = n * (S + c) := by
      intro n
      induction n with
      | zero => simp only [vsum, dot_zero_left]; simp
      | succ n ih =>
        show dot d (fun i => vsum v n i + v n i) (v 0) + dot d (fun i => vsum v n i + v n i) (v 1) = _
        rw [dot_add, dot_add]
        have := each n
        push_cast
        grind
    have z0 : ∀ z, dot d (vsum v (m + 1)) z = 0 := fun z => by
      rw [dot_congr _ (fun _ => 0) z d sum0, dot_zero_left]
    have := tot (m + 1)
    rw [z0, z0] at this
    have h2 : ((m + 1 : Nat) : Int) * (S + c) = 0 := by omega
    rcases Int.mul_eq_zero.mp h2 with h | h
    · omega
    · have : c = -S := by omega
      subst this
      have : (-S) ^ 2 = S ^ 2 := by grind
      omega
  · -- 같은 쪽으로 돌기
    have rot := rot_of_dots d v S c e hc len adj snd (by omega)
    exact ⟨lattice_regular d v S c hS hc len adj rot m close, exact_period d v S c hS hc len adj rot m close⟩

/-! ## 10. 꼬인 정다각형 — 한 평면을 벗어나면 모든 n 이 있다 -/

/-- Zⁿ 의 변 e_k − e_{k+1} (번호는 n 으로 돈다) -/
def skewv (n k : Nat) : Nat → Int := fun i => (if i = k % n then 1 else 0) - (if i = (k + 1) % n then 1 else 0)

/-- ★ 꼬인 정다각형 (n = 4 … 12) : 변 e_k − e_{k+1} 은 길이² 2 · 이웃 내적 −1 · 그 밖 0 — 내적이 번호의 차만으로 정해지고
    (번호 돌림이 Zⁿ 의 등거리 변환이라 모든 변과 각이 같다) 합은 0 (닫힘) -/
theorem skew_polygons :
    (List.range' 4 9).all (fun n =>
      (List.range n).all (fun j => (List.range n).all (fun k =>
        dot n (skewv n j) (skewv n k) ==
          (if j == k then 2 else if (j + 1) % n == k || (k + 1) % n == j then -1 else 0))) &&
      (List.range n).all (fun i => (List.range n).foldl (fun s k => s + skewv n k i) 0 == 0)) = true := by
  decide +kernel

/-- ★ 그리고 꼬여 있다 : S = 2 · c = −1 · e = 0 이면 이웃 세 변의 그람 행렬식이 4 ≠ 0 — 한 평면이 아니다.
    그래서 정오각형은 Z⁵ 에 꼬인 꼴로는 있고 (n = 5), 평면 꼴로는 어느 차원에도 없다 (planar_regular) -/
theorem skew_not_planar :
    (2 : Int) * (2 * 2 - (-1) * (-1)) - (-1) * ((-1) * 2 - 0 * (-1)) + 0 * ((-1) * (-1) - 0 * 2) = 4 := by
  decide

/-! ## 11. 꼬인 정다각형 — 모든 n (n 을 문자로) -/

/-- 한 좌표 벡터와의 내적은 그 좌표 -/
theorem dot_ind (a : Nat) (z : Nat → Int) : ∀ d,
    dot d (fun i => if i = a then (1 : Int) else 0) z = if a < d then z a else 0 := by
  intro d
  induction d with
  | zero => simp [dot]
  | succ d ih =>
    simp only [dot, ih]
    by_cases h1 : a < d
    · have h2 : a < d + 1 := by omega
      have h3 : d ≠ a := by omega
      simp [h1, h2, h3]
    · by_cases h4 : d = a
      · subst h4; simp
      · have h5 : ¬ a < d + 1 := by omega
        simp [h1, h4, h5]

/-- (x + 1) mod n -/
theorem succ_mod (n x : Nat) (hx : x < n) : (x + 1) % n = if x + 1 < n then x + 1 else 0 := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · have : x + 1 = n := by omega
    rw [this, Nat.mod_self]

/-- ★ 모든 n : Zⁿ 의 변 e_j − e_{j+1} 사이의 내적은 2 (같은 변) · −1 (이웃) · 0 (그 밖) — 번호의 차만으로 정해진다 -/
theorem skew_dot (n j k : Nat) (hj : j < n) (hk : k < n) :
    dot n (skewv n j) (skewv n k) =
      (if j = k then 2 else 0) - (if (j + 1) % n = k then 1 else 0) - (if (k + 1) % n = j then 1 else 0) := by
  have hn : 0 < n := by omega
  have hsplit : skewv n j = fun i => 1 * (fun i => if i = j % n then (1 : Int) else 0) i -
      1 * (fun i => if i = (j + 1) % n then (1 : Int) else 0) i := by
    funext i; simp [skewv]
  rw [hsplit, dot_lin, dot_ind, dot_ind]
  have m1 := Nat.mod_lt j hn
  have m2 := Nat.mod_lt (j + 1) hn
  simp only [m1, m2, ite_true]
  simp only [skewv, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk, succ_mod n j hj, succ_mod n k hk]
  by_cases a : j + 1 < n <;> by_cases b : k + 1 < n <;> by_cases c : j = k <;>
    simp [a, b, c] <;> split <;> split <;> omega

/-- ★ 모든 n : 변 e_k − e_{k+1} (k = 0 … n − 1) 의 합은 0 — 닫힌다 -/
theorem skew_closed (n i : Nat) : vsum (skewv n) n i = 0 := by
  have tel : ∀ m, vsum (skewv n) m i = (if i = 0 % n then 1 else 0) - (if i = m % n then 1 else 0) := by
    intro m
    induction m with
    | zero => simp [vsum]
    | succ m ih => show vsum (skewv n) m i + skewv n m i = _; rw [ih]; simp only [skewv]; grind
  rw [tel, Nat.mod_self]; simp only [Nat.zero_mod]; exact Int.sub_self _

end Trombo.Polygon

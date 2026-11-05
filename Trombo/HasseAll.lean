/-
y² = x³ − x — 모든 홀수 소수 p 에서 하세 한계 (린 4 코어만 · Mathlib 없음)

곡선 하나를 모든 소수에서 — «너비의 무한» 쪽 첫 칸.
  · 르장드르 기호 χ(a) = (a 의 제곱근 개수) − 1 의 곱셈성 (세기 논법 · 페르마 소정리 없이)
  · 야콥스탈 합 S(k) = Σ_x χ(x³ − kx) 의 항등식  Σ_k S(k)² = p (p − 1) (1 + χ(−1))
  · S(u² k) = χ(u) S(k) — 그래서 S(1)² + S(g)² = 2p (1 + χ(−1))  (g 는 비잉여)
  · a_p = p + 1 − #E(F_p) = −S(1) 이므로  a_p² < 4p
  · χ(−1) = 1 ⇔ p ≡ 1 (mod 4) (역원 짝짓기의 홀짝) → p ≡ 3 (mod 4) 이면 a_p = 0 ,
    p ≡ 1 (mod 4) 이면 p = A² + B² · a_p = 2A (허수 곱셈 공식의 꼴 · 페르마 두 제곱 정리가 덤으로)
-/
namespace Trombo.HasseAll

/-! ## 1. 합 -/

/-- Σ_{i < n} f i -/
def sm : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sm n f + f n

@[simp] theorem sm_zero (f : Nat → Int) : sm 0 f = 0 := rfl
theorem sm_succ (n : Nat) (f : Nat → Int) : sm (n + 1) f = sm n f + f n := rfl

theorem sm_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) : sm n f = sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sm_succ, sm_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sm_add (n : Nat) (f g : Nat → Int) : sm n (fun i => f i + g i) = sm n f + sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sm_succ, sm_succ, sm_succ, ih]; omega

theorem sm_sub (n : Nat) (f g : Nat → Int) : sm n (fun i => f i - g i) = sm n f - sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sm_succ, sm_succ, sm_succ, ih]; omega

theorem sm_mul_left (n : Nat) (k : Int) (f : Nat → Int) : sm n (fun i => k * f i) = k * sm n f := by
  induction n with
  | zero => simp
  | succ n ih => rw [sm_succ, sm_succ, ih, Int.mul_add]

theorem sm_mul_right (n : Nat) (k : Int) (f : Nat → Int) : sm n (fun i => f i * k) = sm n f * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [sm_succ, sm_succ, ih, Int.add_mul]

theorem sm_const (n : Nat) (k : Int) : sm n (fun _ => k) = (n : Int) * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [sm_succ, ih]; push_cast; grind

theorem sm_comm (n m : Nat) (F : Nat → Nat → Int) :
    sm n (fun i => sm m (fun j => F i j)) = sm m (fun j => sm n (fun i => F i j)) := by
  induction n with
  | zero =>
    rw [sm_zero]
    have := sm_const m 0
    simp at this
    rw [sm_congr m _ (fun _ => (0 : Int)) (fun j _ => by simp)]
    simp [this]
  | succ n ih =>
    rw [sm_succ, ih, ← sm_add]
    rfl

theorem sm_mul_sm (n m : Nat) (f g : Nat → Int) :
    sm n f * sm m g = sm n (fun i => sm m (fun j => f i * g j)) := by
  rw [← sm_mul_right]
  apply sm_congr
  intro i _
  rw [sm_mul_left]

theorem sm_le (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i ≤ g i) : sm n f ≤ sm n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sm_succ, sm_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

theorem sm_nonneg (n : Nat) (f : Nat → Int) (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ sm n f := by
  have := sm_le n (fun _ => 0) f h
  rw [sm_const] at this
  simpa using this

/-- 칸마다 ≤ 이고 합이 같으면 칸마다 = -/
theorem sm_eq_of_le (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i ≤ g i) (he : sm n f = sm n g) :
    ∀ i, i < n → f i = g i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [sm_succ, sm_succ] at he
    have h1 := sm_le n f g (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    have h3 : f n = g n := by omega
    have h4 : sm n f = sm n g := by omega
    by_cases hin : i = n
    · subst hin; exact h3
    · exact ih (fun j hj => h j (by omega)) h4 i (by omega)

/-- 지시 함수 -/
def ind (P : Prop) [Decidable P] : Int := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split <;> omega
theorem ind_le_one (P : Prop) [Decidable P] : ind P ≤ 1 := by unfold ind; split <;> omega
theorem ind_pos {P : Prop} [Decidable P] (h : P) : ind P = 1 := by simp [ind, h]
theorem ind_neg {P : Prop} [Decidable P] (h : ¬ P) : ind P = 0 := by simp [ind, h]

/-- 한 자리만 1 -/
theorem sm_single (n a : Nat) (ha : a < n) (f : Nat → Int) :
    sm n (fun i => if i = a then f i else 0) = f a := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sm_succ]
    by_cases h : a = n
    · subst h
      have : sm a (fun i => if i = a then f i else 0) = 0 := by
        have := sm_const a 0
        rw [sm_congr a _ (fun _ => (0 : Int)) (fun i hi => by simp; omega)]
        simpa using this
      rw [this]; simp
    · rw [ih (by omega)]; simp [Ne.symm h]

/-- 두 자리만 -/
theorem sm_double (n a b : Nat) (ha : a < n) (hb : b < n) (hab : a ≠ b) (f : Nat → Int) :
    sm n (fun i => if i = a ∨ i = b then f i else 0) = f a + f b := by
  rw [sm_congr n _ (fun i => (if i = a then f i else 0) + (if i = b then f i else 0)) (fun i _ => by
    by_cases h1 : i = a
    · subst h1; simp [hab]
    · by_cases h2 : i = b
      · subst h2; simp [h1]
      · simp [h1, h2])]
  rw [sm_add, sm_single n a ha, sm_single n b hb]

/-- 아무 자리도 참이 아니면 지시 함수의 합은 0 -/
theorem sm_ind_none (n : Nat) (P : Nat → Prop) [DecidablePred P] (h : ∀ i, i < n → ¬ P i) :
    sm n (fun i => ind (P i)) = 0 := by
  rw [sm_congr n _ (fun _ => 0) (fun i hi => ind_neg (h i hi)), sm_const]; simp

/-- 참인 자리가 많아야 하나이면 지시 함수의 합 ≤ 1 -/
theorem sm_ind_le_one (n : Nat) (P : Nat → Prop) [DecidablePred P]
    (h : ∀ i j, i < n → j < n → P i → P j → i = j) : sm n (fun i => ind (P i)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sm_succ]
    by_cases hn : P n
    · rw [ind_pos hn, sm_ind_none n P (fun i hi hPi => by have := h i n (by omega) (by omega) hPi hn; omega)]
      omega
    · rw [ind_neg hn]
      have := ih (fun i j hi hj => h i j (by omega) (by omega))
      omega

/-- 지시 함수의 합이 0 이 아니면 참인 자리가 있다 -/
theorem exists_of_sm_ind (n : Nat) (P : Nat → Prop) [DecidablePred P] (h : sm n (fun i => ind (P i)) ≠ 0) :
    ∃ i, i < n ∧ P i := by
  by_cases hex : ∃ i, i < n ∧ P i
  · exact hex
  · exact absurd (sm_ind_none n P (fun i hi hP => hex ⟨i, hi, hP⟩)) h

/-! ## 2. 소수 -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

theorem coprime_of_not_dvd {p m : Nat} (hp : IsPrime p) (h : ¬ p ∣ m) : Nat.Coprime p m := by
  rcases hp.2 (Nat.gcd p m) (Nat.gcd_dvd_left p m) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ Nat.gcd_dvd_right p m) h

theorem euclid_nat {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr ((coprime_of_not_dvd hp ha).dvd_of_dvd_mul_left h)

/-- 유클리드 : p ∣ ab 이면 p ∣ a 또는 p ∣ b -/
theorem euclid {p : Nat} (hp : IsPrime p) {a b : Int} (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases euclid_nat hp h with h | h
  · exact Or.inl (Int.ofNat_dvd_left.mpr h)
  · exact Or.inr (Int.ofNat_dvd_left.mpr h)

/-! ## 3. 합동 -/

/-- a ≡ b (mod p) -/
def cg (p : Nat) (a b : Int) : Prop := (p : Int) ∣ a - b

instance (p : Nat) (a b : Int) : Decidable (cg p a b) := inferInstanceAs (Decidable ((p : Int) ∣ a - b))

theorem cg_refl (p : Nat) (a : Int) : cg p a a := by simp [cg]
theorem cg_symm {p : Nat} {a b : Int} (h : cg p a b) : cg p b a := by
  unfold cg at *; have := Int.dvd_neg.mpr h; rwa [Int.neg_sub] at this
theorem cg_trans {p : Nat} {a b c : Int} (h1 : cg p a b) (h2 : cg p b c) : cg p a c := by
  unfold cg at *; have := Int.dvd_add h1 h2; rwa [show a - b + (b - c) = a - c by omega] at this
theorem cg_add {p : Nat} {a b c d : Int} (h1 : cg p a b) (h2 : cg p c d) : cg p (a + c) (b + d) := by
  unfold cg at *; have := Int.dvd_add h1 h2; rwa [show a - b + (c - d) = a + c - (b + d) by omega] at this
theorem cg_sub {p : Nat} {a b c d : Int} (h1 : cg p a b) (h2 : cg p c d) : cg p (a - c) (b - d) := by
  unfold cg at *; have := Int.dvd_sub h1 h2; rwa [show a - b - (c - d) = a - c - (b - d) by omega] at this
theorem cg_mul {p : Nat} {a b c d : Int} (h1 : cg p a b) (h2 : cg p c d) : cg p (a * c) (b * d) := by
  unfold cg at *
  have e : a * c - b * d = (a - b) * c + b * (c - d) := by grind
  rw [e]
  exact Int.dvd_add (Int.dvd_trans h1 (Int.dvd_mul_right _ _)) (Int.dvd_trans h2 (Int.dvd_mul_left _ _))
theorem cg_of_eq {p : Nat} {a b : Int} (h : a = b) : cg p a b := by subst h; exact cg_refl p a
theorem cg_zero_iff {p : Nat} {a : Int} : cg p a 0 ↔ (p : Int) ∣ a := by simp [cg]
theorem cg_self_mul (p : Nat) (k : Int) : cg p ((p : Int) * k) 0 := by
  simp [cg, Int.dvd_mul_right]

/-- 작은 차이는 0 -/
theorem dvd_small {p : Nat} (hp : 0 < p) {d : Int} (h : (p : Int) ∣ d) (h1 : -(p : Int) < d) (h2 : d < p) : d = 0 := by
  have hp' : (0 : Int) < p := by omega
  by_cases hd : 0 ≤ d
  · have := Int.emod_eq_of_lt hd h2
    rw [Int.emod_eq_zero_of_dvd h] at this
    omega
  · have h' : (p : Int) ∣ -d := Int.dvd_neg.mpr h
    have := Int.emod_eq_of_lt (by omega : 0 ≤ -d) (by omega : -d < p)
    rw [Int.emod_eq_zero_of_dvd h'] at this
    omega

/-- 대표 둘이 합동이면 같다 -/
theorem uniq {p : Nat} (hp : 0 < p) {x y : Nat} (hx : x < p) (hy : y < p) (h : cg p x y) : x = y := by
  have := dvd_small hp h (by omega) (by omega)
  omega

/-- 모든 정수에는 대표가 하나 있다 -/
theorem rep {p : Nat} (hp : 0 < p) (z : Int) : ∃ r : Nat, r < p ∧ cg p z r := by
  have hp' : (p : Int) ≠ 0 := by omega
  refine ⟨(z % (p : Int)).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos z (by omega : (0 : Int) < p)
    have := Int.emod_nonneg z hp'
    omega
  · have h0 := Int.emod_nonneg z hp'
    rw [Int.toNat_of_nonneg h0]
    unfold cg
    have e := Int.emod_add_ediv_mul z (p : Int)
    rw [Int.mul_comm] at e
    exact ⟨z / p, by omega⟩

/-- 대표의 지시 함수 합은 1 -/
theorem sm_rep {p : Nat} (hp : 0 < p) (z : Int) : sm p (fun y => ind (cg p z y)) = 1 := by
  obtain ⟨r, hr, hzr⟩ := rep hp z
  rw [sm_congr p _ (fun y => if y = r then 1 else 0) (fun y hy => by
    by_cases h : y = r
    · subst h; simp [ind, hzr]
    · have : ¬ cg p z y := fun hzy => h (uniq hp hy hr (cg_trans (cg_symm hzy) hzr))
      simp [ind, this, h])]
  exact sm_single p r hr (fun _ => 1)

/-- 합동을 지키는 함수 -/
def Resp (p : Nat) (g : Int → Int) : Prop := ∀ u v, cg p u v → g u = g v

theorem sm_rep_mul {p : Nat} (hp : 0 < p) (g : Int → Int) (hg : Resp p g) (z : Int) :
    sm p (fun y => ind (cg p z y) * g y) = g z := by
  have h1 : ∀ y, y < p → ind (cg p z y) * g y = ind (cg p z y) * g z := by
    intro y _
    by_cases h : cg p z y
    · rw [hg y z (cg_symm h)]
    · simp [ind, h]
  rw [sm_congr p _ _ h1, sm_mul_right, sm_rep hp z, Int.one_mul]

/-! ## 4. 다시 세기 — 단사이면 전사 · 합은 그대로 -/

/-- 대표들 위에서 단사인 사상은 모든 대표를 정확히 한 번 맞힌다 -/
theorem hit_once {p : Nat} (hp : 0 < p) (σ : Nat → Int)
    (hσ : ∀ x x', x < p → x' < p → cg p (σ x) (σ x') → x = x') :
    ∀ y, y < p → sm p (fun x => ind (cg p (σ x) y)) = 1 := by
  have hle : ∀ y, y < p → sm p (fun x => ind (cg p (σ x) y)) ≤ 1 := by
    intro y _
    exact sm_ind_le_one p (fun x => cg p (σ x) y)
      (fun i j hi hj h1 h2 => hσ i j hi hj (cg_trans h1 (cg_symm h2)))
  have htot : sm p (fun y => sm p (fun x => ind (cg p (σ x) y))) = sm p (fun _ => 1) := by
    rw [← sm_comm]
    apply sm_congr
    intro x _
    exact sm_rep hp (σ x)
  exact sm_eq_of_le p _ (fun _ => 1) hle htot

/-- 다시 세기 : Σ_x g(σ x) = Σ_y g(y) -/
theorem reindex {p : Nat} (hp : 0 < p) (σ : Nat → Int)
    (hσ : ∀ x x', x < p → x' < p → cg p (σ x) (σ x') → x = x')
    (g : Int → Int) (hg : Resp p g) :
    sm p (fun x => g (σ x)) = sm p (fun y => g y) := by
  have h1 : sm p (fun x => g (σ x)) = sm p (fun x => sm p (fun y => ind (cg p (σ x) y) * g y)) := by
    apply sm_congr; intro x _; rw [sm_rep_mul hp g hg (σ x)]
  rw [h1, sm_comm]
  apply sm_congr
  intro y hy
  rw [sm_mul_right, hit_once hp σ hσ y hy, Int.one_mul]

/-- 단사 사상은 어떤 대표든 맞힌다 -/
theorem surj {p : Nat} (hp : 0 < p) (σ : Nat → Int)
    (hσ : ∀ x x', x < p → x' < p → cg p (σ x) (σ x') → x = x') (y : Nat) (hy : y < p) :
    ∃ x, x < p ∧ cg p (σ x) y := by
  apply exists_of_sm_ind p (fun x => cg p (σ x) y)
  rw [hit_once hp σ hσ y hy]; omega


/-! ## 5. 제곱근의 개수와 르장드르 기호 -/

/-- a 의 제곱근 개수 (대표 0 … p − 1 가운데) -/
def nr (p : Nat) (a : Int) : Int := sm p (fun y => ind (cg p ((y : Int) * y) a))

/-- 르장드르 기호 χ(a) = 제곱근 개수 − 1 -/
def chi (p : Nat) (a : Int) : Int := nr p a - 1

/-- 제곱 -/
def IsSq (p : Nat) (a : Int) : Prop := ∃ y : Nat, y < p ∧ cg p ((y : Int) * y) a

theorem nr_congr (p : Nat) {a b : Int} (h : cg p a b) : nr p a = nr p b := by
  unfold nr
  apply sm_congr
  intro y _
  by_cases h1 : cg p ((y : Int) * y) a
  · rw [ind_pos h1, ind_pos (cg_trans h1 h)]
  · rw [ind_neg h1, ind_neg (fun h2 => h1 (cg_trans h2 (cg_symm h)))]

theorem chi_congr (p : Nat) {a b : Int} (h : cg p a b) : chi p a = chi p b := by
  unfold chi; rw [nr_congr p h]

theorem chi_resp (p : Nat) : Resp p (chi p) := fun _ _ h => chi_congr p h

section prime
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp in
theorem p_pos : 0 < p := by have := hp.1; omega

include hp in
theorem not_dvd_one : ¬ (p : Int) ∣ 1 := by
  intro h
  have := Int.le_of_dvd (by decide) h
  have := hp.1
  omega

include hp in
theorem dvd_mul_iff {a b : Int} : (p : Int) ∣ a * b ↔ (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  constructor
  · exact euclid hp
  · rintro (h | h)
    · exact Int.dvd_trans h (Int.dvd_mul_right _ _)
    · exact Int.dvd_trans h (Int.dvd_mul_left _ _)

include hp in
/-- 제곱이 합동이면 근은 ± -/
theorem sq_cg {y z : Int} (h : cg p (y * y) (z * z)) : cg p y z ∨ cg p y (-z) := by
  unfold cg at *
  have e : y * y - z * z = (y - z) * (y - (-z)) := by grind
  rw [e] at h
  exact euclid hp h

include hp in
/-- 정수 근이 있으면 대표 근도 있다 -/
theorem isSq_of_root {a s : Int} (h : cg p (s * s) a) : IsSq p a := by
  obtain ⟨r, hr, hsr⟩ := rep (p_pos hp) s
  exact ⟨r, hr, cg_trans (cg_mul (cg_symm hsr) (cg_symm hsr)) h⟩

include hp in
theorem nr_of_dvd {a : Int} (h : (p : Int) ∣ a) : nr p a = 1 := by
  unfold nr
  rw [sm_congr p _ (fun y => if y = 0 then 1 else 0) (fun y hy => by
    by_cases hy0 : y = 0
    · subst hy0
      have : cg p 0 a := by
        unfold cg; simpa using Int.dvd_neg.mpr h
      simp [ind, this]
    · have : ¬ cg p ((y : Int) * y) a := by
        intro h1
        have h2 : (p : Int) ∣ (y : Int) * y := by
          have := Int.dvd_add h1 h
          simpa using this
        have h3 : (p : Int) ∣ (y : Int) := by
          rcases euclid hp h2 with h4 | h4 <;> exact h4
        have := uniq (p_pos hp) hy (p_pos hp) (by unfold cg; simpa using h3)
        omega
      simp [ind, this, hy0])]
  exact sm_single p 0 (p_pos hp) (fun _ => 1)

include hp hodd in
theorem nr_of_root {a : Int} (ha : ¬ (p : Int) ∣ a) {y0 : Nat} (hy0 : y0 < p) (h0 : cg p ((y0 : Int) * y0) a) :
    nr p a = 2 := by
  have hy0' : 0 < y0 := by
    rcases Nat.eq_zero_or_pos y0 with h | h
    · subst h
      exact absurd (by unfold cg at h0; simpa using Int.dvd_neg.mpr h0) ha
    · exact h
  have hne : y0 ≠ p - y0 := by omega
  have hlt : p - y0 < p := by omega
  have hc : ((p - y0 : Nat) : Int) = (p : Int) - y0 := by omega
  unfold nr
  rw [sm_congr p _ (fun y => if y = y0 ∨ y = p - y0 then 1 else 0) (fun y hy => by
    by_cases hc1 : y = y0 ∨ y = p - y0
    · have : cg p ((y : Int) * y) a := by
        rcases hc1 with rfl | rfl
        · exact h0
        · rw [hc]
          apply cg_trans _ h0
          unfold cg
          exact ⟨(p : Int) - 2 * y0, by grind⟩
      simp [ind, this, hc1]
    · have : ¬ cg p ((y : Int) * y) a := by
        intro h1
        rcases sq_cg hp (cg_trans h1 (cg_symm h0)) with h2 | h2
        · exact hc1 (Or.inl (uniq (p_pos hp) hy hy0 h2))
        · refine hc1 (Or.inr (uniq (p_pos hp) hy hlt ?_))
          rw [hc]
          apply cg_trans h2
          unfold cg
          exact ⟨-1, by grind⟩
      simp [ind, this, hc1])]
  rw [sm_double p y0 (p - y0) hy0 hlt hne (fun _ => 1)]
  rfl

theorem nr_of_noroot {a : Int} (h : ¬ IsSq p a) : nr p a = 0 := by
  unfold nr
  exact sm_ind_none p _ (fun y hy h1 => h ⟨y, hy, h1⟩)

include hp in
theorem chi_of_dvd {a : Int} (h : (p : Int) ∣ a) : chi p a = 0 := by
  unfold chi; rw [nr_of_dvd hp h]; rfl

include hp hodd in
theorem chi_of_sq {a : Int} (ha : ¬ (p : Int) ∣ a) (h : IsSq p a) : chi p a = 1 := by
  obtain ⟨y0, hy0, h0⟩ := h
  unfold chi; rw [nr_of_root hp hodd ha hy0 h0]; rfl

theorem chi_of_nonsq {a : Int} (h : ¬ IsSq p a) : chi p a = -1 := by
  unfold chi; rw [nr_of_noroot h]; rfl

include hp hodd in
theorem chi_cases (a : Int) : chi p a = 0 ∨ chi p a = 1 ∨ chi p a = -1 := by
  by_cases h1 : (p : Int) ∣ a
  · exact Or.inl (chi_of_dvd hp h1)
  · by_cases h2 : IsSq p a
    · exact Or.inr (Or.inl (chi_of_sq hp hodd h1 h2))
    · exact Or.inr (Or.inr (chi_of_nonsq h2))

include hp hodd in
theorem chi_eq_zero_iff (a : Int) : chi p a = 0 ↔ (p : Int) ∣ a := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro h1
    by_cases h2 : IsSq p a
    · rw [chi_of_sq hp hodd h1 h2] at h; omega
    · rw [chi_of_nonsq h2] at h; omega
  · exact chi_of_dvd hp

include hp hodd in
theorem chi_unit {a : Int} (h : ¬ (p : Int) ∣ a) : chi p a = 1 ∨ chi p a = -1 := by
  rcases chi_cases hp hodd a with h1 | h1 | h1
  · exact absurd ((chi_eq_zero_iff hp hodd a).mp h1) h
  · exact Or.inl h1
  · exact Or.inr h1

theorem isSq_of_chi {a : Int} (h : chi p a = 1) : IsSq p a := by
  apply Classical.byContradiction
  intro h1
  rw [chi_of_nonsq h1] at h; omega

include hp hodd in
theorem not_dvd_of_chi {a : Int} (h : chi p a ≠ 0) : ¬ (p : Int) ∣ a := by
  intro h1; exact h ((chi_eq_zero_iff hp hodd a).mpr h1)

include hp hodd in
/-- χ(u²) = 1 -/
theorem chi_sq {u : Int} (h : ¬ (p : Int) ∣ u) : chi p (u * u) = 1 := by
  apply chi_of_sq hp hodd
  · intro h1; rcases euclid hp h1 with h2 | h2 <;> exact h h2
  · exact isSq_of_root hp (cg_refl p _)

/-- 모든 대표에 걸친 합 : Σ_a (제곱근 개수) = p -/
theorem sum_nr (hp0 : 0 < p) : sm p (fun a => nr p a) = p := by
  unfold nr
  rw [sm_comm]
  rw [sm_congr p _ (fun _ => 1) (fun y _ => sm_rep hp0 _)]
  rw [sm_const]; simp

/-- Σ_a χ(a) = 0 -/
theorem sum_chi (hp0 : 0 < p) : sm p (fun a => chi p a) = 0 := by
  unfold chi
  rw [sm_sub, sum_nr hp0, sm_const]; simp

/-! ## 6. 역원 -/

include hp in
/-- 곱하기 u 는 대표 위에서 단사 (p ∤ u) -/
theorem mul_inj {u : Int} (hu : ¬ (p : Int) ∣ u) :
    ∀ x x', x < p → x' < p → cg p (u * (x : Int)) (u * (x' : Int)) → x = x' := by
  intro x x' hx hx' h
  apply uniq (p_pos hp) hx hx'
  unfold cg at *
  rw [show u * (x : Int) - u * x' = u * (x - x') by grind] at h
  rcases euclid hp h with h1 | h1
  · exact absurd h1 hu
  · exact h1

include hp in
theorem exists_inv {u : Int} (hu : ¬ (p : Int) ∣ u) : ∃ v : Nat, v < p ∧ cg p (u * v) 1 :=
  surj (p_pos hp) (fun x => u * (x : Int)) (mul_inj hp hu) 1 (by have := hp.1; omega)

end prime

/-- 역원 (없으면 0) -/
noncomputable def inv (p : Nat) (u : Int) : Int :=
  if h : ∃ v : Nat, v < p ∧ cg p (u * v) 1 then ((Classical.choose h : Nat) : Int) else 0

theorem inv_spec {p : Nat} (hp : IsPrime p) {u : Int} (hu : ¬ (p : Int) ∣ u) : cg p (u * inv p u) 1 := by
  have h := exists_inv hp hu
  unfold inv
  split
  · next h' => exact (Classical.choose_spec h').2
  · next h' => exact absurd h h'

theorem inv_range (p : Nat) (u : Int) : ∃ v : Nat, (v < p ∨ v = 0) ∧ inv p u = v := by
  unfold inv
  split
  · next h => exact ⟨_, Or.inl (Classical.choose_spec h).1, rfl⟩
  · exact ⟨0, Or.inr rfl, rfl⟩

/-! ## 7. 곱셈성 χ(ab) = χ(a) χ(b) -/

section mult
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp hodd in
theorem chi_mul_sq_sq {a b : Int} (ha : chi p a = 1) (hb : chi p b = 1) : chi p (a * b) = 1 := by
  obtain ⟨s, _, hs⟩ := isSq_of_chi ha
  obtain ⟨t, _, ht⟩ := isSq_of_chi hb
  apply chi_of_sq hp hodd
  · intro h
    rcases euclid hp h with h1 | h1
    · exact not_dvd_of_chi hp hodd (by omega) h1
    · exact not_dvd_of_chi hp hodd (by omega) h1
  · apply isSq_of_root hp (s := (s : Int) * t)
    have := cg_mul hs ht
    exact cg_trans (cg_of_eq (by grind)) this

include hp hodd in
/-- 제곱 × 비잉여 = 비잉여 -/
theorem chi_mul_sq_nonsq {a b : Int} (ha : chi p a = 1) (hb : chi p b = -1) : chi p (a * b) = -1 := by
  have hpa := not_dvd_of_chi hp hodd (a := a) (by omega)
  have hpb := not_dvd_of_chi hp hodd (a := b) (by omega)
  have hab : ¬ (p : Int) ∣ a * b := by
    intro h; rcases euclid hp h with h1 | h1
    · exact hpa h1
    · exact hpb h1
  rcases chi_unit hp hodd hab with h | h
  · exfalso
    obtain ⟨s, _, hs⟩ := isSq_of_chi ha
    obtain ⟨w, _, hw⟩ := isSq_of_chi h
    have hps : ¬ (p : Int) ∣ (s : Int) := by
      intro h1
      apply hpa
      have h2 : (p : Int) ∣ (s : Int) * s := Int.dvd_trans h1 (Int.dvd_mul_right _ _)
      have := Int.dvd_sub h2 hs
      rwa [show (s : Int) * s - ((s : Int) * s - a) = a by omega] at this
    have hi := inv_spec hp hps
    -- b ≡ (inv s · w)²
    have hsq : IsSq p b := by
      apply isSq_of_root hp (s := inv p s * w)
      -- (s' w)² = s'² w² ≡ s'² (a b) ≡ s'² (s² b) = (s s')² b ≡ b
      have e1 : cg p ((inv p s * w) * (inv p s * w)) ((inv p s * inv p s) * (a * b)) :=
        cg_trans (cg_of_eq (by grind)) (cg_mul (cg_refl p _) hw)
      have e2 : cg p ((inv p s * inv p s) * (a * b)) ((inv p s * inv p s) * ((s * s) * b)) :=
        cg_mul (cg_refl p _) (cg_mul (cg_symm hs) (cg_refl p _))
      have e3 : cg p ((inv p s * inv p s) * ((s * s) * b)) (((s : Int) * inv p s) * ((s : Int) * inv p s) * b) :=
        cg_of_eq (by grind)
      have e4 : cg p (((s : Int) * inv p s) * ((s : Int) * inv p s) * b) (1 * 1 * b) :=
        cg_mul (cg_mul hi hi) (cg_refl p _)
      exact cg_trans e1 (cg_trans e2 (cg_trans e3 (cg_trans e4 (cg_of_eq (by grind)))))
    rw [chi_of_sq hp hodd hpb hsq] at hb
    omega
  · exact h

include hp hodd in
/-- χ(c) = (χ(c) = 1) − (χ(c) = −1) -/
theorem chi_split (c : Int) : chi p c = ind (chi p c = 1) - ind (chi p c = -1) := by
  rcases chi_cases hp hodd c with h | h | h <;> simp [ind, h]

include hp hodd in
/-- 잉여의 수 = 비잉여의 수 -/
theorem count_eq : sm p (fun c => ind (chi p c = 1)) = sm p (fun c => ind (chi p c = -1)) := by
  have h := sum_chi (p := p) (p_pos hp)
  rw [sm_congr p _ _ (fun c _ => chi_split hp hodd c), sm_sub] at h
  omega

include hp hodd in
/-- 비잉여 × 비잉여 = 잉여 (세기 논법) -/
theorem chi_mul_nonsq_nonsq {a b : Int} (ha : chi p a = -1) (hb : chi p b = -1) : chi p (a * b) = 1 := by
  have hpa := not_dvd_of_chi hp hodd (a := a) (by omega)
  have hpb := not_dvd_of_chi hp hodd (a := b) (by omega)
  -- T(c) = [χ c = 1] ≤ T'(c) = [χ(a c) = −1]
  have hle : ∀ c, c < p → ind (chi p (c : Int) = 1) ≤ ind (chi p (a * (c : Int)) = -1) := by
    intro c _
    by_cases hc : chi p (c : Int) = 1
    · rw [ind_pos hc, ind_pos (by rw [Int.mul_comm]; exact chi_mul_sq_nonsq hp hodd hc ha)]
      exact Int.le_refl 1
    · rw [ind_neg hc]; exact ind_nonneg _
  have hsum : sm p (fun c => ind (chi p (c : Int) = 1)) = sm p (fun c => ind (chi p (a * (c : Int)) = -1)) := by
    rw [reindex (p_pos hp) (fun c => a * (c : Int)) (mul_inj hp hpa) (fun z => ind (chi p z = -1))
      (fun u v h => by simp only [chi_congr p h])]
    exact count_eq hp hodd
  have heq := sm_eq_of_le p _ _ hle hsum
  -- c = a⁻¹ b 의 대표
  obtain ⟨r, hr, hcr⟩ := rep (p_pos hp) (inv p a * b)
  have hai := inv_spec hp hpa
  have har : cg p (a * (r : Int)) b := by
    have e1 : cg p (a * (r : Int)) (a * (inv p a * b)) := cg_mul (cg_refl p a) (cg_symm hcr)
    have e2 : cg p (a * (inv p a * b)) ((a * inv p a) * b) := cg_of_eq (by grind)
    have e3 : cg p ((a * inv p a) * b) (1 * b) := cg_mul hai (cg_refl p b)
    exact cg_trans e1 (cg_trans e2 (cg_trans e3 (cg_of_eq (by grind))))
  have h1 : ind (chi p (a * (r : Int)) = -1) = 1 := ind_pos (by rw [chi_congr p har]; exact hb)
  have h2 : chi p (r : Int) = 1 := by
    have := heq r hr
    rw [h1] at this
    apply Classical.byContradiction
    intro hc
    rw [ind_neg hc] at this
    omega
  obtain ⟨s, _, hs⟩ := isSq_of_chi h2
  apply chi_of_sq hp hodd
  · intro h; rcases euclid hp h with h3 | h3
    · exact hpa h3
    · exact hpb h3
  · apply isSq_of_root hp (s := a * s)
    -- (a s)² = a² s² ≡ a² r = a (a r) ≡ a b
    have e1 : cg p ((a * s) * (a * s)) (a * (a * ((s : Int) * s))) := cg_of_eq (by grind)
    have e2 : cg p (a * (a * ((s : Int) * s))) (a * (a * (r : Int))) := cg_mul (cg_refl p a) (cg_mul (cg_refl p a) hs)
    have e3 : cg p (a * (a * (r : Int))) (a * b) := cg_mul (cg_refl p a) har
    exact cg_trans e1 (cg_trans e2 e3)

include hp hodd in
/-- 르장드르 기호의 곱셈성 -/
theorem chi_mul (a b : Int) : chi p (a * b) = chi p a * chi p b := by
  by_cases ha : (p : Int) ∣ a
  · rw [chi_of_dvd hp ha, chi_of_dvd hp (Int.dvd_trans ha (Int.dvd_mul_right _ _))]; simp
  by_cases hb : (p : Int) ∣ b
  · rw [chi_of_dvd hp hb, chi_of_dvd hp (Int.dvd_trans hb (Int.dvd_mul_left _ _))]; simp
  rcases chi_unit hp hodd ha with h1 | h1 <;> rcases chi_unit hp hodd hb with h2 | h2
  · rw [chi_mul_sq_sq hp hodd h1 h2, h1, h2]; rfl
  · rw [chi_mul_sq_nonsq hp hodd h1 h2, h1, h2]; rfl
  · rw [Int.mul_comm, chi_mul_sq_nonsq hp hodd h2 h1, h1, h2]; rfl
  · rw [chi_mul_nonsq_nonsq hp hodd h1 h2, h1, h2]; rfl

end mult


/-! ## 8. 이차식의 합 Σ_k χ((k − s)(k − t)) -/

section conic
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp in
theorem inv_zero : inv p 0 = 0 := by
  unfold inv
  split
  · next h =>
    exfalso
    obtain ⟨v, _, hv⟩ := h
    apply not_dvd_one hp
    unfold cg at hv
    have := Int.dvd_neg.mpr hv
    simpa using this
  · rfl

include hp in
theorem inv_not_dvd {u : Int} (hu : ¬ (p : Int) ∣ u) : ¬ (p : Int) ∣ inv p u := by
  intro h
  have h1 : (p : Int) ∣ u * inv p u := Int.dvd_trans h (Int.dvd_mul_left _ _)
  have h2 := inv_spec hp hu
  unfold cg at h2
  apply not_dvd_one hp
  have := Int.dvd_sub h1 h2
  rwa [show u * inv p u - (u * inv p u - 1) = 1 by omega] at this

include hp in
/-- 역원은 대표 위에서 단사 -/
theorem inv_inj : ∀ x x', x < p → x' < p → cg p (inv p (x : Int)) (inv p (x' : Int)) → x = x' := by
  intro x x' hx hx' h
  by_cases h0 : x = 0
  · by_cases h0' : x' = 0
    · omega
    · exfalso
      subst h0
      have hx'0 : ¬ (p : Int) ∣ (x' : Int) := fun h1 => h0' (uniq (p_pos hp) hx' (p_pos hp) (by unfold cg; simpa using h1))
      rw [show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp] at h
      apply inv_not_dvd hp hx'0
      have := cg_symm h
      unfold cg at this; simpa using this
  · by_cases h0' : x' = 0
    · exfalso
      subst h0'
      have hx0 : ¬ (p : Int) ∣ (x : Int) := fun h1 => h0 (uniq (p_pos hp) hx (p_pos hp) (by unfold cg; simpa using h1))
      rw [show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp] at h
      apply inv_not_dvd hp hx0
      unfold cg at h; simpa using h
    · have hx0 : ¬ (p : Int) ∣ (x : Int) := fun h1 => h0 (uniq (p_pos hp) hx (p_pos hp) (by unfold cg; simpa using h1))
      have hx0' : ¬ (p : Int) ∣ (x' : Int) := fun h1 => h0' (uniq (p_pos hp) hx' (p_pos hp) (by unfold cg; simpa using h1))
      apply uniq (p_pos hp) hx hx'
      have i1 := inv_spec hp hx0
      have i2 := inv_spec hp hx0'
      -- x ≡ x (x' inv x') = x' (x inv x') ≡ x' (x inv x) ≡ x'
      have e1 : cg p (x : Int) ((x : Int) * ((x' : Int) * inv p x')) :=
        cg_trans (cg_of_eq (by grind)) (cg_mul (cg_refl p _) (cg_symm i2))
      have e2 : cg p ((x : Int) * ((x' : Int) * inv p x')) ((x' : Int) * ((x : Int) * inv p x)) :=
        cg_trans (cg_of_eq (by grind)) (cg_mul (cg_refl p _) (cg_mul (cg_refl p _) (cg_symm h)))
      have e3 : cg p ((x' : Int) * ((x : Int) * inv p x)) (x' : Int) :=
        cg_trans (cg_mul (cg_refl p _) i1) (cg_of_eq (by grind))
      exact cg_trans e1 (cg_trans e2 e3)

include hp hodd in
theorem conic_eq (s t : Int) (h : cg p s t) :
    sm p (fun k => chi p (((k : Int) - s) * ((k : Int) - t))) = (p : Int) - 1 := by
  have hpt : ∀ k, k < p → chi p (((k : Int) - s) * ((k : Int) - t)) = 1 - ind (cg p t k) := by
    intro k _
    by_cases hk : cg p t k
    · rw [ind_pos hk]
      apply chi_of_dvd hp
      have h1 : (p : Int) ∣ (k : Int) - t := cg_symm hk
      have := Int.dvd_trans h1 (Int.dvd_mul_left ((k : Int) - s) ((k : Int) - t))
      simpa using this
    · rw [ind_neg hk]
      have hkt : ¬ (p : Int) ∣ (k : Int) - t := fun h1 => hk (cg_symm h1)
      have e : cg p (((k : Int) - s) * ((k : Int) - t)) (((k : Int) - t) * ((k : Int) - t)) :=
        cg_mul (cg_sub (cg_refl p _) h) (cg_refl p _)
      rw [chi_congr p e, chi_sq hp hodd hkt]; rfl
  rw [sm_congr p _ _ hpt, sm_sub, sm_const, sm_rep (p_pos hp) t]
  simp

include hp hodd in
theorem conic_ne (s t : Int) (h : ¬ cg p s t) :
    sm p (fun k => chi p (((k : Int) - s) * ((k : Int) - t))) = -1 := by
  have hp0 := p_pos hp
  have hδ : ¬ (p : Int) ∣ t - s := fun h1 => h (cg_symm h1)
  -- (1) k = v + s
  have t1 : sm p (fun k => chi p (((k : Int) - s) * ((k : Int) - t))) =
      sm p (fun v => chi p ((((v : Int) + s) - s) * (((v : Int) + s) - t))) := by
    symm
    exact reindex hp0 (fun v => (v : Int) + s)
      (fun x x' hx hx' hc => uniq hp0 hx hx' (by have := cg_sub hc (cg_refl p s); simpa using this))
      (fun z => chi p ((z - s) * (z - t)))
      (fun u v huv => chi_congr p (cg_mul (cg_sub huv (cg_refl p _)) (cg_sub huv (cg_refl p _))))
  -- (2) 칸마다 : χ(v (v − δ)) = χ(1 − δ v⁻¹) − [v = 0]
  have t2 : ∀ v, v < p → chi p ((((v : Int) + s) - s) * (((v : Int) + s) - t)) =
      chi p (1 - (t - s) * inv p (v : Int)) - ind (v = 0) := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [ind_pos rfl, show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp]
      rw [chi_of_dvd hp (by simp), show (1 : Int) - (t - s) * 0 = 1 * 1 by omega,
        chi_sq hp hodd (not_dvd_one hp)]
      rfl
    · rw [ind_neg hv0]
      have hpv : ¬ (p : Int) ∣ (v : Int) := fun h1 => hv0 (uniq hp0 hv hp0 (by unfold cg; simpa using h1))
      have hi := inv_spec hp hpv
      -- v (v − δ) ≡ (v v) (1 − δ v⁻¹)
      have e : cg p ((((v : Int) + s) - s) * (((v : Int) + s) - t))
          (((v : Int) * v) * (1 - (t - s) * inv p (v : Int))) := by
        have e1 : cg p ((((v : Int) + s) - s) * (((v : Int) + s) - t))
            ((v : Int) * v - (t - s) * ((v : Int) * 1)) := cg_of_eq (by grind)
        have e2 : cg p ((v : Int) * v - (t - s) * ((v : Int) * 1))
            ((v : Int) * v - (t - s) * ((v : Int) * ((v : Int) * inv p (v : Int)))) :=
          cg_sub (cg_refl p _) (cg_mul (cg_refl p _) (cg_mul (cg_refl p _) (cg_symm hi)))
        exact cg_trans e1 (cg_trans e2 (cg_of_eq (by grind)))
      rw [chi_congr p e, chi_mul hp hodd, chi_sq hp hodd hpv]
      omega
  rw [t1, sm_congr p _ _ t2, sm_sub]
  -- (3) Σ_v χ(1 − δ v⁻¹) = Σ_w χ(1 − δ w) = Σ_z χ(z) = 0
  have t3 : sm p (fun v => chi p (1 - (t - s) * inv p (v : Int))) = sm p (fun w => chi p (1 - (t - s) * (w : Int))) :=
    reindex hp0 (fun v => inv p (v : Int)) (inv_inj hp) (fun z => chi p (1 - (t - s) * z))
      (fun u v huv => chi_congr p (cg_sub (cg_refl p _) (cg_mul (cg_refl p _) huv)))
  have t4 : sm p (fun w => chi p (1 - (t - s) * (w : Int))) = sm p (fun z => chi p (z : Int)) :=
    reindex hp0 (fun w => 1 - (t - s) * (w : Int))
      (fun x x' hx hx' hc => by
        apply uniq hp0 hx hx'
        unfold cg at hc ⊢
        rw [show 1 - (t - s) * (x : Int) - (1 - (t - s) * x') = (t - s) * (x' - x) by grind] at hc
        rcases euclid hp hc with h1 | h1
        · exact absurd h1 hδ
        · have := Int.dvd_neg.mpr h1; rwa [Int.neg_sub] at this)
      (chi p) (chi_resp p)
  rw [t3, t4, sum_chi hp0]
  have : sm p (fun v => ind (v = 0)) = 1 := by
    have := sm_single p 0 hp0 (fun _ => 1)
    simpa [ind] using this
  rw [this]; rfl

include hp hodd in
/-- 두 경우를 한 식으로 : Σ_k χ((k − s)(k − t)) = −1 + p · [s ≡ t] -/
theorem conic (s t : Int) :
    sm p (fun k => chi p (((k : Int) - s) * ((k : Int) - t))) = -1 + (p : Int) * ind (cg p s t) := by
  by_cases h : cg p s t
  · rw [conic_eq hp hodd s t h, ind_pos h]; omega
  · rw [conic_ne hp hodd s t h, ind_neg h]; omega

end conic

/-! ## 9. 야콥스탈 합 S(k) = Σ_x χ(x³ − kx) 와 큰 항등식 -/

/-- 야콥스탈 합 -/
def S (p : Nat) (k : Int) : Int := sm p (fun x => chi p ((x : Int) * x * x - k * x))

section jacobsthal
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp in
/-- x 가 0 이 아닌 대표이면 x² ≡ y² ⇔ y = x 또는 y = p − x -/
theorem sq_eq_iff {x y : Nat} (hx0 : 0 < x) (hx : x < p) (hy : y < p) :
    cg p ((x : Int) * x) ((y : Int) * y) ↔ (y = x ∨ y = p - x) := by
  have hp0 := p_pos hp
  have hc : ((p - x : Nat) : Int) = (p : Int) - x := by omega
  constructor
  · intro h
    rcases sq_cg hp (cg_symm h) with h1 | h1
    · exact Or.inl (uniq hp0 hy hx h1)
    · refine Or.inr (uniq hp0 hy (by omega) ?_)
      rw [hc]
      apply cg_trans h1
      unfold cg
      exact ⟨-1, by grind⟩
  · rintro (rfl | rfl)
    · exact cg_refl p _
    · rw [hc]
      unfold cg
      exact ⟨2 * (x : Int) - p, by grind⟩

include hp hodd in
/-- 안쪽 합 : Σ_y χ(xy) [x² ≡ y²] = [x ≠ 0] (1 + χ(−1)) -/
theorem inner_sum (x : Nat) (hx : x < p) :
    sm p (fun y => chi p ((x : Int) * y) * ind (cg p ((x : Int) * x) ((y : Int) * y))) =
      (1 - ind (x = 0)) * (1 + chi p (-1)) := by
  have hp0 := p_pos hp
  by_cases hx0 : x = 0
  · subst hx0
    rw [ind_pos rfl]
    have : ∀ y, y < p → chi p (((0 : Nat) : Int) * y) * ind (cg p (((0 : Nat) : Int) * ((0 : Nat) : Int)) ((y : Int) * y)) = 0 := by
      intro y _
      rw [chi_of_dvd hp (by simp)]; simp
    rw [sm_congr p _ _ this, sm_const]; simp
  · rw [ind_neg hx0]
    have hx0' : 0 < x := by omega
    have hpx : ¬ (p : Int) ∣ (x : Int) := fun h1 => hx0 (uniq hp0 hx hp0 (by unfold cg; simpa using h1))
    rw [sm_congr p _ (fun y => if y = x ∨ y = p - x then chi p ((x : Int) * y) else 0) (fun y hy => by
      by_cases hc : y = x ∨ y = p - x
      · rw [ind_pos ((sq_eq_iff hp hx0' hx hy).mpr hc)]; simp [hc]
      · rw [ind_neg (fun h1 => hc ((sq_eq_iff hp hx0' hx hy).mp h1))]; simp [hc])]
    rw [sm_double p x (p - x) hx (by omega) (by omega)]
    have hc : ((p - x : Nat) : Int) = (p : Int) - x := by omega
    rw [hc, chi_sq hp hodd hpx]
    have e : cg p ((x : Int) * ((p : Int) - x)) (-1 * ((x : Int) * x)) := by
      unfold cg; exact ⟨(x : Int), by grind⟩
    rw [chi_congr p e, chi_mul hp hodd, chi_sq hp hodd hpx]
    omega

include hp hodd in
/-- 큰 항등식 : Σ_k S(k)² = p (p − 1) (1 + χ(−1)) -/
theorem sum_S_sq : sm p (fun k => S p k * S p k) = (p : Int) * ((p : Int) - 1) * (1 + chi p (-1)) := by
  have hp0 := p_pos hp
  -- S(k)² = Σ_x Σ_y χ(xy) χ((k − x²)(k − y²))
  have h1 : ∀ k, k < p → S p (k : Int) * S p (k : Int) =
      sm p (fun x => sm p (fun y => chi p ((x : Int) * y) *
        chi p (((k : Int) - (x : Int) * x) * ((k : Int) - (y : Int) * y)))) := by
    intro k _
    unfold S
    rw [sm_mul_sm]
    apply sm_congr; intro x _
    apply sm_congr; intro y _
    rw [← chi_mul hp hodd, ← chi_mul hp hodd]
    congr 1
    grind
  rw [sm_congr p _ _ h1]
  -- 순서 바꾸기 : Σ_x Σ_y χ(xy) Σ_k χ(...)
  rw [sm_comm]
  have h2 : ∀ x, x < p → sm p (fun k => sm p (fun y => chi p ((x : Int) * y) *
        chi p (((k : Int) - (x : Int) * x) * ((k : Int) - (y : Int) * y)))) =
      sm p (fun y => chi p ((x : Int) * y) * (-1 + (p : Int) * ind (cg p ((x : Int) * x) ((y : Int) * y)))) := by
    intro x _
    rw [sm_comm]
    apply sm_congr; intro y _
    rw [sm_mul_left, conic hp hodd]
  rw [sm_congr p _ _ h2]
  have h3 : ∀ x, x < p → sm p (fun y => chi p ((x : Int) * y) * (-1 + (p : Int) * ind (cg p ((x : Int) * x) ((y : Int) * y)))) =
      -(chi p (x : Int) * sm p (fun y => chi p (y : Int))) +
        (p : Int) * ((1 - ind (x = 0)) * (1 + chi p (-1))) := by
    intro x hx
    rw [← inner_sum hp hodd x hx]
    have e : ∀ y, y < p → chi p ((x : Int) * y) * (-1 + (p : Int) * ind (cg p ((x : Int) * x) ((y : Int) * y))) =
        (-chi p (x : Int)) * chi p (y : Int) +
          (p : Int) * (chi p ((x : Int) * y) * ind (cg p ((x : Int) * x) ((y : Int) * y))) := by
      intro y _
      have hc := chi_mul hp hodd (x : Int) (y : Int)
      generalize chi p ((x : Int) * y) = c at hc ⊢
      generalize ind (cg p ((x : Int) * x) ((y : Int) * y)) = I
      rw [hc]; grind
    rw [sm_congr p _ _ e, sm_add, sm_mul_left, sm_mul_left]
    grind
  rw [sm_congr p _ _ h3]
  rw [sum_chi hp0]
  simp only [Int.mul_zero, Int.neg_zero, Int.zero_add]
  rw [sm_mul_left]
  have h4 : sm p (fun x => (1 - ind (x = 0)) * (1 + chi p (-1))) = ((p : Int) - 1) * (1 + chi p (-1)) := by
    rw [sm_mul_right, sm_sub, sm_const]
    have := sm_single p 0 hp0 (fun _ => 1)
    have h5 : sm p (fun x => ind (x = 0)) = 1 := by simpa [ind] using this
    rw [h5]; simp
  rw [h4]; grind

end jacobsthal


/-! ## 10. 잉여류 — S(u² k) = χ(u) S(k) 와 두 값 -/

section coset
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

theorem S_congr {k k' : Int} (h : cg p k k') : S p k = S p k' := by
  unfold S; apply sm_congr; intro x _
  apply chi_congr p
  exact cg_sub (cg_refl p _) (cg_mul h (cg_refl p _))

include hp hodd in
theorem chi_one : chi p 1 = 1 := by
  have := chi_sq hp hodd (u := 1) (not_dvd_one hp)
  simpa using this

include hp hodd in
theorem S_scale {u : Int} (hu : ¬ (p : Int) ∣ u) (k : Int) : S p (u * u * k) = chi p u * S p k := by
  unfold S
  have h1 : sm p (fun x => chi p ((x : Int) * x * x - u * u * k * x)) =
      sm p (fun z => chi p ((u * z) * (u * z) * (u * z) - u * u * k * (u * z))) := by
    symm
    exact reindex (p_pos hp) (fun z => u * (z : Int)) (mul_inj hp hu) (fun w => chi p (w * w * w - u * u * k * w))
      (fun a b hab => chi_congr p (cg_sub (cg_mul (cg_mul hab hab) hab) (cg_mul (cg_refl p _) hab)))
  rw [h1, ← sm_mul_left]
  apply sm_congr; intro z _
  rw [show (u * (z : Int)) * (u * z) * (u * z) - u * u * k * (u * z) = u * ((u * u) * ((z : Int) * z * z - k * z)) by grind]
  rw [chi_mul hp hodd, chi_mul hp hodd, chi_sq hp hodd hu, Int.one_mul]

include hp hodd in
theorem S_zero : S p 0 = 0 := by
  unfold S
  have h : ∀ x, x < p → chi p ((x : Int) * x * x - 0 * x) = chi p (x : Int) := by
    intro x _
    rw [show (x : Int) * x * x - 0 * x = (x : Int) * ((x : Int) * x) by grind, chi_mul hp hodd]
    by_cases hx : (p : Int) ∣ (x : Int)
    · rw [chi_of_dvd hp hx]; simp
    · rw [chi_sq hp hodd hx, Int.mul_one]
  rw [sm_congr p _ _ h, sum_chi (p_pos hp)]

include hp hodd in
theorem unit_sq {u : Int} (hu : ¬ (p : Int) ∣ u) : chi p u * chi p u = 1 := by
  rcases chi_unit hp hodd hu with h | h <;> rw [h] <;> rfl

theorem not_dvd_root {k : Int} {u : Nat} (hk : ¬ (p : Int) ∣ k) (huk : cg p ((u : Int) * u) k) :
    ¬ (p : Int) ∣ (u : Int) := by
  intro h
  apply hk
  have h1 : (p : Int) ∣ (u : Int) * u := Int.dvd_trans h (Int.dvd_mul_right _ _)
  have := Int.dvd_sub h1 huk
  rwa [show (u : Int) * u - ((u : Int) * u - k) = k by omega] at this

include hp hodd in
/-- 잉여 k : S(k)² = S(1)² -/
theorem S_sq_of_res {k : Int} (hk : chi p k = 1) : S p k * S p k = S p 1 * S p 1 := by
  have hpk := not_dvd_of_chi hp hodd (a := k) (by omega)
  obtain ⟨u, _, huk⟩ := isSq_of_chi hk
  have hpu := not_dvd_root hpk huk
  have e : S p k = S p ((u : Int) * u * 1) := S_congr (cg_trans (cg_symm huk) (cg_of_eq (by grind)))
  rw [e, S_scale hp hodd hpu]
  have h2 := unit_sq hp hodd hpu
  generalize chi p (u : Int) = c at h2 ⊢
  generalize S p 1 = A
  grind

include hp hodd in
/-- 비잉여 k, g : S(k)² = S(g)² -/
theorem S_sq_of_nonres {k g : Int} (hk : chi p k = -1) (hg : chi p g = -1) : S p k * S p k = S p g * S p g := by
  have hpg := not_dvd_of_chi hp hodd (a := g) (by omega)
  have hi := inv_spec hp hpg
  have hpi := inv_not_dvd hp hpg
  have hci : chi p (inv p g) = -1 := by
    have h1 : chi p g * chi p (inv p g) = 1 := by
      rw [← chi_mul hp hodd, chi_congr p hi, chi_one hp hodd]
    rcases chi_unit hp hodd hpi with h | h
    · rw [hg, h] at h1; omega
    · exact h
  have hres : chi p (k * inv p g) = 1 := by rw [chi_mul hp hodd, hk, hci]; rfl
  have hpki := not_dvd_of_chi hp hodd (a := k * inv p g) (by omega)
  obtain ⟨u, _, huk⟩ := isSq_of_chi hres
  have hpu := not_dvd_root hpki huk
  have e : cg p k ((u : Int) * u * g) := by
    have e1 : cg p k (k * (g * inv p g)) := cg_trans (cg_of_eq (by grind)) (cg_mul (cg_refl p k) (cg_symm hi))
    have e2 : cg p (k * (g * inv p g)) (g * (k * inv p g)) := cg_of_eq (by grind)
    have e3 : cg p (g * (k * inv p g)) (g * ((u : Int) * u)) := cg_mul (cg_refl p g) (cg_symm huk)
    exact cg_trans e1 (cg_trans e2 (cg_trans e3 (cg_of_eq (by grind))))
  rw [S_congr e, S_scale hp hodd hpu]
  have h2 := unit_sq hp hodd hpu
  generalize chi p (u : Int) = c at h2 ⊢
  generalize S p g = B
  grind

include hp hodd in
theorem sum_S_sq_split {g : Int} (hg : chi p g = -1) :
    sm p (fun k => S p k * S p k) =
      sm p (fun k => ind (chi p (k : Int) = 1)) * (S p 1 * S p 1) +
      sm p (fun k => ind (chi p (k : Int) = -1)) * (S p g * S p g) := by
  rw [← sm_mul_right, ← sm_mul_right, ← sm_add]
  apply sm_congr; intro k _
  rcases chi_cases hp hodd (k : Int) with h | h | h
  · have hk0 : (p : Int) ∣ (k : Int) := (chi_eq_zero_iff hp hodd _).mp h
    rw [ind_neg (by rw [h]; decide), ind_neg (by rw [h]; decide)]
    have : S p (k : Int) = S p 0 := S_congr (by unfold cg; simpa using hk0)
    rw [this, S_zero hp hodd]; simp
  · rw [ind_pos h, ind_neg (by rw [h]; decide), S_sq_of_res hp hodd h]; simp
  · rw [ind_neg (by rw [h]; decide), ind_pos h, S_sq_of_nonres hp hodd h hg]; simp

include hp hodd in
/-- 잉여의 수 = (p − 1)/2 -/
theorem count_res : 2 * sm p (fun k => ind (chi p (k : Int) = 1)) = (p : Int) - 1 := by
  have h1 := count_eq hp hodd
  have h2 : sm p (fun k => ind (chi p (k : Int) = 1)) + sm p (fun k => ind (chi p (k : Int) = -1)) = (p : Int) - 1 := by
    rw [← sm_add]
    have h3 : ∀ k, k < p → ind (chi p (k : Int) = 1) + ind (chi p (k : Int) = -1) = 1 - ind (k = 0) := by
      intro k hk
      rcases chi_cases hp hodd (k : Int) with h | h | h
      · have hk0 : k = 0 := uniq (p_pos hp) hk (p_pos hp)
          (by unfold cg; simpa using (chi_eq_zero_iff hp hodd _).mp h)
        rw [ind_neg (by rw [h]; decide), ind_neg (by rw [h]; decide), ind_pos hk0]; rfl
      · have hk0 : k ≠ 0 := by intro h0; subst h0; rw [chi_of_dvd hp (by simp)] at h; omega
        rw [ind_pos h, ind_neg (by rw [h]; decide), ind_neg hk0]; rfl
      · have hk0 : k ≠ 0 := by intro h0; subst h0; rw [chi_of_dvd hp (by simp)] at h; omega
        rw [ind_neg (by rw [h]; decide), ind_pos h, ind_neg hk0]; rfl
    rw [sm_congr p _ _ h3, sm_sub, sm_const]
    have := sm_single p 0 (p_pos hp) (fun _ => 1)
    have h5 : sm p (fun x => ind (x = 0)) = 1 := by simpa [ind] using this
    rw [h5]; simp
  omega

include hp hodd in
theorem exists_nonres : ∃ g : Nat, g < p ∧ chi p (g : Int) = -1 := by
  apply exists_of_sm_ind p (fun g => chi p (g : Int) = -1)
  have h1 := count_res hp hodd
  have h2 := count_eq hp hodd
  have : 3 ≤ p := by have := hp.1; omega
  omega

include hp hodd in
/-- 야콥스탈 : S(1)² + S(g)² = 2p (1 + χ(−1)) (g 는 비잉여) -/
theorem jacobsthal {g : Int} (hg : chi p g = -1) :
    S p 1 * S p 1 + S p g * S p g = 2 * (p : Int) * (1 + chi p (-1)) := by
  have h1 := sum_S_sq hp hodd
  rw [sum_S_sq_split hp hodd hg] at h1
  have h2 := count_res hp hodd
  have h3 := count_eq hp hodd
  generalize sm p (fun k => ind (chi p (k : Int) = 1)) = Q at h1 h2 h3
  rw [← h3] at h1
  generalize S p 1 * S p 1 = A at h1 ⊢
  generalize S p g * S p g = B at h1 ⊢
  generalize chi p (-1) = c at h1 ⊢
  have h4 : ((p : Int) - 1) * (A + B) = ((p : Int) - 1) * (2 * (p : Int) * (1 + c)) := by
    rw [← h2]; grind
  have hp3 : 3 ≤ p := by have := hp.1; omega
  exact Int.eq_of_mul_eq_mul_left (by omega) h4

end coset

/-! ## 11. 점의 수와 하세 한계 -/

/-- #E(F_p) = 무한원점 1 + Σ_x (x³ − x 의 제곱근 개수) -/
def card (p : Nat) : Int := 1 + sm p (fun x => nr p ((x : Int) * x * x - x))

/-- 프로베니우스의 대각합 a_p = p + 1 − #E(F_p) -/
def ap (p : Nat) : Int := (p : Int) + 1 - card p

theorem ap_eq (p : Nat) : ap p = - S p 1 := by
  unfold ap card S chi
  rw [sm_sub, sm_const]
  have : sm p (fun x => nr p ((x : Int) * x * x - 1 * x)) = sm p (fun x => nr p ((x : Int) * x * x - x)) := by
    apply sm_congr; intro x _; simp
  rw [this]; simp; omega

/-- 4p 는 제곱수가 아니다 -/
theorem not_sq_four_p {p : Nat} (hp : IsPrime p) (s : Int) : s * s ≠ 4 * (p : Int) := by
  intro h
  have h2' : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases h2' with h2 | h2
  · have ht : s = 2 * (s / 2) := by omega
    generalize s / 2 = t at ht
    subst ht
    have h3 : t * t = (p : Int) := by grind
    have h4 : t.natAbs * t.natAbs = p := by
      have := Int.natAbs_mul_self (a := t)
      omega
    rcases hp.2 t.natAbs ⟨t.natAbs, h4.symm⟩ with h5 | h5
    · rw [h5] at h4; have := hp.1; omega
    · rw [h5] at h4
      have := hp.1
      have : p * p ≥ 2 * p := Nat.mul_le_mul_right p this
      omega
  · have ht : s = 2 * (s / 2) + 1 := by omega
    generalize s / 2 = t at ht
    subst ht
    have : (2 * t + 1) * (2 * t + 1) = 4 * (t * t + t) + 1 := by grind
    omega

section hasse
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp hodd in
/-- ★ 하세 한계 — y² = x³ − x 의 모든 홀수 소수 p 에서  a_p² < 4p -/
theorem hasse : ap p * ap p < 4 * (p : Int) := by
  obtain ⟨g, _, hg⟩ := exists_nonres hp hodd
  have hj := jacobsthal hp hodd hg
  have hc : chi p (-1) ≤ 1 := by rcases chi_cases hp hodd (-1) with h | h | h <;> omega
  rw [ap_eq]
  have h0 : 0 ≤ S p (g : Int) * S p (g : Int) := by
    have := Int.sq_nonneg (S p (g : Int))
    have e : S p (g : Int) ^ 2 = S p (g : Int) * S p (g : Int) := by grind
    omega
  have h5 := Int.mul_le_mul_of_nonneg_left hc (by omega : (0 : Int) ≤ 2 * p)
  have e : 2 * (p : Int) * (1 + chi p (-1)) = 2 * p + 2 * p * chi p (-1) := by grind
  have hle : S p 1 * S p 1 ≤ 4 * (p : Int) := by omega
  have hne := not_sq_four_p hp (S p 1)
  have e2 : -S p 1 * -S p 1 = S p 1 * S p 1 := by grind
  omega

end hasse


/-! ## 12. 짝짓기 — 대합(σσ = id) 의 합은 고정점 + 2 × (반쪽) -/

/-- 자연수 첨자 위의 다시 세기 -/
theorem reindexN {p : Nat} (hp : 0 < p) (σ : Nat → Nat) (hlt : ∀ x, x < p → σ x < p)
    (hinj : ∀ x x', x < p → x' < p → σ x = σ x' → x = x') (F : Nat → Int) :
    sm p (fun x => F (σ x)) = sm p F := by
  let g : Int → Int := fun z => F (z % (p : Int)).toNat
  have hg : Resp p g := by
    intro u v huv
    obtain ⟨k, hk⟩ := huv
    have : u = v + (p : Int) * k := by omega
    simp only [g, this, Int.add_mul_emod_self_left]
  have hgy : ∀ y, y < p → g (y : Int) = F y := by
    intro y hy
    simp only [g]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  have h1 : sm p (fun x => F (σ x)) = sm p (fun x => g ((σ x : Nat) : Int)) := by
    apply sm_congr; intro x hx; rw [hgy (σ x) (hlt x hx)]
  have h2 := reindex hp (fun x => ((σ x : Nat) : Int))
    (fun x x' hx hx' hc => hinj x x' hx hx' (uniq hp (hlt x hx) (hlt x' hx') hc)) g hg
  rw [h1, h2]
  apply sm_congr; intro y hy; exact hgy y hy

/-- 대합의 합 -/
theorem pair_sum {p : Nat} (hp : 0 < p) (σ : Nat → Nat) (hlt : ∀ x, x < p → σ x < p)
    (hinv : ∀ x, x < p → σ (σ x) = x) (F : Nat → Int) (hF : ∀ x, x < p → F (σ x) = F x) :
    sm p F = sm p (fun x => F x * ind (σ x = x)) + 2 * sm p (fun x => F x * ind (x < σ x)) := by
  have hinj : ∀ x x', x < p → x' < p → σ x = σ x' → x = x' := by
    intro x x' hx hx' h
    rw [← hinv x hx, ← hinv x' hx', h]
  have hsplit : ∀ x, x < p → F x = F x * ind (σ x = x) + F x * ind (x < σ x) + F x * ind (σ x < x) := by
    intro x _
    by_cases h1 : σ x = x
    · rw [ind_pos h1, ind_neg (by omega), ind_neg (by omega)]; omega
    · by_cases h2 : x < σ x
      · rw [ind_neg h1, ind_pos h2, ind_neg (by omega)]; omega
      · rw [ind_neg h1, ind_neg h2, ind_pos (by omega)]; omega
  have hhalf : sm p (fun x => F x * ind (σ x < x)) = sm p (fun x => F x * ind (x < σ x)) := by
    have := reindexN hp σ hlt hinj (fun x => F x * ind (σ x < x))
    rw [← this]
    apply sm_congr; intro x hx
    show F (σ x) * ind (σ (σ x) < σ x) = F x * ind (x < σ x)
    rw [hF x hx, hinv x hx]
  rw [sm_congr p _ _ hsplit, sm_add, sm_add, hhalf]
  omega

/-! ## 13. χ(−1) 과 p 를 4 로 나눈 나머지 -/

section mod4
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

/-- 역원의 대표 -/
noncomputable def invN (p : Nat) (u : Int) : Nat := (inv p u).toNat

theorem invN_cast (p : Nat) (u : Int) : ((invN p u : Nat) : Int) = inv p u := by
  obtain ⟨v, _, hv⟩ := inv_range p u
  unfold invN; rw [hv]; simp

theorem invN_lt {p : Nat} (hp0 : 0 < p) (u : Int) : invN p u < p := by
  obtain ⟨v, hv1, hv⟩ := inv_range p u
  unfold invN; rw [hv]; simp; omega

include hp in
/-- 역원은 하나뿐 -/
theorem inv_unique {x y : Int} (hx : ¬ (p : Int) ∣ x) (h : cg p (x * y) 1) : cg p y (inv p x) := by
  have hi := inv_spec hp hx
  -- y ≡ y (x inv x) = inv x (x y) ≡ inv x
  have e1 : cg p y (y * (x * inv p x)) := cg_trans (cg_of_eq (by grind)) (cg_mul (cg_refl p y) (cg_symm hi))
  have e2 : cg p (y * (x * inv p x)) (inv p x * (x * y)) := cg_of_eq (by grind)
  have e3 : cg p (inv p x * (x * y)) (inv p x * 1) := cg_mul (cg_refl p _) h
  exact cg_trans e1 (cg_trans e2 (cg_trans e3 (cg_of_eq (by grind))))

include hp in
theorem invN_invN {x : Nat} (hx : x < p) : invN p (invN p (x : Int) : Int) = x := by
  have hp0 := p_pos hp
  by_cases hx0 : x = 0
  · subst hx0
    have : invN p ((0 : Nat) : Int) = 0 := by unfold invN; rw [show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp]; rfl
    rw [this, this]
  · have hpx : ¬ (p : Int) ∣ (x : Int) := fun h1 => hx0 (uniq hp0 hx hp0 (by unfold cg; simpa using h1))
    have hi := inv_spec hp hpx
    have hpy := inv_not_dvd hp hpx
    apply uniq hp0 (invN_lt hp0 _) hx
    rw [invN_cast, invN_cast]
    -- inv(inv x) ≡ x : x · inv x ≡ 1 이므로 inv x 의 역원은 x
    have : cg p (inv p (x : Int) * (x : Int)) 1 := cg_trans (cg_of_eq (by grind)) hi
    exact cg_symm (inv_unique hp hpy this)

include hp hodd in
theorem chi_inv {u : Int} (hu : ¬ (p : Int) ∣ u) : chi p (inv p u) = chi p u := by
  have hi := inv_spec hp hu
  have hpi := inv_not_dvd hp hu
  have h1 : chi p u * chi p (inv p u) = 1 := by
    rw [← chi_mul hp hodd, chi_congr p hi, chi_one hp hodd]
  rcases chi_unit hp hodd hu with h | h <;> rcases chi_unit hp hodd hpi with h' | h' <;>
    rw [h, h'] at h1 <;> omega

include hp hodd in
/-- 역원의 고정점은 0 · 1 · p − 1 뿐 -/
theorem invN_fixed {x : Nat} (hx : x < p) : invN p (x : Int) = x ↔ (x = 0 ∨ x = 1 ∨ x = p - 1) := by
  have hp0 := p_pos hp
  have hp3 : 3 ≤ p := by have := hp.1; omega
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hpx : ¬ (p : Int) ∣ (x : Int) := fun h1 => hx0 (uniq hp0 hx hp0 (by unfold cg; simpa using h1))
      have hi := inv_spec hp hpx
      rw [← invN_cast, h] at hi
      -- x · x ≡ 1 · 1
      have h2 : cg p (((1 : Nat) : Int) * ((1 : Nat) : Int)) ((x : Int) * x) := cg_symm (cg_trans hi (cg_of_eq (by simp)))
      rcases (sq_eq_iff hp (x := 1) (y := x) (by omega) (by omega) hx).mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3
  · rintro (h | h | h)
    · subst h; unfold invN; rw [show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp]; rfl
    · subst h
      apply uniq hp0 (invN_lt hp0 _) hx
      rw [invN_cast]
      have := inv_unique hp (x := ((1 : Nat) : Int)) (y := ((1 : Nat) : Int)) (not_dvd_one hp) (cg_of_eq (by simp))
      exact cg_symm this
    · apply uniq hp0 (invN_lt hp0 _) hx
      rw [invN_cast]
      have hc : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
      have hpx : ¬ (p : Int) ∣ ((p - 1 : Nat) : Int) := by
        rw [hc]; intro h1
        apply not_dvd_one hp
        have := Int.dvd_sub (Int.dvd_refl (p : Int)) h1
        rwa [show (p : Int) - ((p : Int) - 1) = 1 by omega] at this
      have hsq : cg p (((p - 1 : Nat) : Int) * ((p - 1 : Nat) : Int)) 1 := by
        rw [hc]; unfold cg; exact ⟨(p : Int) - 2, by grind⟩
      rw [h]
      exact cg_symm (inv_unique hp hpx hsq)

include hp hodd in
/-- ★ 첫 보충 법칙 : χ(−1) = 1 ⇔ p ≡ 1 (mod 4) -/
theorem chi_neg_one : chi p (-1) = 1 ↔ p % 4 = 1 := by
  have hp0 := p_pos hp
  have hp3 : 3 ≤ p := by have := hp.1; omega
  let σ : Nat → Nat := fun x => invN p (x : Int)
  let F : Nat → Int := fun x => ind (chi p (x : Int) = 1)
  have hlt : ∀ x, x < p → σ x < p := fun x _ => invN_lt hp0 _
  have hinv : ∀ x, x < p → σ (σ x) = x := fun x hx => invN_invN hp hx
  have hF : ∀ x, x < p → F (σ x) = F x := by
    intro x hx
    simp only [F, σ]
    rw [invN_cast]
    by_cases hx0 : (p : Int) ∣ (x : Int)
    · have : x = 0 := uniq hp0 hx hp0 (by unfold cg; simpa using hx0)
      subst this
      rw [show ((0 : Nat) : Int) = 0 by rfl, inv_zero hp]
    · rw [chi_inv hp hodd hx0]
  have hpair := pair_sum hp0 σ hlt hinv F hF
  -- 고정점 0 · 1 · p − 1
  have hfix : sm p (fun x => F x * ind (σ x = x)) = 1 + ind (chi p (-1) = 1) := by
    have h1 : ∀ x, x < p → F x * ind (σ x = x) =
        (if x = 1 then 1 else 0) + (if x = p - 1 then ind (chi p (-1) = 1) else 0) := by
      intro x hx
      simp only [F, σ]
      by_cases h0 : x = 0
      · subst h0
        rw [ind_neg (by rw [chi_of_dvd hp (by simp)]; decide)]
        simp; omega
      · by_cases h1 : x = 1
        · subst h1
          rw [ind_pos (by simpa using chi_one hp hodd), ind_pos ((invN_fixed hp hodd hx).mpr (Or.inr (Or.inl rfl)))]
          simp; omega
        · by_cases h2 : x = p - 1
          · rw [ind_pos ((invN_fixed hp hodd hx).mpr (Or.inr (Or.inr h2)))]
            have hc : (x : Int) = (p : Int) - 1 := by omega
            have e : chi p (x : Int) = chi p (-1) := chi_congr p (by rw [hc]; unfold cg; exact ⟨1, by omega⟩)
            rw [e, ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
            omega
          · rw [show ind (invN p (x : Int) = x) = 0 from
              ind_neg (fun h3 => by rcases (invN_fixed hp hodd hx).mp h3 with h4 | h4 | h4 <;> omega)]
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
            omega
    rw [sm_congr p _ _ h1, sm_add, sm_single p 1 (by omega) (fun _ => 1), sm_single p (p - 1) (by omega) (fun _ => ind (chi p (-1) = 1))]
  have hcount := count_res hp hodd
  have hQ : sm p F = sm p (fun k => ind (chi p (k : Int) = 1)) := rfl
  rw [hfix, ← hQ] at hpair
  have hI := ind_nonneg (chi p (-1) = 1)
  have hI1 := ind_le_one (chi p (-1) = 1)
  constructor
  · intro h
    rw [ind_pos h] at hpair
    omega
  · intro h
    apply Classical.byContradiction
    intro hne
    rw [ind_neg hne] at hpair
    omega

include hp hodd in
/-- ★ p ≡ 3 (mod 4) 이면 a_p = 0 (초특이) -/
theorem ap_zero (h3 : p % 4 = 3) : ap p = 0 := by
  have hc : chi p (-1) = -1 := by
    rcases chi_unit hp hodd (a := -1) (fun h => not_dvd_one hp (by simpa using Int.dvd_neg.mpr h)) with h | h
    · have := (chi_neg_one hp hodd).mp h; omega
    · exact h
  obtain ⟨g, _, hg⟩ := exists_nonres hp hodd
  have hj := jacobsthal hp hodd hg
  rw [hc] at hj
  have h1 : 0 ≤ S p 1 * S p 1 := by
    have := Int.sq_nonneg (S p 1); have e : S p 1 ^ 2 = S p 1 * S p 1 := by grind
    omega
  have h2 : 0 ≤ S p (g : Int) * S p (g : Int) := by
    have := Int.sq_nonneg (S p (g : Int)); have e : S p (g : Int) ^ 2 = S p (g : Int) * S p (g : Int) := by grind
    omega
  have h3 : S p 1 * S p 1 = 0 := by
    have : 2 * (p : Int) * (1 + -1) = 0 := by grind
    omega
  rw [ap_eq]
  rcases Int.mul_eq_zero.mp h3 with h4 | h4 <;> rw [h4] <;> rfl

include hp hodd in
/-- χ(−1) = 1 이면 S(k) 는 짝수 (x ↔ −x 짝짓기) -/
theorem S_even (hc : chi p (-1) = 1) (k : Int) : ∃ m, S p k = 2 * m := by
  have hp0 := p_pos hp
  let σ : Nat → Nat := fun x => (p - x) % p
  have hlt : ∀ x, x < p → σ x < p := fun x _ => Nat.mod_lt _ hp0
  have hσ0 : σ 0 = 0 := by simp [σ]
  have hσx : ∀ x, 0 < x → x < p → σ x = p - x := by
    intro x h0 hx; simp only [σ]; exact Nat.mod_eq_of_lt (by omega)
  have hinv : ∀ x, x < p → σ (σ x) = x := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; rw [hσ0, hσ0]
    · rw [hσx x (by omega) hx, hσx (p - x) (by omega) (by omega)]; omega
  let F : Nat → Int := fun x => chi p ((x : Int) * x * x - k * x)
  have hF : ∀ x, x < p → F (σ x) = F x := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; rw [hσ0]
    · simp only [F]
      rw [hσx x (by omega) hx]
      have hc' : ((p - x : Nat) : Int) = (p : Int) - x := by omega
      rw [hc']
      have e : cg p (((p : Int) - x) * ((p : Int) - x) * ((p : Int) - x) - k * ((p : Int) - x))
          (-1 * ((x : Int) * x * x - k * x)) := by
        unfold cg
        exact ⟨(p : Int) * p - 3 * p * x + 3 * x * x - k, by grind⟩
      rw [chi_congr p e, chi_mul hp hodd, hc, Int.one_mul]
  have hpair := pair_sum hp0 σ hlt hinv F hF
  have hfix : sm p (fun x => F x * ind (σ x = x)) = 0 := by
    rw [sm_congr p _ (fun _ => 0) (fun x hx => by
      by_cases h0 : x = 0
      · subst h0
        show chi p (((0 : Nat) : Int) * ((0 : Nat) : Int) * ((0 : Nat) : Int) - k * ((0 : Nat) : Int)) * _ = 0
        rw [chi_of_dvd hp (by simp)]; simp
      · rw [show ind (σ x = x) = 0 from ind_neg (by rw [hσx x (by omega) hx]; omega)]; simp)]
    rw [sm_const]; simp
  rw [hfix] at hpair
  exact ⟨sm p (fun x => F x * ind (x < σ x)), by unfold S; rw [hpair]; omega⟩


include hp hodd in
/-- ★ p ≡ 1 (mod 4) 이면 p = A² + B² 이고 a_p = 2A — 허수 곱셈 공식의 꼴
    (A 의 부호와 홀짝은 여기서 정하지 않는다 — 공식 그 자체보다 약하다) -/
theorem ap_two_squares (h1 : p % 4 = 1) : ∃ A B : Int, (p : Int) = A * A + B * B ∧ ap p = 2 * A := by
  have hc : chi p (-1) = 1 := (chi_neg_one hp hodd).mpr h1
  obtain ⟨g, _, hg⟩ := exists_nonres hp hodd
  have hj := jacobsthal hp hodd hg
  rw [hc] at hj
  obtain ⟨m1, hm1⟩ := S_even hp hodd hc 1
  obtain ⟨m2, hm2⟩ := S_even hp hodd hc (g : Int)
  refine ⟨-m1, m2, ?_, ?_⟩
  · rw [hm1, hm2] at hj
    have e : 4 * (m1 * m1 + m2 * m2) = 4 * (p : Int) := by grind
    have e2 : (-m1) * (-m1) = m1 * m1 := by grind
    omega
  · rw [ap_eq, hm1]; grind

include hp hodd in
/-- 덤 : 페르마의 두 제곱 정리 — p ≡ 1 (mod 4) 인 소수는 두 제곱수의 합 -/
theorem fermat_two_squares (h1 : p % 4 = 1) : ∃ A B : Int, (p : Int) = A * A + B * B := by
  obtain ⟨A, B, h, _⟩ := ap_two_squares hp hodd h1
  exact ⟨A, B, h⟩

end mod4

/-! ## 14. 가족 전체 — y² = x³ − kx (p ∤ k) 의 모든 곡선 -/

/-- E_k : y² = x³ − kx 의 점의 수와 대각합 -/
def cardK (p : Nat) (k : Int) : Int := 1 + sm p (fun x => nr p ((x : Int) * x * x - k * x))
def apK (p : Nat) (k : Int) : Int := (p : Int) + 1 - cardK p k

theorem apK_eq (p : Nat) (k : Int) : apK p k = - S p k := by
  unfold apK cardK S chi
  rw [sm_sub, sm_const]; simp; omega

theorem ap_eq_apK (p : Nat) : ap p = apK p 1 := by
  rw [ap_eq, apK_eq]

section family
variable {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)

include hp hodd in
/-- ★ 하세 한계 — y² = x³ − kx 꼴의 모든 곡선 (k 는 p 의 배수가 아님) · 모든 홀수 소수 p -/
theorem hasse_family {k : Int} (hk : ¬ (p : Int) ∣ k) : apK p k * apK p k < 4 * (p : Int) := by
  obtain ⟨g, _, hg⟩ := exists_nonres hp hodd
  have hj := jacobsthal hp hodd hg
  have hc : chi p (-1) ≤ 1 := by rcases chi_cases hp hodd (-1) with h | h | h <;> omega
  have h1 : 0 ≤ S p 1 * S p 1 := by
    have := Int.sq_nonneg (S p 1); have e : S p 1 ^ 2 = S p 1 * S p 1 := by grind
    omega
  have h2 : 0 ≤ S p (g : Int) * S p (g : Int) := by
    have := Int.sq_nonneg (S p (g : Int)); have e : S p (g : Int) ^ 2 = S p (g : Int) * S p (g : Int) := by grind
    omega
  have h5 := Int.mul_le_mul_of_nonneg_left hc (by omega : (0 : Int) ≤ 2 * p)
  have e : 2 * (p : Int) * (1 + chi p (-1)) = 2 * p + 2 * p * chi p (-1) := by grind
  have hk2 : S p k * S p k ≤ 4 * (p : Int) := by
    rcases chi_unit hp hodd hk with h | h
    · rw [S_sq_of_res hp hodd h]; omega
    · rw [S_sq_of_nonres hp hodd h hg]; omega
  have hne := not_sq_four_p hp (S p k)
  rw [apK_eq]
  have e2 : -S p k * -S p k = S p k * S p k := by grind
  omega

include hp hodd in
/-- p ≡ 3 (mod 4) 이면 모든 k 에서 a_p(E_k) = 0 — p ∤ k 인 곡선은 초특이, k ≡ 0 (특이 곡선 y² = x³) 에서도 값은 0 -/
theorem apK_zero (h3 : p % 4 = 3) (k : Int) : apK p k = 0 := by
  have hc : chi p (-1) = -1 := by
    rcases chi_unit hp hodd (a := -1) (fun h => not_dvd_one hp (by simpa using Int.dvd_neg.mpr h)) with h | h
    · have := (chi_neg_one hp hodd).mp h; omega
    · exact h
  have hsum := sum_S_sq hp hodd
  rw [hc] at hsum
  have hall : sm p (fun k => S p k * S p k) = 0 := by rw [hsum]; grind
  -- 제곱의 합이 0 이면 모두 0
  have hnn : ∀ i, i < p → 0 ≤ S p (i : Int) * S p (i : Int) := by
    intro i _
    have := Int.sq_nonneg (S p (i : Int)); have e : S p (i : Int) ^ 2 = S p (i : Int) * S p (i : Int) := by grind
    omega
  have hz := sm_eq_of_le p (fun _ => 0) (fun i => S p (i : Int) * S p (i : Int)) (fun i hi => hnn i hi)
    (by rw [hall, sm_const]; simp)
  obtain ⟨r, hr, hkr⟩ := rep (p_pos hp) k
  have h0 : S p (r : Int) * S p (r : Int) = 0 := (hz r hr).symm
  rw [apK_eq, S_congr hkr]
  rcases Int.mul_eq_zero.mp h0 with h4 | h4 <;> rw [h4] <;> rfl

end family

theorem apK_small :
    [apK 5 1, apK 5 2, apK 5 3, apK 5 4, apK 13 1, apK 13 2, apK 13 3, apK 13 4, apK 13 5, apK 13 6] =
    [-2, -4, 4, 2, 6, -4, 6, -6, -4, -4] := by
  decide +kernel

/-! ## 15. 작은 소수에서 커널이 직접 센 값 (파이썬으로 점을 하나하나 센 값과 같다) -/

theorem ap_small :
    [ap 3, ap 5, ap 7, ap 11, ap 13, ap 17, ap 19, ap 23, ap 29, ap 31, ap 37, ap 41, ap 43, ap 47,
     ap 53, ap 59, ap 61, ap 67, ap 71, ap 73, ap 79, ap 83, ap 89, ap 97] =
    [0, -2, 0, 0, 6, 2, 0, 0, -10, 0, -2, 10, 0, 0, 14, 0, -10, 0, 0, -6, 0, 0, 10, 18] := by
  decide +kernel

/-! ## 16. IsPrime 은 비어 있지 않다 — 정의 그대로 판정하고, 주 정리를 실제 소수에 적용 -/

theorem isPrime_of_bounded (p : Nat) (h2 : 2 ≤ p)
    (h : ∀ m, m < p + 1 → m ∣ p → m = 1 ∨ m = p) : IsPrime p :=
  ⟨h2, fun m hm => h m (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)) hm⟩

theorem isPrime_iff_bounded (p : Nat) :
    IsPrime p ↔ (2 ≤ p ∧ ∀ m, m < p + 1 → m ∣ p → m = 1 ∨ m = p) :=
  ⟨fun h => ⟨h.1, fun m _ hm => h.2 m hm⟩, fun h => isPrime_of_bounded p h.1 h.2⟩

instance (p : Nat) : Decidable (IsPrime p) := decidable_of_iff _ (isPrime_iff_bounded p).symm

theorem prime7 : IsPrime 7 := isPrime_of_bounded 7 (by decide) (by decide)
theorem prime13 : IsPrime 13 := isPrime_of_bounded 13 (by decide) (by decide)
theorem not_prime1 : ¬ IsPrime 1 := fun h => by have := h.1; omega
theorem not_prime91 : ¬ IsPrime 91 := by decide

/-- IsPrime 그 자체로 거른 100 아래의 홀수 소수 -/
theorem odd_IsPrime_below_100 :
    (List.range 100).filter (fun n => decide (IsPrime n) && n % 2 == 1) =
    [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] := by
  decide +kernel

/-- 주 정리를 실제 소수에 — 가설이 채워진다 -/
theorem hasse_13 : ap 13 * ap 13 < 4 * ((13 : Nat) : Int) := hasse prime13 (by decide)
theorem ap_zero_7 : ap 7 = 0 := ap_zero prime7 (by decide) (by decide)
theorem two_squares_13 : ∃ A B : Int, ((13 : Nat) : Int) = A * A + B * B ∧ ap 13 = 2 * A :=
  ap_two_squares prime13 (by decide) (by decide)

/-- 덤 : 나눗셈 시험(불 값)으로 거른 목록도 같다 -/
theorem odd_primes_below_100 :
    ((List.range 100).filter (fun n => 3 ≤ n && n % 2 == 1 && (List.range n).all (fun d => d < 2 || n % d != 0))) =
    [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] := by
  decide +kernel


end Trombo.HasseAll

#print axioms Trombo.HasseAll.euclid
#print axioms Trombo.HasseAll.reindex
#print axioms Trombo.HasseAll.sum_chi
#print axioms Trombo.HasseAll.chi_mul
#print axioms Trombo.HasseAll.conic
#print axioms Trombo.HasseAll.sum_S_sq
#print axioms Trombo.HasseAll.S_scale
#print axioms Trombo.HasseAll.count_res
#print axioms Trombo.HasseAll.jacobsthal
#print axioms Trombo.HasseAll.ap_eq
#print axioms Trombo.HasseAll.not_sq_four_p
#print axioms Trombo.HasseAll.hasse
#print axioms Trombo.HasseAll.pair_sum
#print axioms Trombo.HasseAll.chi_neg_one
#print axioms Trombo.HasseAll.ap_zero
#print axioms Trombo.HasseAll.S_even
#print axioms Trombo.HasseAll.ap_two_squares
#print axioms Trombo.HasseAll.fermat_two_squares
#print axioms Trombo.HasseAll.ap_small
#print axioms Trombo.HasseAll.odd_primes_below_100
#print axioms Trombo.HasseAll.odd_IsPrime_below_100
#print axioms Trombo.HasseAll.hasse_13
#print axioms Trombo.HasseAll.two_squares_13
#print axioms Trombo.HasseAll.hasse_family
#print axioms Trombo.HasseAll.apK_zero
#print axioms Trombo.HasseAll.apK_small

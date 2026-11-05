/-
황금소수의 일반 증명 — 모든 소수 p 에서 Lₚ ≡ 1 · Fₚ ≡ 5^((p−1)/2) (mod p) (■) · 앞선 소수 301 개 확인(②)의 일반판
(린 4 코어만 · Mathlib 없음 · sorry 없음 · native_decide 없음 · 새 공리 없음)

  A. choose_dvd         : 0 < k < p 이면 p ∣ C(p, k)
  B. fermat             : aᵖ ≡ a (mod p)  (신입생의 꿈 (1 + a)ᵖ ≡ 1 + aᵖ 와 a 에 대한 귀납)
  C. lucas_prime        : Lₚ ≡ 1 (mod p)
  D. fib_prime          : Fₚ ≡ 5^((p−1)/2) (mod p)  (p = 2 · p = 5 포함)
  E. five_reciprocity   : p ≡ ±1 (mod 5) 이면 5^((p−1)/2) ≡ 1 , p ≡ ±2 (mod 5) 이면 5^((p−1)/2) ≡ −1 (mod p)
  따름 fib_prime_legendre : Fₚ ≡ (p/5) (mod p) · 5 ∣ F₅
  따름 fib_rank           : p ≡ ±1 (mod 5) 이면 p ∣ F (p − 1) , p ≡ ±2 (mod 5) 이면 p ∣ F (p + 1)

길 : (1 + √5)ⁿ = Aₙ + Bₙ √5 의 두 성분을 이항 합 Σ C(n, k)(√5)ᵏ 로 적고 (2Aₙ = 2ⁿ Lₙ · 2Bₙ = 2ⁿ Fₙ),
소수 p 에서 가운데 이항 계수가 모두 p 의 배수라는 것(A)과 2ᵖ ≡ 2 (B)로 C · D 를 얻는다.
E 는 가우스 합 g = x − x² − x³ + x⁴ = x (1 − x)² (1 + x) 를 Z[x]/(x⁵ − 1) 안에서 쓴다 :
g³ = 5g 이므로 gᵖ = 5^((p−1)/2) g , 한편 신입생의 꿈으로 gᵖ ≡ g(xᵖ) = (p/5) g (mod p). x 의 계수를 비교한다.
모든 정리는 모든 소수에 대해 성립하며 끝에 #print axioms 로 쓰인 공리를 보인다.
검증 : lean 황금소수일반.lean  (린 v4.34.0)
-/
namespace GoldenPrimeAll

/-! ## 0. 정의 -/

def F : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

def L : Nat → Int
  | 0 => 2
  | 1 => 1
  | n + 2 => L n + L (n + 1)

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ n k, n < k → choose n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt n k (by omega), choose_eq_zero_of_lt n (k + 1) (by omega)]

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt n (n + 1) (by omega)]

theorem choose_one_right : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_zero_right, choose_one_right n]; omega

theorem succ_mul_choose_eq : ∀ n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
    rw [choose_zero_succ, choose_succ_succ, choose_zero_succ, choose_zero_succ]; simp
  | n + 1, 0 => by rw [choose_zero_right, choose_one_right]
  | n + 1, k + 1 => by
    have h1 := succ_mul_choose_eq n k
    have h2 := succ_mul_choose_eq n (k + 1)
    have p1 := choose_succ_succ n k
    have p2 := choose_succ_succ (n + 1) (k + 1)
    rw [p2]
    grind

/-! ## A. p ∣ C(p, k) -/

theorem coprime_of_lt {p k : Nat} (hp : Prime p) (hk0 : 0 < k) (hkp : k < p) : Nat.Coprime p k := by
  rcases hp.2 (Nat.gcd p k) (Nat.gcd_dvd_left p k) with h | h
  · exact h
  · have : p ∣ k := h ▸ Nat.gcd_dvd_right p k
    have := Nat.le_of_dvd hk0 this
    omega

theorem choose_dvd {p k : Nat} (hp : Prime p) (hk0 : 0 < k) (hkp : k < p) : p ∣ choose p k := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.1; omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e := succ_mul_choose_eq n j
  have hd : n + 1 ∣ (j + 1) * choose (n + 1) (j + 1) :=
    ⟨choose n j, by rw [Nat.mul_comm (j + 1), ← e]⟩
  exact (coprime_of_lt hp hk0 hkp).dvd_of_dvd_mul_left hd

/-! ## 합 -/

def sm : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sm n f + f n

theorem sm_succ (n : Nat) (f : Nat → Int) : sm (n + 1) f = sm n f + f n := rfl

theorem sm_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) : sm n f = sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sm_succ, sm_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sm_add (n : Nat) (f g : Nat → Int) : sm n (fun i => f i + g i) = sm n f + sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sm_succ, sm_succ, sm_succ, ih]; omega

theorem sm_mul_left (n : Nat) (a : Int) (f : Nat → Int) : sm n (fun i => a * f i) = a * sm n f := by
  induction n with
  | zero => simp [sm]
  | succ n ih => rw [sm_succ, sm_succ, ih, Int.mul_add]

theorem sm_shift (n : Nat) (f : Nat → Int) : sm (n + 1) f = f 0 + sm n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sm]
  | succ n ih => rw [sm_succ, ih, sm_succ]; omega

theorem sm_dvd (n : Nat) (d : Int) (f : Nat → Int) (h : ∀ i, i < n → d ∣ f i) : d ∣ sm n f := by
  induction n with
  | zero => exact Int.dvd_zero d
  | succ n ih => rw [sm_succ]; exact Int.dvd_add (ih (fun i hi => h i (by omega))) (h n (by omega))

/-! ## 이항 변환 : bt c n = Σ_{k ≤ n} C(n, k) c k -/

def bt (c : Nat → Int) (n : Nat) : Int := sm (n + 1) (fun k => (choose n k : Int) * c k)

theorem bt_zero (c : Nat → Int) : bt c 0 = c 0 := by
  simp [bt, sm, choose]

theorem bt_succ (c : Nat → Int) (n : Nat) : bt c (n + 1) = bt c n + bt (fun k => c (k + 1)) n := by
  unfold bt
  rw [sm_shift (n + 1)]
  rw [sm_congr (n + 1) _ (fun i => (choose n i : Int) * c (i + 1) + (choose n (i + 1) : Int) * c (i + 1))
    (by intro i _; simp only [choose_succ_succ]; push_cast; grind)]
  rw [sm_add, sm_shift n (fun k => (choose n k : Int) * c k)]
  rw [sm_succ n (fun i => (choose n (i + 1) : Int) * c (i + 1))]
  rw [choose_eq_zero_of_lt n (n + 1) (by omega), choose_zero_right, choose_zero_right]
  simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero]
  omega

theorem bt_congr (c d : Nat → Int) (n : Nat) (h : ∀ k, c k = d k) : bt c n = bt d n := by
  have : c = d := funext h
  rw [this]

theorem bt_mul (a : Int) (c : Nat → Int) (n : Nat) : bt (fun k => a * c k) n = a * bt c n := by
  unfold bt
  rw [← sm_mul_left]
  apply sm_congr
  intro i _
  grind

/-- 소수 p 에서 가운데 항은 모두 p 의 배수 : bt c p ≡ c 0 + c p -/
theorem bt_prime {p : Nat} (hp : Prime p) (c : Nat → Int) : (p : Int) ∣ bt c p - c 0 - c p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
  unfold bt
  rw [sm_succ, sm_shift m, choose_zero_right, choose_self]
  have hmid : ((m + 1 : Nat) : Int) ∣ sm m (fun i => (choose (m + 1) (i + 1) : Int) * c (i + 1)) := by
    apply sm_dvd
    intro i hi
    exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr (choose_dvd hp (by omega) (by omega)))
      (Int.dvd_mul_right _ _)
  have e : (1 : Nat) * c 0 + sm m (fun i => (choose (m + 1) (i + 1) : Int) * c (i + 1))
      + ((1 : Nat) : Int) * c (m + 1) - c 0 - c (m + 1)
      = sm m (fun i => (choose (m + 1) (i + 1) : Int) * c (i + 1)) := by
    simp only [Int.natCast_one, Int.one_mul]; omega
  rw [e]
  exact hmid

/-! ## B. 페르마 -/

theorem bt_pow (a : Int) (n : Nat) : bt (fun k => a ^ k) n = (1 + a) ^ n := by
  induction n with
  | zero => rw [bt_zero]; simp
  | succ n ih =>
    rw [bt_succ, bt_congr (fun k => a ^ (k + 1)) (fun k => a * a ^ k) n (fun k => by rw [Int.pow_succ, Int.mul_comm]),
      bt_mul, ih, Int.pow_succ]
    grind

/-- 신입생의 꿈 : (1 + a)^p ≡ 1 + a^p -/
theorem freshman {p : Nat} (hp : Prime p) (a : Int) : (p : Int) ∣ (1 + a) ^ p - 1 - a ^ p := by
  have h := bt_prime hp (fun k => a ^ k)
  rw [bt_pow] at h
  simpa using h

theorem fermat_int {p : Nat} (hp : Prime p) (a : Nat) : (p : Int) ∣ (a : Int) ^ p - a := by
  induction a with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
    simp [Int.pow_succ]
  | succ a ih =>
    have h := freshman hp (a : Int)
    have e : ((a + 1 : Nat) : Int) ^ p - ((a + 1 : Nat) : Int)
        = ((1 + (a : Int)) ^ p - 1 - (a : Int) ^ p) + ((a : Int) ^ p - a) := by
      push_cast; rw [Int.add_comm (a : Int) 1]; omega
    rw [e]
    exact Int.dvd_add h ih

/-- B. 페르마 소정리 : a^p ≡ a (mod p) -/
theorem fermat {p : Nat} (hp : Prime p) (a : Nat) : a ^ p % p = a % p := by
  have h := fermat_int hp a
  have h' : ((a ^ p : Nat) : Int) % (p : Int) = ((a : Nat) : Int) % (p : Int) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    push_cast; exact h
  have : ((a ^ p % p : Nat) : Int) = ((a % p : Nat) : Int) := by
    push_cast; exact h'
  exact Int.ofNat.inj this

/-! ## Z[√5] 의 (1 + √5)ⁿ -/

/-- (√5)^k = (ab k).1 + (ab k).2 · √5 -/
def ab : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => (5 * (ab n).2, (ab n).1)

theorem ab_parity (m : Nat) : ab (2 * m) = (5 ^ m, 0) ∧ ab (2 * m + 1) = (0, 5 ^ m) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    have e1 : ab (2 * (m + 1)) = (5 * (ab (2 * m + 1)).2, (ab (2 * m + 1)).1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; rfl
    have e2 : ab (2 * (m + 1) + 1) = (5 * (ab (2 * (m + 1))).2, (ab (2 * (m + 1))).1) := rfl
    have e3 : ab (2 * (m + 1)) = (5 ^ (m + 1), 0) := by
      rw [e1, ih.2, Int.pow_succ, Int.mul_comm]
    exact ⟨e3, by rw [e2, e3]; simp⟩

/-- (1 + √5)ⁿ = A n + B n · √5 -/
def A (n : Nat) : Int := bt (fun k => (ab k).1) n
def B (n : Nat) : Int := bt (fun k => (ab k).2) n

theorem A_succ (n : Nat) : A (n + 1) = A n + 5 * B n := by
  unfold A B
  rw [bt_succ]
  rw [show (fun k => (ab (k + 1)).1) = (fun k => 5 * (ab k).2) from rfl, bt_mul]

theorem B_succ (n : Nat) : B (n + 1) = B n + A n := by
  unfold A B
  rw [bt_succ]
  rfl

theorem step_both (n : Nat) :
    2 * F (n + 1) = L n + F n ∧ 2 * L (n + 1) = L n + 5 * F n := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    have e1 : F (k + 1 + 1) = F k + F (k + 1) := rfl
    have e2 : L (k + 1 + 1) = L k + L (k + 1) := rfl
    obtain ⟨h1, h2⟩ := ih
    constructor <;> omega

/-- 2·(1 + √5)ⁿ = 2ⁿ·(Lₙ + Fₙ √5) -/
theorem AB_LF (n : Nat) : 2 * A n = 2 ^ n * L n ∧ 2 * B n = 2 ^ n * F n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨s1, s2⟩ := step_both n
    rw [A_succ, B_succ, Int.pow_succ]
    constructor
    · have : 2 * (A n + 5 * B n) = 2 ^ n * L n + 5 * (2 ^ n * F n) := by rw [← h1, ← h2]; grind
      rw [this]
      have : 2 ^ n * 2 * L (n + 1) = 2 ^ n * (2 * L (n + 1)) := by grind
      rw [this, s2]; grind
    · have : 2 * (B n + A n) = 2 ^ n * F n + 2 ^ n * L n := by rw [← h1, ← h2]; grind
      rw [this]
      have : 2 ^ n * 2 * F (n + 1) = 2 ^ n * (2 * F (n + 1)) := by grind
      rw [this, s1]; grind

/-! ## C · D. 소수에서 -/

theorem prime_two_or_odd {p : Nat} (hp : Prime p) : p = 2 ∨ ∃ m, p = 2 * m + 1 := by
  by_cases h : p % 2 = 0
  · left
    rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h) with h2 | h2
    · omega
    · omega
  · right; exact ⟨p / 2, by omega⟩

/-- 홀수 p 에서 반으로 나누기 : p ∣ 2x → p ∣ x -/
theorem dvd_of_dvd_two_mul {m : Nat} {x : Int} (h : ((2 * m + 1 : Nat) : Int) ∣ 2 * x) :
    ((2 * m + 1 : Nat) : Int) ∣ x := by
  have e : x = ((2 * m + 1 : Nat) : Int) * x - (m : Int) * (2 * x) := by push_cast; grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_mul_right _ _) (Int.dvd_trans h (Int.dvd_mul_left _ _))

/-- 2^p ≡ 2 (mod p) -/
theorem two_pow {p : Nat} (hp : Prime p) : (p : Int) ∣ 2 ^ p - 2 := by
  have := fermat_int hp 2
  simpa using this

/-- C. 모든 소수 p 에서 Lₚ ≡ 1 (mod p) -/
theorem lucas_prime {p : Nat} (hp : Prime p) : (p : Int) ∣ L p - 1 := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · subst h; exact ⟨1, by decide⟩
  · have hA := bt_prime hp (fun k => (ab k).1)
    have hz : (ab p).1 = 0 := by rw [h, (ab_parity m).2]
    have h0 : (ab 0).1 = 1 := rfl
    simp only [hz, h0] at hA
    have hE := (AB_LF p).1
    have h2 := two_pow hp
    have e : 2 * (L p - 1) = 2 * (bt (fun k => (ab k).1) p - 1 - 0) - (2 ^ p - 2) * L p := by
      unfold A at hE; rw [Int.sub_mul, ← hE]; omega
    have hd : (p : Int) ∣ 2 * (L p - 1) := by
      rw [e]
      exact Int.dvd_sub (Int.dvd_trans hA (Int.dvd_mul_left _ _)) (Int.dvd_trans h2 (Int.dvd_mul_right _ _))
    subst h
    exact dvd_of_dvd_two_mul hd

/-- D. 모든 소수 p 에서 Fₚ ≡ 5^((p−1)/2) (mod p) (p = 2 · p = 5 포함) -/
theorem fib_prime {p : Nat} (hp : Prime p) : (p : Int) ∣ F p - 5 ^ ((p - 1) / 2) := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · subst h; exact ⟨0, by decide⟩
  · have hB := bt_prime hp (fun k => (ab k).2)
    have hz : (ab p).2 = 5 ^ m := by rw [h, (ab_parity m).2]
    have h0 : (ab 0).2 = 0 := rfl
    simp only [hz, h0] at hB
    have hm : (p - 1) / 2 = m := by omega
    rw [hm]
    have hE := (AB_LF p).2
    have h2 := two_pow hp
    have e : 2 * (F p - 5 ^ m) = 2 * (bt (fun k => (ab k).2) p - 0 - 5 ^ m) - (2 ^ p - 2) * F p := by
      unfold B at hE; rw [Int.sub_mul, ← hE]; omega
    have hd : (p : Int) ∣ 2 * (F p - 5 ^ m) := by
      rw [e]
      exact Int.dvd_sub (Int.dvd_trans hB (Int.dvd_mul_left _ _)) (Int.dvd_trans h2 (Int.dvd_mul_right _ _))
    subst h
    exact dvd_of_dvd_two_mul hd

/-! ## E. 5 의 상호 법칙 — 가우스 합 g = x − x² − x³ + x⁴ (Z[x]/(x⁵ − 1) 안에서) -/

/-- Z[x]/(x⁵ − 1) 의 원소 a0 + a1 x + a2 x² + a3 x³ + a4 x⁴ -/
structure R where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
deriving DecidableEq

namespace R

theorem ext' {u v : R} (h0 : u.a0 = v.a0) (h1 : u.a1 = v.a1) (h2 : u.a2 = v.a2)
    (h3 : u.a3 = v.a3) (h4 : u.a4 = v.a4) : u = v := by
  cases u; cases v; simp_all

def one : R := ⟨1, 0, 0, 0, 0⟩
def X : R := ⟨0, 1, 0, 0, 0⟩
def add (u v : R) : R := ⟨u.a0 + v.a0, u.a1 + v.a1, u.a2 + v.a2, u.a3 + v.a3, u.a4 + v.a4⟩
def smul (c : Int) (u : R) : R := ⟨c * u.a0, c * u.a1, c * u.a2, c * u.a3, c * u.a4⟩
def mul (u v : R) : R :=
  ⟨u.a0 * v.a0 + u.a1 * v.a4 + u.a2 * v.a3 + u.a3 * v.a2 + u.a4 * v.a1,
   u.a0 * v.a1 + u.a1 * v.a0 + u.a2 * v.a4 + u.a3 * v.a3 + u.a4 * v.a2,
   u.a0 * v.a2 + u.a1 * v.a1 + u.a2 * v.a0 + u.a3 * v.a4 + u.a4 * v.a3,
   u.a0 * v.a3 + u.a1 * v.a2 + u.a2 * v.a1 + u.a3 * v.a0 + u.a4 * v.a4,
   u.a0 * v.a4 + u.a1 * v.a3 + u.a2 * v.a2 + u.a3 * v.a1 + u.a4 * v.a0⟩
def pow (u : R) : Nat → R
  | 0 => one
  | n + 1 => mul (pow u n) u

theorem mul_comm (u v : R) : mul u v = mul v u := by
  apply ext' <;> simp only [mul] <;> grind

theorem mul_assoc (u v w : R) : mul (mul u v) w = mul u (mul v w) := by
  apply ext' <;> simp only [mul] <;> grind

theorem mul_one_add (u y : R) : mul u (add one y) = add u (mul u y) := by
  apply ext' <;> simp only [mul, add, one] <;> grind

theorem smul_mul (c : Int) (u v : R) : mul (smul c u) v = smul c (mul u v) := by
  apply ext' <;> simp only [mul, smul] <;> grind

theorem mul_smul (c : Int) (u v : R) : mul u (smul c v) = smul c (mul u v) := by
  apply ext' <;> simp only [mul, smul] <;> grind

theorem smul_smul (c d : Int) (u : R) : smul c (smul d u) = smul (c * d) u := by
  apply ext' <;> simp only [smul] <;> grind

theorem pow_mul_distrib (u v : R) (n : Nat) : pow (mul u v) n = mul (pow u n) (pow v n) := by
  induction n with
  | zero => apply ext' <;> simp [pow, mul, one]
  | succ n ih =>
    simp only [pow]
    rw [ih, mul_assoc, ← mul_assoc (pow v n) u v, mul_comm (pow v n) u, mul_assoc u, ← mul_assoc]

theorem pow_smul (c : Int) (u : R) (n : Nat) : pow (smul c u) n = smul (c ^ n) (pow u n) := by
  induction n with
  | zero => apply ext' <;> simp [pow, smul, one]
  | succ n ih =>
    simp only [pow]
    rw [ih, smul_mul, mul_smul, smul_smul, Int.pow_succ]

/-- 성분별 합동 -/
def cg (p : Nat) (u v : R) : Prop :=
  (p : Int) ∣ u.a0 - v.a0 ∧ (p : Int) ∣ u.a1 - v.a1 ∧ (p : Int) ∣ u.a2 - v.a2 ∧
  (p : Int) ∣ u.a3 - v.a3 ∧ (p : Int) ∣ u.a4 - v.a4

theorem cg_refl (p : Nat) (u : R) : cg p u u := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem dsub_trans {d a b c : Int} (h1 : d ∣ a - b) (h2 : d ∣ b - c) : d ∣ a - c := by
  have := Int.dvd_add h1 h2; rwa [show a - b + (b - c) = a - c by omega] at this

theorem dsub_add {d a a' b b' : Int} (h1 : d ∣ a - a') (h2 : d ∣ b - b') : d ∣ (a + b) - (a' + b') := by
  have := Int.dvd_add h1 h2; rwa [show a - a' + (b - b') = a + b - (a' + b') by omega] at this

theorem dsub_mul {d a a' b b' : Int} (h1 : d ∣ a - a') (h2 : d ∣ b - b') : d ∣ a * b - a' * b' := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by grind
  rw [e]
  exact Int.dvd_add (Int.dvd_trans h1 (Int.dvd_mul_right _ _)) (Int.dvd_trans h2 (Int.dvd_mul_left _ _))

theorem cg_trans {p : Nat} {u v w : R} (h1 : cg p u v) (h2 : cg p v w) : cg p u w :=
  ⟨dsub_trans h1.1 h2.1, dsub_trans h1.2.1 h2.2.1, dsub_trans h1.2.2.1 h2.2.2.1,
   dsub_trans h1.2.2.2.1 h2.2.2.2.1, dsub_trans h1.2.2.2.2 h2.2.2.2.2⟩

theorem cg_mul {p : Nat} {u u' v v' : R} (hu : cg p u u') (hv : cg p v v') : cg p (mul u v) (mul u' v') := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hu
  obtain ⟨k0, k1, k2, k3, k4⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mul]
  · exact dsub_add (dsub_add (dsub_add (dsub_add (dsub_mul h0 k0) (dsub_mul h1 k4)) (dsub_mul h2 k3)) (dsub_mul h3 k2)) (dsub_mul h4 k1)
  · exact dsub_add (dsub_add (dsub_add (dsub_add (dsub_mul h0 k1) (dsub_mul h1 k0)) (dsub_mul h2 k4)) (dsub_mul h3 k3)) (dsub_mul h4 k2)
  · exact dsub_add (dsub_add (dsub_add (dsub_add (dsub_mul h0 k2) (dsub_mul h1 k1)) (dsub_mul h2 k0)) (dsub_mul h3 k4)) (dsub_mul h4 k3)
  · exact dsub_add (dsub_add (dsub_add (dsub_add (dsub_mul h0 k3) (dsub_mul h1 k2)) (dsub_mul h2 k1)) (dsub_mul h3 k0)) (dsub_mul h4 k4)
  · exact dsub_add (dsub_add (dsub_add (dsub_add (dsub_mul h0 k4) (dsub_mul h1 k3)) (dsub_mul h2 k2)) (dsub_mul h3 k1)) (dsub_mul h4 k0)

end R

open R

/-- 다섯 항 일차 결합의 합 -/
theorem sm_lin5 (n : Nat) (f0 f1 f2 f3 f4 : Nat → Int) (b0 b1 b2 b3 b4 : Int) :
    sm n (fun i => f0 i * b0 + f1 i * b1 + f2 i * b2 + f3 i * b3 + f4 i * b4)
      = sm n f0 * b0 + sm n f1 * b1 + sm n f2 * b2 + sm n f3 * b3 + sm n f4 * b4 := by
  induction n with
  | zero => simp [sm]
  | succ n ih => simp only [sm_succ]; rw [ih]; grind

theorem bt_lin5 (n : Nat) (f0 f1 f2 f3 f4 : Nat → Int) (b0 b1 b2 b3 b4 : Int) :
    bt (fun i => f0 i * b0 + f1 i * b1 + f2 i * b2 + f3 i * b3 + f4 i * b4) n
      = bt f0 n * b0 + bt f1 n * b1 + bt f2 n * b2 + bt f3 n * b3 + bt f4 n * b4 := by
  unfold bt
  rw [← sm_lin5]
  apply sm_congr
  intro i _
  grind

/-- R 안의 이항 정리 (성분별) : (1 + y)ⁿ = Σ C(n, k) yᵏ -/
theorem binomR (y : R) (n : Nat) :
    (pow (add one y) n).a0 = bt (fun k => (pow y k).a0) n ∧
    (pow (add one y) n).a1 = bt (fun k => (pow y k).a1) n ∧
    (pow (add one y) n).a2 = bt (fun k => (pow y k).a2) n ∧
    (pow (add one y) n).a3 = bt (fun k => (pow y k).a3) n ∧
    (pow (add one y) n).a4 = bt (fun k => (pow y k).a4) n := by
  induction n with
  | zero => simp [bt_zero, pow]
  | succ n ih =>
    obtain ⟨i0, i1, i2, i3, i4⟩ := ih
    have e : pow (add one y) (n + 1) = add (pow (add one y) n) (mul (pow (add one y) n) y) := by
      simp only [pow]; rw [mul_one_add]
    rw [e]
    generalize pow (add one y) n = P at i0 i1 i2 i3 i4 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [bt_succ, pow, mul, add] <;> rw [bt_lin5] <;>
      rw [i0, i1, i2, i3, i4]

/-- R 안의 신입생의 꿈 : (1 + y)^p ≡ 1 + y^p -/
theorem freshmanR {p : Nat} (hp : Prime p) (y : R) : R.cg p (pow (add one y) p) (add one (pow y p)) := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := binomR y p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [i0]; have := bt_prime hp (fun k => (pow y k).a0); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i1]; have := bt_prime hp (fun k => (pow y k).a1); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i2]; have := bt_prime hp (fun k => (pow y k).a2); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i3]; have := bt_prime hp (fun k => (pow y k).a3); simp only [add]; simpa [pow, one, Int.sub_sub] using this
  · rw [i4]; have := bt_prime hp (fun k => (pow y k).a4); simp only [add]; simpa [pow, one, Int.sub_sub] using this

/-- xᵏ 은 x^(k mod 5) -/
def basis : Nat → R
  | 0 => ⟨1, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 0, 1⟩

theorem pow_X (k : Nat) : pow X k = basis (k % 5) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow]
    rw [ih]
    have h : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases h with h | h | h | h | h
    · rw [h, show (k + 1) % 5 = 1 by omega]; decide
    · rw [h, show (k + 1) % 5 = 2 by omega]; decide
    · rw [h, show (k + 1) % 5 = 3 by omega]; decide
    · rw [h, show (k + 1) % 5 = 4 by omega]; decide
    · rw [h, show (k + 1) % 5 = 0 by omega]; decide

/-- 가우스 합 g = x − x² − x³ + x⁴ = x (1 − x)² (1 + x) -/
def gs : R := ⟨0, 1, -1, -1, 1⟩
def hm : R := add one (smul (-1) X)
def hp' : R := add one X

theorem gs_factor : gs = mul (mul (mul X hm) hm) hp' := by decide

/-- g³ = 5 g (그래서 g^(2j+1) = 5ʲ g) -/
theorem gs_pow_odd (j : Nat) : pow gs (2 * j + 1) = smul (5 ^ j) gs := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [e, show pow gs (2 * j + 1 + 1 + 1) = mul (mul (pow gs (2 * j + 1)) gs) gs from rfl, ih,
      smul_mul, smul_mul]
    have g3 : mul (mul gs gs) gs = smul 5 gs := by decide
    rw [g3, smul_smul, Int.pow_succ]

theorem neg_one_pow_odd (m : Nat) : (-1 : Int) ^ (2 * m + 1) = -1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by omega, Int.pow_succ, Int.pow_succ, ih]; decide

/-- 프로베니우스 : g^p ≡ g(x^p) (홀수 소수) -/
theorem gauss_frob {p m : Nat} (hp : Prime p) (hm2 : p = 2 * m + 1) :
    R.cg p (pow gs p)
      (mul (mul (mul (basis (p % 5)) (add one (smul (-1) (basis (p % 5)))))
        (add one (smul (-1) (basis (p % 5))))) (add one (basis (p % 5)))) := by
  rw [gs_factor, pow_mul_distrib, pow_mul_distrib, pow_mul_distrib, pow_X]
  have c1 : R.cg p (pow hm p) (add one (smul (-1) (basis (p % 5)))) := by
    have := freshmanR hp (smul (-1) X)
    rw [pow_smul, pow_X, hm2, neg_one_pow_odd, ← hm2] at this
    exact this
  have c2 : R.cg p (pow hp' p) (add one (basis (p % 5))) := by
    have := freshmanR hp X
    rw [pow_X] at this
    exact this
  exact R.cg_mul (R.cg_mul (R.cg_mul (R.cg_refl p _) c1) c1) c2

/-- E. 5 의 이차 상호 법칙 (오일러 꼴) : 모든 소수 p 에서
p ≡ ±1 (mod 5) 이면 5^((p−1)/2) ≡ 1 , p ≡ ±2 (mod 5) 이면 5^((p−1)/2) ≡ −1 (mod p) -/
theorem five_reciprocity {p : Nat} (hp : Prime p) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (p : Int) ∣ 5 ^ ((p - 1) / 2) - 1) ∧
    ((p % 5 = 2 ∨ p % 5 = 3) → (p : Int) ∣ 5 ^ ((p - 1) / 2) + 1) := by
  rcases prime_two_or_odd hp with h | ⟨m, h⟩
  · subst h; exact ⟨fun h => by omega, fun _ => ⟨1, by decide⟩⟩
  · have hmm : (p - 1) / 2 = m := by omega
    rw [hmm]
    have hf := gauss_frob hp h
    rw [h, gs_pow_odd, ← h] at hf
    have v : ∀ r, (r = 1 ∨ r = 4 → mul (mul (mul (basis r) (add one (smul (-1) (basis r))))
          (add one (smul (-1) (basis r)))) (add one (basis r)) = gs) ∧
        (r = 2 ∨ r = 3 → mul (mul (mul (basis r) (add one (smul (-1) (basis r))))
          (add one (smul (-1) (basis r)))) (add one (basis r)) = smul (-1) gs) := by
      intro r
      constructor
      · intro hr; rcases hr with hr | hr <;> subst hr <;> decide
      · intro hr; rcases hr with hr | hr <;> subst hr <;> decide
    constructor
    · intro hr
      rw [(v (p % 5)).1 hr] at hf
      have key := hf.2.1
      simpa [smul, gs] using key
    · intro hr
      rw [(v (p % 5)).2 hr] at hf
      have key := hf.2.1
      simp only [smul, gs] at key
      have : 5 ^ m * 1 - -1 * 1 = (5 : Int) ^ m + 1 := by omega
      rw [this] at key
      exact key

/-! ## 따름 : 뤼카의 네 줄 (모든 소수) -/

/-- Fₚ ≡ (p/5) (mod p) : p ≡ ±1 (mod 5) 이면 Fₚ ≡ 1 , p ≡ ±2 (mod 5) 이면 Fₚ ≡ −1 , 그리고 5 ∣ F₅ -/
theorem fib_prime_legendre {p : Nat} (hp : Prime p) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (p : Int) ∣ F p - 1) ∧
    ((p % 5 = 2 ∨ p % 5 = 3) → (p : Int) ∣ F p + 1) ∧
    (p = 5 → (p : Int) ∣ F p) := by
  have hD := fib_prime hp
  have hE := five_reciprocity hp
  refine ⟨fun hr => ?_, fun hr => ?_, fun h5 => ?_⟩
  · exact R.dsub_trans hD (hE.1 hr)
  · have := Int.dvd_add hD (hE.2 hr)
    rwa [show F p - 5 ^ ((p - 1) / 2) + (5 ^ ((p - 1) / 2) + 1) = F p + 1 by omega] at this
  · subst h5; exact ⟨1, by decide⟩

/-- p ∣ F_{p − (p/5)} : p ≡ ±1 (mod 5) 이면 p ∣ F (p − 1) , p ≡ ±2 (mod 5) 이면 p ∣ F (p + 1) -/
theorem fib_rank {p : Nat} (hp : Prime p) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (p : Int) ∣ F (p - 1)) ∧
    ((p % 5 = 2 ∨ p % 5 = 3) → (p : Int) ∣ F (p + 1)) := by
  have hL := lucas_prime hp
  have hF := fib_prime_legendre hp
  have hs : 2 * F (p + 1) = L p + F p := (step_both p).1
  constructor
  · intro hr
    have h1 := hF.1 hr
    rcases prime_two_or_odd hp with h | ⟨m, h⟩
    · omega
    · have hd : (p : Int) ∣ 2 * (F (p + 1) - 1) := by
        have := Int.dvd_add hL h1
        rwa [show L p - 1 + (F p - 1) = 2 * (F (p + 1) - 1) by omega] at this
      have hd' : (p : Int) ∣ F (p + 1) - 1 := by
        rw [h] at hd ⊢; exact dvd_of_dvd_two_mul hd
      have hrec : F (p - 1 + 2) = F (p - 1) + F (p - 1 + 1) := rfl
      rw [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at hrec
      have := Int.dvd_sub hd' h1
      rwa [show F (p + 1) - 1 - (F p - 1) = F (p - 1) by omega] at this
  · intro hr
    have h1 := hF.2.1 hr
    rcases prime_two_or_odd hp with h | ⟨m, h⟩
    · subst h; exact ⟨1, by decide⟩
    · have hd : (p : Int) ∣ 2 * F (p + 1) := by
        have := Int.dvd_add hL h1
        rwa [show L p - 1 + (F p + 1) = 2 * F (p + 1) by omega] at this
      rw [h] at hd ⊢; exact dvd_of_dvd_two_mul hd

end GoldenPrimeAll


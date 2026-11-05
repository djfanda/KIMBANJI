/-
함수체 바일 창 — 모든 N 에서 (린 4 코어만 · Mathlib 없음)

곡선 하나의 제타는 두 근 α · ᾱ (α + ᾱ = a · αᾱ = q) 로 정해진다. 창 N 의 바일 행렬
  M_N[m, n] = q^{min(m,n)} · V_{|m − n|}   (m, n = 0 … N,  V = 뤼카 수열 : α^k + ᾱ^k)
는 정의가 FFPrelude 와 글자 그대로 같다(그때는 N = 1 … 5 만 커널 셈으로 확인).

여기서는 모든 N 을 한 번에 닫는다.
  · X^m ≡ c_m + d_m X  (mod X² − aX + q) 의 두 수열 c · d 로 칸 하나를 적으면
      M[m, n] = 2 c_m c_n + a (c_m d_n + d_m c_n) + 2q d_m d_n        (weil_eq_G)
  · 그래서 모든 N 과 모든 정수 벡터 x 에서 이차 형식은
      Σ_{m,n ≤ N} x_m x_n M[m, n] = 2 (A² + aAB + qB²) ,  A = Σ x_m c_m , B = Σ x_m d_m   (QF_eq)
    이고 4(A² + aAB + qB²) = (2A + aB)² + (4q − a²) B² 이므로
      a² ≤ 4q  ⇔  모든 창 N 에서 모든 정수 벡터의 이차 형식 ≥ 0          (psd_iff)
    (정수 벡터로 시험한다 — 실수 벡터의 양의 준정부호와 같다는 것은 여기서 형식화하지 않았다)
  · M x = (2A + aB) c + (aA + 2qB) d — 열공간은 c · d 둘 (계수 ≤ 2)     (col)
  · 모든 3 × 3 소행렬식 = 0 · 크기 3 이상 모든 소행렬식 = 0 · 2 × 2 주소행렬식 = (4q − a²)(c_m d_n − d_m c_n)²
    → FFPrelude 의 주장 C(q, a) 를 모든 N ≥ 1 로 (claim_all)
-/
namespace Trombo.WeilAll

/-! ## 1. 정의 — FFPrelude 와 글자 그대로 같다 -/

def V (q a : Int) : Nat → Int
  | 0 => 2
  | 1 => a
  | n + 2 => a * V q a (n + 1) - q * V q a n

def U (q a : Int) : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => a * U q a (n + 1) - q * U q a n

def dist (m n : Nat) : Nat := if m ≤ n then n - m else m - n

def weil (q a : Int) (m n : Nat) : Int := q ^ (min m n) * V q a (dist m n)

def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, j + 1 => nth xs j

def dropAt : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, j + 1 => x :: dropAt xs j

def sgn (j : Nat) : Int := if j % 2 = 0 then 1 else -1

def det (M : Nat → Nat → Int) : List Nat → List Nat → Int
  | [], _ => 1
  | r :: rs, C => (List.range C.length).foldl
      (fun acc j => acc + sgn j * M r (nth C j) * det M rs (dropAt C j)) 0

def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

def idx (N : Nat) : List Nat := List.range (N + 1)

def principal (N : Nat) : List (List Nat) := (List.range (N + 1)).flatMap fun k => choose (k + 1) (idx N)

theorem V_two (q a : Int) (n : Nat) : V q a (n + 2) = a * V q a (n + 1) - q * V q a n := rfl
theorem U_two (q a : Int) (n : Nat) : U q a (n + 2) = a * U q a (n + 1) - q * U q a n := rfl

/-! ## 2. X^m ≡ c_m + d_m X (mod X² − aX + q) -/

def cd (q a : Int) : Nat → Int × Int
  | 0 => (1, 0)
  | m + 1 => (-q * (cd q a m).2, (cd q a m).1 + a * (cd q a m).2)

def c (q a : Int) (m : Nat) : Int := (cd q a m).1
def d (q a : Int) (m : Nat) : Int := (cd q a m).2

theorem c_zero (q a : Int) : c q a 0 = 1 := rfl
theorem d_zero (q a : Int) : d q a 0 = 0 := rfl
theorem c_succ (q a : Int) (m : Nat) : c q a (m + 1) = -q * d q a m := rfl
theorem d_succ (q a : Int) (m : Nat) : d q a (m + 1) = c q a m + a * d q a m := rfl

/-- d 는 뤼카 수열 U -/
theorem d_eq_U (q a : Int) (m : Nat) : d q a m = U q a m ∧ d q a (m + 1) = U q a (m + 1) := by
  induction m with
  | zero => exact ⟨rfl, by simp [d_succ, c_zero, d_zero, U]⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [d_succ, c_succ, U_two, ← ih.1, ← ih.2, d_succ]
    grind

/-- 트레이스 : V_k = α^k + ᾱ^k = 2 c_k + a d_k -/
theorem V_eq_cd (q a : Int) (k : Nat) :
    V q a k = 2 * c q a k + a * d q a k ∧ V q a (k + 1) = 2 * c q a (k + 1) + a * d q a (k + 1) := by
  induction k with
  | zero => exact ⟨by simp [V, c_zero, d_zero], by simp [V, c_succ, d_succ, c_zero, d_zero]⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [V_two, ih.1, ih.2, c_succ q a (k + 1), d_succ q a (k + 1), c_succ q a k, d_succ q a k]
    grind

/-! ## 3. 칸 하나 = 2 c_m c_n + a (c_m d_n + d_m c_n) + 2q d_m d_n -/

def G (q a : Int) (m n : Nat) : Int :=
  2 * c q a m * c q a n + a * (c q a m * d q a n + d q a m * c q a n) + 2 * q * d q a m * d q a n

theorem G_symm (q a : Int) (m n : Nat) : G q a m n = G q a n m := by
  simp only [G]; grind

theorem G_zero (q a : Int) (k : Nat) : G q a 0 k = V q a k := by
  rw [(V_eq_cd q a k).1]; simp only [G, c_zero, d_zero]; grind

theorem G_succ (q a : Int) (m n : Nat) : G q a (m + 1) (n + 1) = q * G q a m n := by
  simp only [G, c_succ, d_succ]; grind

theorem G_shift (q a : Int) (m k : Nat) : G q a m (m + k) = q ^ m * V q a k := by
  induction m with
  | zero => rw [Nat.zero_add, G_zero, Int.pow_zero, Int.one_mul]
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega, G_succ, ih, Int.pow_succ]
    grind

/-- 바일 창의 모든 칸 -/
theorem weil_eq_G (q a : Int) (m n : Nat) : weil q a m n = G q a m n := by
  unfold weil dist
  split
  · next h =>
    rw [Nat.min_eq_left h]
    have e := G_shift q a m (n - m)
    rw [show m + (n - m) = n by omega] at e
    exact e.symm
  · next h =>
    rw [Nat.min_eq_right (by omega), G_symm]
    have e := G_shift q a n (m - n)
    rw [show n + (m - n) = m by omega] at e
    exact e.symm

/-! ## 4. 합과 이차 형식 — 모든 N -/

/-- Σ_{i < n} f i -/
def sm : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sm n f + f n

theorem sm_lin (N : Nat) (k1 k2 : Int) (f g : Nat → Int) :
    sm N (fun m => k1 * f m + k2 * g m) = k1 * sm N f + k2 * sm N g := by
  induction N with
  | zero => simp [sm]
  | succ N ih => simp only [sm]; rw [ih]; grind

/-- 행렬 곱 M x 의 m 째 칸 — 창의 크기와 상관없이 c_m · d_m 의 결합 (열공간 = c · d 둘) -/
theorem col (q a : Int) (x : Nat → Int) (N m : Nat) :
    sm N (fun n => weil q a m n * x n) =
      (2 * sm N (fun n => x n * c q a n) + a * sm N (fun n => x n * d q a n)) * c q a m +
      (a * sm N (fun n => x n * c q a n) + 2 * q * sm N (fun n => x n * d q a n)) * d q a m := by
  induction N with
  | zero => simp [sm]
  | succ N ih =>
    simp only [sm]
    rw [ih, weil_eq_G]
    simp only [G]
    grind

/-- 창 N (첨자 0 … N) 의 이차 형식 Σ_{m,n ≤ N} x_m x_n M[m, n] -/
def QF (q a : Int) (x : Nat → Int) (N : Nat) : Int :=
  sm (N + 1) (fun m => x m * sm (N + 1) (fun n => weil q a m n * x n))

/-- 이차 형식은 두 수 A · B 로 닫힌다 -/
theorem QF_eq (q a : Int) (x : Nat → Int) (N : Nat) :
    QF q a x N = 2 * ((sm (N + 1) fun n => x n * c q a n) ^ 2
      + a * (sm (N + 1) fun n => x n * c q a n) * (sm (N + 1) fun n => x n * d q a n)
      + q * (sm (N + 1) fun n => x n * d q a n) ^ 2) := by
  unfold QF
  generalize hA : sm (N + 1) (fun n => x n * c q a n) = A
  generalize hB : sm (N + 1) (fun n => x n * d q a n) = B
  have h1 : ∀ m, x m * sm (N + 1) (fun n => weil q a m n * x n) =
      (2 * A + a * B) * (x m * c q a m) + (a * A + 2 * q * B) * (x m * d q a m) := by
    intro m
    rw [col, hA, hB]
    grind
  rw [show (fun m => x m * sm (N + 1) (fun n => weil q a m n * x n)) =
      (fun m => (2 * A + a * B) * (x m * c q a m) + (a * A + 2 * q * B) * (x m * d q a m)) from funext h1]
  rw [sm_lin, hA, hB]
  grind

/-- a² ≤ 4q 이면 모든 창 N 이 양의 준정부호 -/
theorem psd_all (q a : Int) (h : a ^ 2 ≤ 4 * q) (x : Nat → Int) (N : Nat) : 0 ≤ QF q a x N := by
  rw [QF_eq]
  generalize sm (N + 1) (fun n => x n * c q a n) = A
  generalize sm (N + 1) (fun n => x n * d q a n) = B
  have e : 4 * (A ^ 2 + a * A * B + q * B ^ 2) = (2 * A + a * B) ^ 2 + (4 * q - a ^ 2) * B ^ 2 := by grind
  have h1 : 0 ≤ (2 * A + a * B) ^ 2 := Int.sq_nonneg _
  have h2 : 0 ≤ (4 * q - a ^ 2) * B ^ 2 := Int.mul_nonneg (by omega) (Int.sq_nonneg _)
  omega

/-- 거꾸로 : 창 1 하나만 양의 준정부호여도 a² ≤ 4q — 벡터 x = (a, −2) 에서 이차 형식 = 2 (4q − a²) -/
theorem QF_witness (q a : Int) : QF q a (fun i => if i = 0 then a else if i = 1 then -2 else 0) 1 = 2 * (4 * q - a ^ 2) := by
  rw [QF_eq]
  simp [sm, c, d, cd]
  grind

theorem psd_converse (q a : Int) (h : ∀ x : Nat → Int, 0 ≤ QF q a x 1) : a ^ 2 ≤ 4 * q := by
  have h1 := h (fun i => if i = 0 then a else if i = 1 then -2 else 0)
  rw [QF_witness] at h1
  omega

/-- 바일 판정 (함수체 · 곡선 하나) : 모든 창 N 에서 모든 정수 벡터의 이차 형식 ≥ 0 ⇔ a² ≤ 4q
    (해석 : 곧 두 근 α · ᾱ 의 크기가 √q — 이 동치는 여기서 형식화하지 않았다) -/
theorem psd_iff (q a : Int) : (∀ N : Nat, ∀ x : Nat → Int, 0 ≤ QF q a x N) ↔ a ^ 2 ≤ 4 * q :=
  ⟨fun h => psd_converse q a (h 1), fun h N x => psd_all q a h x N⟩

/-! ## 5. 소행렬식 — 크기 3 이상은 모두 0, 크기 2 의 주소행렬식은 (4q − a²) × 제곱 -/

theorem det_nil (M : Nat → Nat → Int) (C : List Nat) : det M [] C = 1 := rfl

/-- 1 × 1 -/
theorem det_one (M : Nat → Nat → Int) (r c0 : Nat) : det M [r] [c0] = M r c0 := by
  simp [det, List.range, List.range.loop, List.foldl, nth, sgn]

/-- 2 × 2 -/
theorem det_two (M : Nat → Nat → Int) (r0 r1 c0 c1 : Nat) :
    det M [r0, r1] [c0, c1] = M r0 c0 * M r1 c1 - M r0 c1 * M r1 c0 := by
  simp [det, List.range, List.range.loop, List.foldl, nth, dropAt, sgn]
  grind

/-- 3 × 3 -/
theorem det_three (M : Nat → Nat → Int) (r0 r1 r2 c0 c1 c2 : Nat) :
    det M [r0, r1, r2] [c0, c1, c2] =
      M r0 c0 * (M r1 c1 * M r2 c2 - M r1 c2 * M r2 c1)
      - M r0 c1 * (M r1 c0 * M r2 c2 - M r1 c2 * M r2 c0)
      + M r0 c2 * (M r1 c0 * M r2 c1 - M r1 c1 * M r2 c0) := by
  simp [det, List.range, List.range.loop, List.foldl, nth, dropAt, sgn]
  grind

/-- 모든 3 × 3 소행렬식은 0 (어느 행 셋 · 어느 열 셋이든) -/
theorem minor3_zero (q a : Int) (r0 r1 r2 c0 c1 c2 : Nat) :
    det (weil q a) [r0, r1, r2] [c0, c1, c2] = 0 := by
  rw [det_three]
  simp only [weil_eq_G, G]
  grind

/-- 2 × 2 주소행렬식 = (4q − a²)(c_m d_n − d_m c_n)² -/
theorem minor2_principal (q a : Int) (m n : Nat) :
    det (weil q a) [m, n] [m, n] = (4 * q - a ^ 2) * (c q a m * d q a n - d q a m * c q a n) ^ 2 := by
  rw [det_two]
  simp only [weil_eq_G, G]
  grind

/-- 모든 2 × 2 소행렬식 = (4q − a²)(c_{r0} d_{r1} − d_{r0} c_{r1})(c_{c0} d_{c1} − d_{c0} c_{c1}) -/
theorem minor2 (q a : Int) (r0 r1 c0 c1 : Nat) :
    det (weil q a) [r0, r1] [c0, c1] = (4 * q - a ^ 2) * (c q a r0 * d q a r1 - d q a r0 * c q a r1) *
      (c q a c0 * d q a c1 - d q a c0 * c q a c1) := by
  rw [det_two]
  simp only [weil_eq_G, G]
  grind

/-- 1 × 1 : 2 q^m -/
theorem minor1 (q a : Int) (m : Nat) : det (weil q a) [m] [m] = 2 * q ^ m := by
  rw [det_one]; simp [weil, dist, V]; grind

/-! ### 크기 3 이상 -/

theorem foldl_zero (n : Nat) (f : Nat → Int) (h : ∀ j, j < n → f j = 0) :
    (List.range n).foldl (fun acc j => acc + f j) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (fun j hj => h j (by omega))]
    simp [h n (by omega)]

theorem dropAt_length (l : List Nat) (j : Nat) (h : j < l.length) : (dropAt l j).length = l.length - 1 := by
  induction l generalizing j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero => simp [dropAt]
    | succ j =>
      simp only [dropAt, List.length_cons]
      simp only [List.length_cons] at h
      rw [ih j (by omega)]
      omega

/-- 크기 j + 3 의 모든 소행렬식은 0 -/
theorem minor_big_zero' (q a : Int) : ∀ j : Nat, ∀ R C : List Nat, R.length = j + 3 → C.length = j + 3 →
    det (weil q a) R C = 0 := by
  intro j
  induction j with
  | zero =>
    intro R C hR hC
    match R, C, hR, hC with
    | [r0, r1, r2], [c0, c1, c2], _, _ => exact minor3_zero q a r0 r1 r2 c0 c1 c2
  | succ j ih =>
    intro R C hR hC
    match R, hR with
    | r :: rs, hR =>
      simp only [List.length_cons] at hR
      simp only [det]
      apply foldl_zero
      intro k hk
      rw [ih rs (dropAt C k) (by omega) (by rw [dropAt_length C k hk]; omega)]
      grind

/-- 크기 k ≥ 3 의 모든 소행렬식은 0 -/
theorem minor_big_zero (q a : Int) (k : Nat) (hk : 3 ≤ k) (R C : List Nat) (hR : R.length = k) (hC : C.length = k) :
    det (weil q a) R C = 0 :=
  minor_big_zero' q a (k - 3) R C (by omega) (by omega)

/-! ## 6. 주장 C(q, a) 를 모든 N 으로 -/

theorem choose_length : ∀ (k : Nat) (l L : List Nat), L ∈ choose k l → L.length = k := by
  intro k l
  induction l generalizing k with
  | nil =>
    intro L hL
    cases k with
    | zero => simp [choose] at hL; simp [hL]
    | succ k => simp [choose] at hL
  | cons x xs ih =>
    intro L hL
    cases k with
    | zero => simp [choose] at hL; simp [hL]
    | succ k =>
      simp only [choose, List.mem_append, List.mem_map] at hL
      rcases hL with ⟨L', hL', rfl⟩ | hL
      · simp [ih k L' hL']
      · exact ih (k + 1) L hL

theorem principal_length (N : Nat) (S : List Nat) (h : S ∈ principal N) : 1 ≤ S.length := by
  simp only [principal, List.mem_flatMap] at h
  obtain ⟨k, _, hk⟩ := h
  rw [choose_length (k + 1) (idx N) S hk]
  omega

/-- 모든 주소행렬식 ≥ 0 (모든 N) — 크기 1 은 2q^m, 크기 2 는 (4q − a²) × 제곱, 크기 3 이상은 0 -/
theorem principal_nonneg (q a : Int) (hq : 0 ≤ q) (h : a ^ 2 ≤ 4 * q) (S : List Nat) (hS : 1 ≤ S.length) :
    0 ≤ det (weil q a) S S := by
  match S, hS with
  | [m], _ => rw [minor1]; exact Int.mul_nonneg (by omega) (Int.pow_nonneg hq)
  | [m, n], _ => rw [minor2_principal]; exact Int.mul_nonneg (by omega) (Int.sq_nonneg _)
  | r0 :: r1 :: r2 :: rs, _ =>
    rw [minor_big_zero q a (rs.length + 3) (by omega) _ _ (by simp) (by simp)]
    exact Int.le_refl 0

theorem idx_eq (N : Nat) (h : 1 ≤ N) : ∃ t, idx N = 0 :: 1 :: t := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  refine ⟨(List.range M).map (fun i => i + 2), ?_⟩
  simp only [idx]
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]

theorem zero_one_mem (N : Nat) (h : 1 ≤ N) : [0, 1] ∈ choose 2 (idx N) := by
  obtain ⟨t, ht⟩ := idx_eq N h
  rw [ht]
  simp [choose]

theorem idx_length (N : Nat) : (idx N).length = N + 1 := by simp [idx]

/-- 창 1 의 행렬식은 4q − a² -/
theorem window1_det (q a : Int) : det (weil q a) [0, 1] [0, 1] = 4 * q - a ^ 2 := by
  rw [det_two]; simp [weil, dist, V]; grind

/-- FFPrelude 의 주장 C(q, a) 를 N = 1 … 5 에서 모든 N ≥ 1 로 :
  (i) 창 N 의 모든 주소행렬식 ≥ 0  (ii) 창 1 행렬식 = 4q − a² > 0
  (iii) N ≥ 2 : 모든 3 × 3 소행렬식 = 0 · 2 × 2 주소행렬식 하나 > 0 (계수 정확히 2) · 행렬식 = 0 -/
theorem claim_all (q a : Int) (hq : 0 ≤ q) (h : a ^ 2 < 4 * q) (N : Nat) (hN : 1 ≤ N) :
    (∀ S ∈ principal N, 0 ≤ det (weil q a) S S) ∧
    det (weil q a) [0, 1] [0, 1] = 4 * q - a ^ 2 ∧ 0 < det (weil q a) [0, 1] [0, 1] ∧
    (2 ≤ N →
      (∀ R ∈ choose 3 (idx N), ∀ C ∈ choose 3 (idx N), det (weil q a) R C = 0) ∧
      (∃ S ∈ choose 2 (idx N), 0 < det (weil q a) S S) ∧
      det (weil q a) (idx N) (idx N) = 0) := by
  refine ⟨fun S hS => principal_nonneg q a hq (by omega) S (principal_length N S hS),
    window1_det q a, by rw [window1_det]; omega, fun h2 => ⟨?_, ?_, ?_⟩⟩
  · intro R hR C hC
    exact minor_big_zero q a 3 (Nat.le_refl 3) R C (choose_length 3 _ R hR) (choose_length 3 _ C hC)
  · exact ⟨[0, 1], zero_one_mem N hN, by rw [window1_det]; omega⟩
  · exact minor_big_zero q a (N + 1) (by omega) _ _ (idx_length N) (idx_length N)

/-- FFPrelude 의 주장 C(q, a) — 글자 그대로 (그때는 (q, a) 열두 쌍을 커널 셈으로 하나씩) -/
def Claim (q a : Int) : Prop :=
  (∀ N ∈ [1, 2, 3, 4, 5], ∀ S ∈ principal N, 0 ≤ det (weil q a) S S) ∧
  det (weil q a) [0, 1] [0, 1] = 4 * q - a ^ 2 ∧ 0 < det (weil q a) [0, 1] [0, 1] ∧
  (∀ N ∈ [2, 3, 4, 5],
    (∀ R ∈ choose 3 (idx N), ∀ C ∈ choose 3 (idx N), det (weil q a) R C = 0) ∧
    (∃ S ∈ choose 2 (idx N), 0 < det (weil q a) S S) ∧
    det (weil q a) (idx N) (idx N) = 0)

/-- 그 주장은 q ≥ 0 · a² < 4q 인 모든 정수 쌍에서 참 — 열두 쌍의 커널 셈이 한 정리로 -/
theorem claim_general (q a : Int) (h : a ^ 2 < 4 * q) : Claim q a := by
  have hq : 0 ≤ q := by have := Int.sq_nonneg a; omega
  refine ⟨fun N hN S hS => ?_, window1_det q a, by rw [window1_det]; omega, fun N hN => ?_⟩
  · have h1 : 1 ≤ N := by simp at hN; omega
    exact (claim_all q a hq h N h1).1 S hS
  · have h2 : 2 ≤ N := by simp at hN; omega
    exact (claim_all q a hq h N (by omega)).2.2.2 h2

/-! ## 7. 보기 — F₂ · F₃ 의 모든 곡선 (하세 안의 모든 트레이스) -/

theorem claim_all_q2 (a : Int) (ha : a ∈ ([-2, -1, 0, 1, 2] : List Int)) (N : Nat) (hN : 1 ≤ N) :
    (∀ S ∈ principal N, 0 ≤ det (weil 2 a) S S) ∧ 0 < det (weil 2 a) [0, 1] [0, 1] := by
  have h : a ^ 2 < 4 * 2 := by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨(claim_all 2 a (by decide) h N hN).1, (claim_all 2 a (by decide) h N hN).2.2.1⟩

theorem claim_all_q3 (a : Int) (ha : a ∈ ([-3, -2, -1, 0, 1, 2, 3] : List Int)) (N : Nat) (hN : 1 ≤ N) :
    (∀ S ∈ principal N, 0 ≤ det (weil 3 a) S S) ∧ 0 < det (weil 3 a) [0, 1] [0, 1] := by
  have h : a ^ 2 < 4 * 3 := by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨(claim_all 3 a (by decide) h N hN).1, (claim_all 3 a (by decide) h N hN).2.2.1⟩

/-- 경계 a² = 4q 에서 2 × 2 주소행렬식은 모두 0 -/
theorem boundary_rank_one (q a : Int) (h : a ^ 2 = 4 * q) (m n : Nat) : det (weil q a) [m, n] [m, n] = 0 := by
  rw [minor2_principal, show 4 * q - a ^ 2 = 0 by omega, Int.zero_mul]

/-- 경계 a² = 4q (예 q = 4, a = 4) : 모든 창이 양의 준정부호이고, 모든 2 × 2 소행렬식이 0 이며 M[0, 0] = 2 — 계수 정확히 1 -/
theorem boundary (q a : Int) (h : a ^ 2 = 4 * q) :
    (∀ N : Nat, ∀ x : Nat → Int, 0 ≤ QF q a x N) ∧
    (∀ r0 r1 c0 c1 : Nat, det (weil q a) [r0, r1] [c0, c1] = 0) ∧ weil q a 0 0 = 2 := by
  refine ⟨fun N x => psd_all q a (by omega) x N, fun r0 r1 c0 c1 => ?_, by simp [weil, dist, V]⟩
  rw [minor2, show 4 * q - a ^ 2 = 0 by omega]; simp

end Trombo.WeilAll

#print axioms Trombo.WeilAll.weil_eq_G
#print axioms Trombo.WeilAll.col
#print axioms Trombo.WeilAll.QF_eq
#print axioms Trombo.WeilAll.psd_all
#print axioms Trombo.WeilAll.psd_iff
#print axioms Trombo.WeilAll.minor3_zero
#print axioms Trombo.WeilAll.minor2_principal
#print axioms Trombo.WeilAll.minor_big_zero
#print axioms Trombo.WeilAll.principal_nonneg
#print axioms Trombo.WeilAll.claim_all
#print axioms Trombo.WeilAll.claim_general
#print axioms Trombo.WeilAll.claim_all_q2
#print axioms Trombo.WeilAll.claim_all_q3
#print axioms Trombo.WeilAll.boundary_rank_one
#print axioms Trombo.WeilAll.minor2
#print axioms Trombo.WeilAll.boundary

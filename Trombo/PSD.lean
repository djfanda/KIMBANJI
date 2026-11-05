/-!
# 양정치 (Positive-Semidefiniteness) Certificate Checker

정확한 정수 인증서로 이차 꼴의 양(반)정치를 판정하는 검사기와 그 건전성 정리 —
바일 꼴 창 인증서로 가는 첫 걸음 · 검사기는 셈만, 옳음은 정리(■)

* 행렬 `A`, 벡터 `x`, 인증서 행 `ℓ_r` 은 모두 `Nat` 첨자 함수로 읽고,
  합은 `sum n f = f 0 + … + f (n-1)` 로 명시적으로 센다.
* 인증서: 척도 `c > 0`, 무게 `d_r ≥ 0`, 행 `ℓ_r` 로
  `c · A_{ij} = Σ_r d_r ℓ_r(i) ℓ_r(j)` (모든 `i, j < n`).
* 검사기 `check` 는 정수 셈만 한다. 옳음은 정리 `sound` 가 맡는다:
  `check C = true → ∀ x, 0 ≤ xᵀ A x`.
* 엄격판 `checkStrict` (행 `ℓ_r` 이 `i ≤ r` 에만 받침, `ℓ_r(r) ≠ 0`, `d_r > 0`) 은
  `sound_strict` : `x ≠ 0 → 0 < xᵀ A x`.

Core Lean 4 only: no imports, no `sorry`, no `native_decide`, no `axiom`.
-/

namespace PSD

/-! ## 1. 유한 합 -/

/-- `sum n f = f 0 + f 1 + … + f (n-1)` -/
def sum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sum n f + f n

@[simp] theorem sum_zero (f : Nat → Int) : sum 0 f = 0 := rfl
@[simp] theorem sum_succ (n : Nat) (f : Nat → Int) : sum (n + 1) f = sum n f + f n := rfl

theorem sum_congr {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k = g k) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum_succ]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem sum_add (n : Nat) (f g : Nat → Int) :
    sum n (fun k => f k + g k) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum_succ, ih]; omega

theorem mul_sum (n : Nat) (a : Int) (f : Nat → Int) :
    a * sum n f = sum n (fun k => a * f k) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_succ, ← ih, Int.mul_add]

theorem sum_mul (n : Nat) (a : Int) (f : Nat → Int) :
    sum n f * a = sum n (fun k => f k * a) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_succ, ← ih, Int.add_mul]

theorem sum_comm (n m : Nat) (f : Nat → Nat → Int) :
    sum n (fun i => sum m (fun j => f i j)) = sum m (fun j => sum n (fun i => f i j)) := by
  induction n with
  | zero =>
    simp only [sum_zero]
    induction m with
    | zero => rfl
    | succ m ih => simp only [sum_succ, ← ih]; omega
  | succ n ih =>
    simp only [sum_succ, ih]
    exact (sum_add m (fun j => sum n (fun i => f i j)) (fun j => f n j)).symm

theorem sum_nonneg {n : Nat} {f : Nat → Int} (h : ∀ k, k < n → 0 ≤ f k) : 0 ≤ sum n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_succ]
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h n (Nat.lt_succ_self n)
    omega

theorem sum_eq_zero_of_nonneg {n : Nat} {f : Nat → Int} (h : ∀ k, k < n → 0 ≤ f k)
    (hs : sum n f = 0) : ∀ k, k < n → f k = 0 := by
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    simp only [sum_succ] at hs
    have h1 := sum_nonneg (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h n (Nat.lt_succ_self n)
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk)) (by omega) k hk
    · subst hk; omega

theorem sum_eq_zero {n : Nat} {f : Nat → Int} (h : ∀ k, k < n → f k = 0) : sum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum_succ]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]
    rfl

/-- 한 자리만 남는 합. -/
theorem sum_single {n r : Nat} {f : Nat → Int} (hr : r < n)
    (h : ∀ k, k < n → k ≠ r → f k = 0) : sum n f = f r := by
  induction n with
  | zero => exact absurd hr (Nat.not_lt_zero r)
  | succ n ih =>
    simp only [sum_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | hr'
    · rw [ih hr' (fun k hk hkr => h k (Nat.lt_succ_of_lt hk) hkr),
          h n (Nat.lt_succ_self n) (by omega)]
      omega
    · subst hr'
      rw [sum_eq_zero (fun k hk => h k (Nat.lt_succ_of_lt hk) (by omega))]
      omega

theorem sum_mul_sum (n : Nat) (f g : Nat → Int) :
    sum n f * sum n g = sum n (fun i => sum n (fun j => f i * g j)) := by
  rw [sum_mul]
  apply sum_congr
  intro i _
  rw [mul_sum]

/-! ## 2. 이차 꼴과 일차 꼴 -/

/-- `xᵀ A x = Σ_i Σ_j x_i A_{ij} x_j` -/
def quad (n : Nat) (A : Nat → Nat → Int) (x : Nat → Int) : Int :=
  sum n (fun i => sum n (fun j => x i * A i j * x j))

/-- `ℓ · x = Σ_i ℓ_i x_i` -/
def lin (n : Nat) (ℓ : Nat → Int) (x : Nat → Int) : Int :=
  sum n (fun i => ℓ i * x i)

theorem square_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have : 0 ≤ -a := by omega
    have := Int.mul_nonneg this this
    rwa [Int.neg_mul_neg] at this

/-- 핵심 항등식: 인증서 등식이 성립하면 `c · xᵀAx = Σ_r d_r (ℓ_r·x)²`. -/
theorem key_identity (n m : Nat) (c : Int) (A : Nat → Nat → Int) (d : Nat → Int)
    (L : Nat → Nat → Int)
    (hEq : ∀ i, i < n → ∀ j, j < n → c * A i j = sum m (fun r => d r * L r i * L r j))
    (x : Nat → Int) :
    c * quad n A x = sum m (fun r => d r * (lin n (L r) x * lin n (L r) x)) := by
  unfold quad
  -- 왼쪽: c 를 안으로, 인증서 등식 대입, 합 순서 교환
  have step1 : c * sum n (fun i => sum n (fun j => x i * A i j * x j))
      = sum n (fun i => sum n (fun j => sum m (fun r => x i * (d r * L r i * L r j) * x j))) := by
    rw [mul_sum]
    apply sum_congr; intro i hi
    rw [mul_sum]
    apply sum_congr; intro j hj
    have e : c * (x i * A i j * x j) = x i * (c * A i j) * x j := by grind
    rw [e, hEq i hi j hj, mul_sum, sum_mul]
  rw [step1]
  have step2 : sum n (fun i => sum n (fun j => sum m (fun r => x i * (d r * L r i * L r j) * x j)))
      = sum n (fun i => sum m (fun r => sum n (fun j => x i * (d r * L r i * L r j) * x j))) := by
    apply sum_congr; intro i _
    exact sum_comm n m (fun j r => x i * (d r * L r i * L r j) * x j)
  rw [step2, sum_comm n m (fun i r => sum n (fun j => x i * (d r * L r i * L r j) * x j))]
  apply sum_congr; intro r _
  unfold lin
  rw [sum_mul_sum, mul_sum]
  apply sum_congr; intro i _
  rw [mul_sum]
  apply sum_congr; intro j _
  grind

/-- 함수 수준 건전성: 인증서 조건 ⇒ 양반정치. -/
theorem psd_of_cert (n m : Nat) (c : Int) (A : Nat → Nat → Int) (d : Nat → Int)
    (L : Nat → Nat → Int) (hc : 0 < c) (hd : ∀ r, r < m → 0 ≤ d r)
    (hEq : ∀ i, i < n → ∀ j, j < n → c * A i j = sum m (fun r => d r * L r i * L r j))
    (x : Nat → Int) : 0 ≤ quad n A x := by
  have hk := key_identity n m c A d L hEq x
  have hnn : 0 ≤ c * quad n A x := by
    rw [hk]
    exact sum_nonneg (fun r hr => Int.mul_nonneg (hd r hr) (square_nonneg _))
  rcases Int.lt_or_le (quad n A x) 0 with h3 | h3
  · have := Int.mul_neg_of_pos_of_neg hc h3; omega
  · exact h3

/-- 함수 수준 엄격판: 행 `ℓ_r` 이 `i ≤ r` 에만 받침, `ℓ_r(r) ≠ 0`, `d_r > 0`, 행 수 `= n`
⇒ `x ≠ 0` 이면 `0 < xᵀAx`. -/
theorem pd_of_cert (n : Nat) (c : Int) (A : Nat → Nat → Int) (d : Nat → Int)
    (L : Nat → Nat → Int) (hc : 0 < c) (hd : ∀ r, r < n → 0 < d r)
    (hdiag : ∀ r, r < n → L r r ≠ 0)
    (htri : ∀ r, r < n → ∀ i, i < n → r < i → L r i = 0)
    (hEq : ∀ i, i < n → ∀ j, j < n → c * A i j = sum n (fun r => d r * L r i * L r j))
    (x : Nat → Int) (hx : ∃ k, k < n ∧ x k ≠ 0) : 0 < quad n A x := by
  have h0 := psd_of_cert n n c A d L hc (fun r hr => Int.le_of_lt (hd r hr)) hEq x
  rcases Int.lt_or_le 0 (quad n A x) with h | h
  · exact h
  · exfalso
    have hq : quad n A x = 0 := by omega
    have hk := key_identity n n c A d L hEq x
    rw [hq, Int.mul_zero] at hk
    have hterm := sum_eq_zero_of_nonneg
      (fun r hr => Int.mul_nonneg (Int.le_of_lt (hd r hr)) (square_nonneg (lin n (L r) x)))
      hk.symm
    -- 각 행에서 ℓ_r · x = 0
    have hlin : ∀ r, r < n → lin n (L r) x = 0 := by
      intro r hr
      have e := hterm r hr
      rcases Int.mul_eq_zero.mp e with e | e
      · have := hd r hr; omega
      · rcases Int.mul_eq_zero.mp e with e | e <;> exact e
    -- 삼각 구조로 x_0 = x_1 = … = 0
    have hall : ∀ r, ∀ k, k < r → k < n → x k = 0 := by
      intro r
      induction r with
      | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
      | succ r ih =>
        intro k hk hkn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact ih k hk hkn
        · subst hk
          have hl := hlin k hkn
          unfold lin at hl
          rw [sum_single hkn (fun i hi hik => by
                rcases Nat.lt_or_gt_of_ne hik with h1 | h1
                · rw [ih i h1 hi, Int.mul_zero]
                · rw [htri k hkn i hi h1, Int.zero_mul])] at hl
          rcases Int.mul_eq_zero.mp hl with e | e
          · exact absurd e (hdiag k hkn)
          · exact e
    obtain ⟨k, hkn, hxk⟩ := hx
    exact hxk (hall (k + 1) k (Nat.lt_succ_self k) hkn)

/-! ## 3. 인증서 자료와 검사기 (셈만) -/

/-- 정수 인증서: 행렬 `A` (n×n), 척도 `c`, 행 목록 `(d_r, ℓ_r)`. -/
structure Cert where
  n : Nat
  A : List (List Int)
  c : Int
  rows : List (Int × List Int)

namespace Cert

/-- `A_{ij}` (범위 밖은 0) -/
def mat (C : Cert) (i j : Nat) : Int := (C.A.getD i []).getD j 0
/-- 행 수 `m` -/
def m (C : Cert) : Nat := C.rows.length
/-- 무게 `d_r` -/
def d (C : Cert) (r : Nat) : Int := (C.rows.getD r (0, [])).1
/-- 행 `ℓ_r(i)` -/
def L (C : Cert) (r i : Nat) : Int := (C.rows.getD r (0, [])).2.getD i 0

end Cert

/-- `allBelow n p = true ↔ ∀ k < n, p k = true` -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) :
    ∀ k, k < n → p k = true := by
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih h.1 k hk
    · subst hk; exact h.2

/-- 검사기: `c > 0`, 모든 `d_r ≥ 0`, 그리고 정확한 정수 등식 `c·A = Σ d_r ℓ_r ℓ_rᵀ`. -/
def check (C : Cert) : Bool :=
  decide (0 < C.c) &&
  allBelow C.m (fun r => decide (0 ≤ C.d r)) &&
  allBelow C.n (fun i => allBelow C.n (fun j =>
    decide (C.c * C.mat i j = sum C.m (fun r => C.d r * C.L r i * C.L r j))))

/-- 엄격 검사기: `check` 에 더해 행 수 `= n`, `d_r > 0`, `ℓ_r(r) ≠ 0`, `i > r → ℓ_r(i) = 0`. -/
def checkStrict (C : Cert) : Bool :=
  check C && decide (C.m = C.n) &&
  allBelow C.n (fun r => decide (0 < C.d r) && decide (C.L r r ≠ 0) &&
    allBelow C.n (fun i => decide (r < i → C.L r i = 0)))

/-! ## 4. 건전성 (■) -/

/-- **건전성**: 검사기가 받아들이면 `A` 는 양반정치. -/
theorem sound (C : Cert) (h : check C = true) : ∀ x : Nat → Int, 0 ≤ quad C.n C.mat x := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hd⟩, hEq⟩ := h
  intro x
  apply psd_of_cert C.n C.m C.c C.mat C.d C.L hc
  · intro r hr; exact of_decide_eq_true (allBelow_spec hd r hr)
  · intro i hi j hj
    exact of_decide_eq_true (allBelow_spec (allBelow_spec hEq i hi) j hj)

/-- **엄격 건전성**: 엄격 검사기가 받아들이면 `A` 는 양정치. -/
theorem sound_strict (C : Cert) (h : checkStrict C = true) :
    ∀ x : Nat → Int, (∃ k, k < C.n ∧ x k ≠ 0) → 0 < quad C.n C.mat x := by
  have hchk : check C = true := by
    simp only [checkStrict, Bool.and_eq_true] at h; exact h.1.1
  simp only [checkStrict, check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, _⟩, hEq⟩, hm⟩, hs⟩ := h
  have _ := hchk
  intro x hx
  have hEq' : ∀ i, i < C.n → ∀ j, j < C.n →
      C.c * C.mat i j = sum C.n (fun r => C.d r * C.L r i * C.L r j) := by
    intro i hi j hj
    rw [← hm]
    exact of_decide_eq_true (allBelow_spec (allBelow_spec hEq i hi) j hj)
  have hrow : ∀ r, r < C.n → (0 < C.d r ∧ C.L r r ≠ 0) ∧
      ∀ i, i < C.n → (r < i → C.L r i = 0) := by
    intro r hr
    have e := allBelow_spec hs r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    exact ⟨e.1, fun i hi => of_decide_eq_true (allBelow_spec e.2 i hi)⟩
  exact pd_of_cert C.n C.c C.mat C.d C.L hc
    (fun r hr => (hrow r hr).1.1) (fun r hr => (hrow r hr).1.2)
    (fun r hr i hi hri => (hrow r hr).2 i hi hri) hEq' x hx

/-- 따름정리: `xᵀAx < 0` 인 증인이 있으면 어떤 인증서도 통과하지 못한다. -/
theorem no_cert_of_witness (C : Cert) (x : Nat → Int) (hx : quad C.n C.mat x < 0) :
    check C = false := by
  cases hc : check C with
  | false => rfl
  | true => have := sound C hc x; omega

/-! ## 5. 견본 -/

/-- 경로 라플라시안 꼴 `A = [[2,-1,0],[-1,2,-1],[0,-1,2]]`,
`6A = 8·e₀e₀ᵀ + 1·(-2,3,0)(-2,3,0)ᵀ + 3·(0,-1,2)(0,-1,2)ᵀ` (뒤집은 LDLᵀ). -/
def certPath3 : Cert where
  n := 3
  A := [[2, -1, 0], [-1, 2, -1], [0, -1, 2]]
  c := 6
  rows := [(8, [1, 0, 0]), (1, [-2, 3, 0]), (3, [0, -1, 2])]

theorem demo_path3_check : check certPath3 = true := by decide
theorem demo_path3_strict : checkStrict certPath3 = true := by decide

theorem demo_path3_psd : ∀ x : Nat → Int, 0 ≤ quad 3 certPath3.mat x :=
  sound certPath3 demo_path3_check

theorem demo_path3_pd :
    ∀ x : Nat → Int, (∃ k, k < 3 ∧ x k ≠ 0) → 0 < quad 3 certPath3.mat x :=
  sound_strict certPath3 demo_path3_strict

/-- 특이(반정치) 꼴 `[[1,-1],[-1,1]] = (1,-1)(1,-1)ᵀ`: 반정치는 통과, 엄격은 불통. -/
def certSingular : Cert where
  n := 2
  A := [[1, -1], [-1, 1]]
  c := 1
  rows := [(1, [1, -1])]

theorem demo_singular_check : check certSingular = true := by decide
theorem demo_singular_not_strict : checkStrict certSingular = false := by decide

theorem demo_singular_psd : ∀ x : Nat → Int, 0 ≤ quad 2 certSingular.mat x :=
  sound certSingular demo_singular_check

/-- 거부 1: 부정치 `[[1,2],[2,1]]` 에 가짜 인증서 `(1,1)(1,1)ᵀ` — 등식 불성립. -/
def certFakeEq : Cert where
  n := 2
  A := [[1, 2], [2, 1]]
  c := 1
  rows := [(1, [1, 1])]

theorem demo_reject_eq : check certFakeEq = false := by decide

/-- 거부 2: `2A = 3·(1,1)(1,1)ᵀ + (-1)·(1,-1)(1,-1)ᵀ` 는 등식은 맞지만 무게가 음수. -/
def certFakeNeg : Cert where
  n := 2
  A := [[1, 2], [2, 1]]
  c := 2
  rows := [(3, [1, 1]), (-1, [1, -1])]

theorem demo_reject_neg : check certFakeNeg = false := by decide

/-- 거부 2 의 등식 자체는 정확히 성립함 (무게 검사가 본질적이라는 증거). -/
theorem demo_fakeNeg_identity_holds :
    allBelow 2 (fun i => allBelow 2 (fun j =>
      decide (certFakeNeg.c * certFakeNeg.mat i j =
        sum certFakeNeg.m (fun r => certFakeNeg.d r * certFakeNeg.L r i * certFakeNeg.L r j))))
      = true := by decide

/-- 거부 3: 척도 `c = 0` 은 거부. -/
def certZeroScale : Cert where
  n := 2
  A := [[1, 2], [2, 1]]
  c := 0
  rows := []

theorem demo_reject_zero_scale : check certZeroScale = false := by decide

/-- 증인 `x = (1,-1)` 에서 `xᵀAx = -2 < 0` 이므로, `[[1,2],[2,1]]` 에는
어떤 `(c, d, ℓ)` 인증서도 통과할 수 없다. -/
theorem demo_indefinite_no_cert (c : Int) (rows : List (Int × List Int)) :
    check { n := 2, A := [[1, 2], [2, 1]], c := c, rows := rows } = false :=
  no_cert_of_witness _ (fun k => if k = 0 then 1 else -1)
    (by show quad 2 (Cert.mat ⟨2, [[1, 2], [2, 1]], 0, []⟩) (fun k => if k = 0 then 1 else -1) < 0
        decide)

end PSD


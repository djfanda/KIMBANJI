import Trombo.PSD

/-!
# 창 상자 (Window Box) — 구간 산술 위의 양반정치 인증

구간(공) 산술의 창 행렬을 커널로 — 가운데 행렬 A₀ 와 반지름 e 의 상자 안 모든 행렬이
양반정치임을, A₀ − n·e·I 의 정수 인증서 하나로 보인다 (■)

* `iabs a = |a|` 는 `Int.natAbs` 를 정수로 되돌린 값.
* `abs_sum_sq` : `(Σ_{i<n} |x_i|)² ≤ n · Σ_{i<n} x_i²` (코시–슈바르츠, 정수판).
* `quad_perturb_lower` : 상자 `|M_{ij} − A_{ij}| ≤ e` 안에서
  `xᵀMx ≥ xᵀAx − e·(Σ|x_i|)²`, 그리고 `quad_perturb_lower'` : `≥ xᵀAx − n·e·Σ x_i²`.
* `quad_diag_shift` : `xᵀ(A − c·I)x = xᵀAx − c·Σ x_i²`.
* `box_sound` : `A₀ − n·e·I` 의 인증서가 검사기를 통과하면 상자 안 모든 `M` 이 양반정치.
* `box_sound_strict` : 엄격 검사기 통과면 상자 안 모든 `M` 이 양정치.

Core Lean 4 only: no `sorry`, no `native_decide`, no `axiom`.
-/

namespace WindowBox

open PSD

/-! ## 1. 절댓값과 합의 보조 정리 -/

/-- `|a|` (정수) -/
def iabs (a : Int) : Int := (a.natAbs : Int)

theorem iabs_nonneg (a : Int) : 0 ≤ iabs a := by unfold iabs; omega
theorem le_iabs (a : Int) : a ≤ iabs a := by unfold iabs; omega
theorem neg_le_iabs (a : Int) : -a ≤ iabs a := by unfold iabs; omega

theorem iabs_mul (a b : Int) : iabs (a * b) = iabs a * iabs b := by
  unfold iabs; rw [Int.natAbs_mul, Int.natCast_mul]

theorem iabs_mul_self (a : Int) : iabs a * iabs a = a * a := Int.natAbs_mul_self' a

theorem sum_le {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k ≤ g k) :
    sum n f ≤ sum n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [sum_succ]
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h n (Nat.lt_succ_self n)
    omega

theorem sum_const (n : Nat) (c : Int) : sum n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_succ, ih]; rw [Int.natCast_succ, Int.add_mul, Int.one_mul]

/-- 정수 라그랑주 항등식의 반쪽: `Σ_i Σ_j (a_i − a_j)² = 2(n Σ a² − (Σ a)²)`. -/
theorem lagrange (n : Nat) (a : Nat → Int) :
    sum n (fun i => sum n (fun j => (a i - a j) * (a i - a j)))
      = 2 * ((n : Int) * sum n (fun i => a i * a i) - sum n a * sum n a) := by
  have e1 : ∀ i, sum n (fun j => (a i - a j) * (a i - a j))
      = (n : Int) * (a i * a i) + sum n (fun j => a j * a j) - 2 * a i * sum n a := by
    intro i
    have : sum n (fun j => (a i - a j) * (a i - a j))
        = sum n (fun j => (a i * a i + a j * a j) + (-(2 * a i)) * a j) := by
      apply sum_congr; intro j _; grind
    rw [this, sum_add, sum_add, sum_const, ← mul_sum]
    grind
  rw [sum_congr (fun i _ => e1 i)]
  have e2 : sum n (fun i => (n : Int) * (a i * a i) + sum n (fun j => a j * a j) - 2 * a i * sum n a)
      = sum n (fun i => (n : Int) * (a i * a i)) + sum n (fun _ => sum n (fun j => a j * a j))
        + sum n (fun i => (-(2 * sum n a)) * a i) := by
    rw [← sum_add, ← sum_add]
    apply sum_congr; intro i _; grind
  rw [e2, ← mul_sum, sum_const, ← mul_sum]
  grind

/-- **코시–슈바르츠 (정수판)**: `(Σ_{i<n} |x_i|)² ≤ n · Σ_{i<n} x_i²`. -/
theorem abs_sum_sq (x : Nat → Int) (n : Nat) :
    sum n (fun i => iabs (x i)) * sum n (fun i => iabs (x i))
      ≤ (n : Int) * sum n (fun i => x i * x i) := by
  have hL := lagrange n (fun i => iabs (x i))
  have hnn : 0 ≤ sum n (fun i => sum n (fun j =>
      (iabs (x i) - iabs (x j)) * (iabs (x i) - iabs (x j))) ) :=
    sum_nonneg (fun i _ => sum_nonneg (fun j _ => square_nonneg _))
  have hs : sum n (fun i => iabs (x i) * iabs (x i)) = sum n (fun i => x i * x i) :=
    sum_congr (fun i _ => iabs_mul_self (x i))
  rw [hs] at hL
  omega

/-! ## 2. 상자 섭동의 아래 한계 -/

/-- 한 항: `|D| ≤ e` 이면 `0 ≤ e·|a|·|b| + a·D·b`. -/
theorem term_lower (a b D e : Int) (hD : iabs D ≤ e) :
    0 ≤ e * iabs a * iabs b + a * D * b := by
  have h1 : -(a * D * b) ≤ iabs (a * D * b) := neg_le_iabs _
  have h2 : iabs (a * D * b) = iabs D * (iabs a * iabs b) := by
    rw [iabs_mul, iabs_mul]; grind
  have h3 : iabs D * (iabs a * iabs b) ≤ e * (iabs a * iabs b) :=
    Int.mul_le_mul_of_nonneg_right hD (Int.mul_nonneg (iabs_nonneg a) (iabs_nonneg b))
  have h4 : e * iabs a * iabs b = e * (iabs a * iabs b) := Int.mul_assoc _ _ _
  omega

/-- **상자 아래 한계**: `|M_{ij} − A_{ij}| ≤ e` (모든 `i, j < n`) 이면
`xᵀMx ≥ xᵀAx − e·(Σ|x_i|)²`. -/
theorem quad_perturb_lower (n : Nat) (M A : Nat → Nat → Int) (e : Int)
    (h : ∀ i, i < n → ∀ j, j < n → iabs (M i j - A i j) ≤ e) (x : Nat → Int) :
    quad n A x - e * (sum n (fun i => iabs (x i)) * sum n (fun i => iabs (x i)))
      ≤ quad n M x := by
  have h1 : quad n M x = quad n A x
      + sum n (fun i => sum n (fun j => x i * (M i j - A i j) * x j)) := by
    unfold quad
    rw [← sum_add]
    apply sum_congr; intro i _
    rw [← sum_add]
    apply sum_congr; intro j _
    grind
  have h2 : e * (sum n (fun i => iabs (x i)) * sum n (fun i => iabs (x i)))
      = sum n (fun i => sum n (fun j => e * iabs (x i) * iabs (x j))) := by
    rw [sum_mul_sum, mul_sum]
    apply sum_congr; intro i _
    rw [mul_sum]
    apply sum_congr; intro j _
    grind
  have h3 : 0 ≤ sum n (fun i => sum n (fun j => e * iabs (x i) * iabs (x j)))
      + sum n (fun i => sum n (fun j => x i * (M i j - A i j) * x j)) := by
    rw [← sum_add]
    apply sum_nonneg; intro i hi
    rw [← sum_add]
    apply sum_nonneg; intro j hj
    exact term_lower (x i) (x j) (M i j - A i j) e (h i hi j hj)
  omega

/-- **상자 아래 한계 (제곱합판)**: 같은 가정과 `e ≥ 0` 이면
`xᵀMx ≥ xᵀAx − n·e·Σ x_i²`. -/
theorem quad_perturb_lower' (n : Nat) (M A : Nat → Nat → Int) (e : Int) (he : 0 ≤ e)
    (h : ∀ i, i < n → ∀ j, j < n → iabs (M i j - A i j) ≤ e) (x : Nat → Int) :
    quad n A x - (n : Int) * e * sum n (fun i => x i * x i) ≤ quad n M x := by
  have h1 := quad_perturb_lower n M A e h x
  have h2 := Int.mul_le_mul_of_nonneg_left (abs_sum_sq x n) he
  have h3 : e * ((n : Int) * sum n (fun i => x i * x i))
      = (n : Int) * e * sum n (fun i => x i * x i) := by grind
  omega

/-! ## 3. 대각 이동 -/

theorem quad_congr {n : Nat} {A B : Nat → Nat → Int}
    (h : ∀ i, i < n → ∀ j, j < n → A i j = B i j) (x : Nat → Int) :
    quad n A x = quad n B x := by
  unfold quad
  apply sum_congr; intro i hi
  apply sum_congr; intro j hj
  rw [h i hi j hj]

/-- `xᵀ(A − c·I)x = xᵀAx − c·Σ x_i²`. -/
theorem quad_diag_shift (n : Nat) (A : Nat → Nat → Int) (c : Int) (x : Nat → Int) :
    quad n (fun i j => A i j - (if i = j then c else 0)) x
      = quad n A x - c * sum n (fun i => x i * x i) := by
  have hrow : ∀ i, i < n →
      sum n (fun j => x i * (A i j - (if i = j then c else 0)) * x j)
        = sum n (fun j => x i * A i j * x j) + (-c) * (x i * x i) := by
    intro i hi
    have : sum n (fun j => x i * (A i j - (if i = j then c else 0)) * x j)
        = sum n (fun j => x i * A i j * x j)
          + sum n (fun j => x i * (-(if i = j then c else 0)) * x j) := by
      rw [← sum_add]; apply sum_congr; intro j _; grind
    rw [this, sum_single (f := fun j => x i * (-(if i = j then c else 0)) * x j) hi
          (fun k _ hk => by
            show x i * (-(if i = k then c else 0)) * x k = 0
            rw [ite_eq_right (fun e => hk e.symm)]; grind)]
    show sum n (fun j => x i * A i j * x j) + x i * (-(if i = i then c else 0)) * x i
      = sum n (fun j => x i * A i j * x j) + (-c) * (x i * x i)
    rw [ite_eq_left rfl]
    grind
  unfold quad
  rw [sum_congr hrow, sum_add, mul_sum]
  have : sum n (fun i => -c * (x i * x i)) = -(sum n (fun i => c * (x i * x i))) := by
    have := sum_add n (fun i => -c * (x i * x i)) (fun i => c * (x i * x i))
    have h0 : sum n (fun i => -c * (x i * x i) + c * (x i * x i)) = 0 :=
      sum_eq_zero (fun k _ => by grind)
    omega
  rw [this]
  omega

/-! ## 4. 상자 건전성 (■) -/

/-- **상자 건전성**: `A₀ − n·e·I` 의 인증서가 검사기를 통과하면, 가운데 `A₀`,
반지름 `e` 의 상자 안 모든 행렬 `M` 은 양반정치. -/
theorem box_sound (C : Cert) (hC : check C = true) (n : Nat) (A0 : Nat → Nat → Int)
    (e : Int) (he : 0 ≤ e) (hn : C.n = n)
    (hmat : ∀ i, i < n → ∀ j, j < n →
      C.mat i j = A0 i j - (if i = j then (n : Int) * e else 0))
    (M : Nat → Nat → Int)
    (hM : ∀ i, i < n → ∀ j, j < n → iabs (M i j - A0 i j) ≤ e) :
    ∀ x : Nat → Int, 0 ≤ quad n M x := by
  intro x
  have h0 := sound C hC x
  rw [hn, quad_congr hmat x, quad_diag_shift] at h0
  have h1 := quad_perturb_lower' n M A0 e he hM x
  omega

/-- **상자 엄격 건전성**: 엄격 검사기가 받아들이면 상자 안 모든 `M` 은 양정치. -/
theorem box_sound_strict (C : Cert) (hC : checkStrict C = true) (n : Nat)
    (A0 : Nat → Nat → Int) (e : Int) (he : 0 ≤ e) (hn : C.n = n)
    (hmat : ∀ i, i < n → ∀ j, j < n →
      C.mat i j = A0 i j - (if i = j then (n : Int) * e else 0))
    (M : Nat → Nat → Int)
    (hM : ∀ i, i < n → ∀ j, j < n → iabs (M i j - A0 i j) ≤ e) :
    ∀ x : Nat → Int, (∃ k, k < n ∧ x k ≠ 0) → 0 < quad n M x := by
  intro x hx
  have h0 := sound_strict C hC x (by rw [hn]; exact hx)
  rw [hn, quad_congr hmat x, quad_diag_shift] at h0
  have h1 := quad_perturb_lower' n M A0 e he hM x
  omega

/-- 상자가 너무 넓으면: `A₀ − n·e·I` 에 음의 증인이 있으면 어떤 인증서도 통과 못 함. -/
theorem box_no_cert_of_witness (C : Cert) (n : Nat) (A0 : Nat → Nat → Int) (e : Int)
    (hn : C.n = n)
    (hmat : ∀ i, i < n → ∀ j, j < n →
      C.mat i j = A0 i j - (if i = j then (n : Int) * e else 0))
    (x : Nat → Int)
    (hx : quad n (fun i j => A0 i j - (if i = j then (n : Int) * e else 0)) x < 0) :
    check C = false := by
  apply no_cert_of_witness C x
  rw [hn, quad_congr hmat x]
  exact hx

/-! ## 5. 견본 -/

/-- 목록 행렬의 항 (범위 밖은 0) — `Cert.mat` 과 같은 읽기. -/
def ent (A : List (List Int)) (i j : Nat) : Int := (A.getD i []).getD j 0

/-- 가운데 `A₀ = [[5,1],[1,5]]`. -/
def A0demo : List (List Int) := [[5, 1], [1, 5]]

/-- 반지름 `e = 1`, `n = 2`: `A₀ − 2·1·I = [[3,1],[1,3]]`,
`3·[[3,1],[1,3]] = 8·(1,0)(1,0)ᵀ + 1·(1,3)(1,3)ᵀ` (엄격판 삼각 구조). -/
def certBox : Cert where
  n := 2
  A := [[3, 1], [1, 3]]
  c := 3
  rows := [(8, [1, 0]), (1, [1, 3])]

theorem demo_certBox_check : check certBox = true := by decide
theorem demo_certBox_strict : checkStrict certBox = true := by decide

theorem demo_certBox_mat : ∀ i, i < 2 → ∀ j, j < 2 →
    certBox.mat i j = ent A0demo i j - (if i = j then ((2 : Nat) : Int) * 1 else 0) := by
  decide

/-- **견본**: `[[5,1],[1,5]]` 의 항마다 ±1 안의 모든 정수 행렬은 양반정치. -/
theorem demo_box (M : Nat → Nat → Int)
    (hM : ∀ i, i < 2 → ∀ j, j < 2 → iabs (M i j - ent A0demo i j) ≤ 1) :
    ∀ x : Nat → Int, 0 ≤ quad 2 M x :=
  box_sound certBox demo_certBox_check 2 (ent A0demo) 1 (by decide) rfl demo_certBox_mat M hM

/-- **견본 (엄격)**: 같은 상자의 모든 행렬은 양정치. -/
theorem demo_box_strict (M : Nat → Nat → Int)
    (hM : ∀ i, i < 2 → ∀ j, j < 2 → iabs (M i j - ent A0demo i j) ≤ 1) :
    ∀ x : Nat → Int, (∃ k, k < 2 ∧ x k ≠ 0) → 0 < quad 2 M x :=
  box_sound_strict certBox demo_certBox_strict 2 (ent A0demo) 1 (by decide) rfl
    demo_certBox_mat M hM

/-- **거부 견본**: 반지름 `e = 3` 이면 `A₀ − 2·3·I = [[-1,1],[1,-1]]` 이고
증인 `x = (1,0)` 에서 `-1 < 0` — 어떤 인증서도 통과하지 못한다. -/
theorem demo_box_too_wide (C : Cert) (hn : C.n = 2)
    (hmat : ∀ i, i < 2 → ∀ j, j < 2 →
      C.mat i j = ent A0demo i j - (if i = j then ((2 : Nat) : Int) * 3 else 0)) :
    check C = false :=
  box_no_cert_of_witness C 2 (ent A0demo) 3 hn hmat (fun k => if k = 0 then 1 else 0)
    (by decide)

/-- 거부가 정당함: 반지름 3 상자 안의 `[[2,4],[4,2]]` 는 실제로 부정치
(`x = (1,-1)` 에서 `-4`). -/
theorem demo_box_too_wide_real :
    (∀ i, i < 2 → ∀ j, j < 2 → iabs (ent [[2, 4], [4, 2]] i j - ent A0demo i j) ≤ 3) ∧
    quad 2 (ent [[2, 4], [4, 2]]) (fun k => if k = 0 then 1 else -1) < 0 := by
  decide

end WindowBox

#print axioms WindowBox.box_sound
#print axioms WindowBox.box_sound_strict
#print axioms WindowBox.demo_box
#print axioms WindowBox.demo_box_strict
#print axioms WindowBox.demo_box_too_wide
#print axioms WindowBox.demo_box_too_wide_real

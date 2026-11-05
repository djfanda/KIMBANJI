import Trombo.PSD

/-!
# 구 짓기 — 맞선 두 점을 더해 구를 짓고, 정수 호몰로지를 커널로 확인 (린 4 코어)

맞선 두 점 S⁰ = {+, −} 을 하나씩 이어 붙이면 (조인) 구가 된다 :
축 하나는 두 점 (S⁰), 둘은 네모 (원 S¹), 셋은 정팔면체 겉면 (S²), 넷은 16-포 경계 (S³).
꼭짓점은 `v = 2·축 + 부호` 로 적고, 면 (facet) 은 축마다 부호 하나를 고른 것이다.

1. 면 수와 오일러 수 : 축 1·2·3·4 에서 χ = 2, 0, 2, 0. 정팔면체 (6, 12, 8), 16-포 경계 (8, 24, 32, 16).
   닫힌 의사다양체 : 한 차원 낮은 면은 모두 정확히 두 면에 들어 있다 (축 2·3·4).
2. 순서 무관 : 어떤 순서로 짝을 더해도 면 집합은 같다. 일반 정리 `mem_build`
   (면 = 축마다 한 끝을 고른 것) 와 `build_order_free`, 그리고 축 넷의 24 순서 전수 확인.
3. 정수 호몰로지를 축약 증명서로 : 일반 정리 `cycle_is_boundary` —
   `d₂ P + Q d₁ = I` (모서리 위 성분별 등식) 이면 모든 정수 1-고리 z 는 z = d₂ (P z) 로 경계다.
   같은 정리를 한 차원 위에 쓰면 H₂. 증명서 P, Q 는 파이썬 (`은비/쌍대층/구짓기_증명서.py`) 이 신장 나무와
   정수 연립식으로 찾고, 등식은 커널이 정수 셈으로 확인한다. 경계 행렬 자체는 린이 면 목록에서 계산한다.
   · 정팔면체 : H₁ = 0. · 16-포 경계 : H₁ = 0, H₂ = 0.
   · 음성 대조 : 네모의 둘레 고리는 경계가 아니다 (2-면이 없다). 7 꼭짓점 원환면에서는
     공고리 w (w ∘ d₂ = 0) 와 고리 z 의 짝 w·z = 7 ≠ 0 이라 z 는 경계가 아니다 (`not_boundary_of_cocycle`).

정직한 범위 : 모두 고전 사실 (S⁰ 의 조인은 구, 단체 호몰로지) 을 커널이 확인할 수 있게 옮긴 것이다.
구를 짓는 것은 푸앵카레 추측이 아니다 (어려운 쪽, 단일 연결 닫힌 3-다양체가 구라는 방향은 페렐만의 정리다).
기본군은 여기서 형식화하지 않았고 정수 호몰로지만 다룬다. 어떤 미해결 문제에 대해서도 주장하지 않는다.

Core Lean 4 only: `sorry`, `native_decide`, 새 공리 없음.
-/

namespace SphereJoin

open PSD (sum sum_zero sum_succ sum_congr sum_add mul_sum sum_mul sum_comm sum_eq_zero sum_single)

/-! ## 1. 단체 복합체와 S⁰ 이어 붙이기 -/

/-- 면 = 꼭짓점 목록 (오름차순) -/
abbrev Face := List Nat
/-- 복합체 = 최대 면 (facet) 목록 -/
abbrev Cx := List Face

/-- 축 `a` 의 맞선 두 점 {2a, 2a+1} 을 이어 붙이기 (S⁰ 과의 조인) : 면마다 두 끝 중 하나를 더한다 -/
def addPair (a : Nat) : Cx → Cx
  | [] => []
  | f :: K => (2 * a :: f) :: ((2 * a + 1) :: f) :: addPair a K

/-- 축 목록의 짝을 차례로 더한다 (목록 끝의 축부터 붙는다). 빈 복합체의 면은 빈 면 하나 -/
def build : List Nat → Cx
  | [] => [[]]
  | a :: l => addPair a (build l)

/-- 축 k 개의 정십자다면체 경계 -/
def cross (k : Nat) : Cx := build (List.range k)

/-- 길이 m 인 부분 목록 (순서 유지) -/
def sublistsLen : Nat → List Nat → Cx
  | 0, _ => [[]]
  | _ + 1, [] => []
  | m + 1, a :: l => (sublistsLen m l).map (a :: ·) ++ sublistsLen (m + 1) l

/-- 처음 나온 것만 남기기 -/
def dedup (l : Cx) : Cx := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- 꼭짓점 m 개짜리 면 전부 -/
def faces (K : Cx) (m : Nat) : Cx := dedup (K.flatMap (sublistsLen m))

/-- 면 수 (꼭짓점 1 개짜리부터 n 개짜리까지) -/
def fvec (K : Cx) (n : Nat) : List Nat := (List.range n).map fun m => (faces K (m + 1)).length

/-- 오일러 수 χ = Σ (−1)^m · (꼭짓점 m+1 개짜리 면 수) -/
def euler (K : Cx) (n : Nat) : Int :=
  ((List.range n).map fun m => (if m % 2 == 0 then (1 : Int) else -1) * (faces K (m + 1)).length).foldl (· + ·) 0

/-- 닫힌 의사다양체 : 꼭짓점 r 개짜리 면 (한 차원 낮은 면) 이 모두 정확히 두 최대 면에 들어 있다 -/
def closedPM (K : Cx) (r : Nat) : Bool :=
  (faces K r).all fun τ => (K.filter fun σ => τ.all σ.contains).length == 2

theorem cross1_euler : fvec (cross 1) 1 = [2] ∧ euler (cross 1) 1 = 2 := by decide +kernel
theorem cross2_euler : fvec (cross 2) 2 = [4, 4] ∧ euler (cross 2) 2 = 0 := by decide +kernel
/-- 정팔면체 겉면 : 꼭짓점 6, 모서리 12, 삼각형 8, χ = 2 -/
theorem cross3_euler : fvec (cross 3) 3 = [6, 12, 8] ∧ euler (cross 3) 3 = 2 := by decide +kernel
/-- 16-포 경계 : 8, 24, 32, 16, χ = 0 -/
theorem cross4_euler : fvec (cross 4) 4 = [8, 24, 32, 16] ∧ euler (cross 4) 4 = 0 := by decide +kernel

/-- 닫힌 의사다양체 : 네모의 꼭짓점, 정팔면체의 모서리, 16-포 경계의 삼각형은 저마다 정확히 두 면에 들어 있다 -/
theorem cross_closed_pm :
    closedPM (cross 2) 1 = true ∧ closedPM (cross 3) 2 = true ∧ closedPM (cross 4) 3 = true := by
  decide +kernel

/-! ## 2. 순서 무관 -/

theorem mem_addPair {a : Nat} {K : Cx} {f : Face} :
    f ∈ addPair a K ↔ ∃ g ∈ K, f = 2 * a :: g ∨ f = (2 * a + 1) :: g := by
  induction K with
  | nil => simp [addPair]
  | cons g K ih =>
    simp only [addPair, List.mem_cons, ih]
    constructor
    · rintro (h | h | ⟨g', hg', h⟩)
      · exact ⟨g, Or.inl rfl, Or.inl h⟩
      · exact ⟨g, Or.inl rfl, Or.inr h⟩
      · exact ⟨g', Or.inr hg', h⟩
    · rintro ⟨g', hg' | hg', h⟩
      · subst hg'
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨g', hg', h⟩)

/-- 한꺼번에 읽기 : 면은 정확히 "축 목록의 축마다 한 끝 (2a 또는 2a+1) 을 고른 것" 이다 -/
theorem mem_build {l : List Nat} {f : Face} : f ∈ build l ↔ f.map (· / 2) = l := by
  induction l generalizing f with
  | nil => simp [build]
  | cons a l ih =>
    simp only [build, mem_addPair, ih]
    constructor
    · rintro ⟨g, hg, h | h⟩ <;> subst h <;> simp only [List.map_cons, hg, List.cons.injEq, and_true] <;> omega
    · intro h
      cases f with
      | nil => simp at h
      | cons x g =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨hx, hg⟩ := h
        refine ⟨g, hg, ?_⟩
        have : x = 2 * a ∨ x = 2 * a + 1 := by omega
        rcases this with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])

/-- 면의 수는 2^(축 수) -/
theorem length_build (l : List Nat) : (build l).length = 2 ^ l.length := by
  have hp : ∀ (a : Nat) (K : Cx), (addPair a K).length = 2 * K.length := by
    intro a K
    induction K with
    | nil => rfl
    | cons f K ih => simp only [addPair, List.length_cons, ih]; omega
  induction l with
  | nil => rfl
  | cons a l ih => simp only [build, hp, ih, List.length_cons, Nat.pow_succ]; omega

theorem eq_of_nodup_map {f : Face} (hf : (f.map (· / 2)).Nodup) {x y : Nat}
    (hx : x ∈ f) (hy : y ∈ f) (hxy : x / 2 = y / 2) : x = y := by
  induction f with
  | nil => simp at hx
  | cons c r ih =>
    rw [List.map_cons, List.nodup_cons] at hf
    obtain ⟨hc, hr⟩ := hf
    rw [List.mem_cons] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]
    · subst hx
      exact absurd (List.mem_map.mpr ⟨y, hy, hxy.symm⟩) hc
    · subst hy
      exact absurd (List.mem_map.mpr ⟨x, hx, hxy⟩) hc
    · exact ih hr hx hy

/-- 면 f 가 축 a 에서 고른 끝 -/
def pick (f : Face) (a : Nat) : Nat := if 2 * a ∈ f then 2 * a else 2 * a + 1

/-- 순서 무관 (일반) : 같은 축들을 (겹침 없이) 다른 순서로 더해도, 면마다 같은 꼭짓점 집합의 면이 있다 -/
theorem build_order_free {l l' : List Nat} (hl : l.Nodup) (hmem : ∀ a, a ∈ l ↔ a ∈ l')
    {f : Face} (hf : f ∈ build l) : ∃ f' ∈ build l', ∀ v, v ∈ f ↔ v ∈ f' := by
  rw [mem_build] at hf
  have hnd : (f.map (· / 2)).Nodup := by rw [hf]; exact hl
  refine ⟨l'.map (pick f), ?_, ?_⟩
  · rw [mem_build, List.map_map]
    have hp : ∀ a, pick f a / 2 = a := by
      intro a; unfold pick; split <;> omega
    simp [Function.comp_def, hp]
  · intro v
    constructor
    · intro hv
      have ha : v / 2 ∈ l := by rw [← hf]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
      refine List.mem_map.mpr ⟨v / 2, (hmem _).mp ha, ?_⟩
      unfold pick
      split
      · rename_i h
        by_cases hv2 : v % 2 = 0
        · omega
        · have := eq_of_nodup_map hnd h hv (by omega)
          omega
      · rename_i h
        by_cases hv2 : v % 2 = 0
        · exact absurd (by rwa [show 2 * (v / 2) = v by omega]) h
        · omega
    · intro hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      have ha' : a ∈ f.map (· / 2) := by rw [hf]; exact (hmem a).mpr ha
      obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ha'
      unfold pick
      split
      · assumption
      · rename_i h
        have hne : x ≠ 2 * a := fun e => h (e ▸ hx)
        have : x = 2 * a + 1 := by omega
        exact this ▸ hx

/-- 끼워 넣기 순열 -/
def insertAll (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (b :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertAll a)

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insertSorted x l

def isort : List Nat → List Nat
  | [] => []
  | x :: l => insertSorted x (isort l)

/-- 꼭짓점 집합으로 본 면 목록이 같다 -/
def sameFacets (K L : Cx) : Bool :=
  let K' := K.map isort
  let L' := L.map isort
  K'.length == L'.length && K'.all L'.contains && L'.all K'.contains

/-- 한꺼번에 : 0 ≤ s < 2^k 의 이진 자리로 축마다 부호를 고른다 -/
def allAtOnce (k : Nat) : Cx :=
  (List.range (2 ^ k)).map fun s => (List.range k).map fun a => 2 * a + (s / 2 ^ a) % 2

/-- 축 넷 : 24 가지 순서 모두, 그리고 한꺼번에 고르기가 같은 16 면을 준다.
동서 먼저 ([3,2,1,0] 은 축 0 부터 붙는다), 남북 먼저 ([0,…] 은 축 3 부터 붙는다) 도 이 안에 있다 -/
theorem all_orders_k4 :
    (perms [0, 1, 2, 3]).length = 24 ∧
    (perms [0, 1, 2, 3]).all (fun l => sameFacets (build l) (cross 4)) = true ∧
    sameFacets (allAtOnce 4) (cross 4) = true ∧ (cross 4).length = 16 := by
  decide +kernel

theorem all_at_once_small :
    sameFacets (allAtOnce 1) (cross 1) = true ∧ sameFacets (allAtOnce 2) (cross 2) = true ∧
    sameFacets (allAtOnce 3) (cross 3) = true := by
  decide +kernel

/-! ## 3. 정수 호몰로지 : 축약 증명서 -/

/-- 행렬 곱 벡터 : (A x)_i = Σ_{j<n} A i j · x j -/
def mv (n : Nat) (A : Nat → Nat → Int) (x : Nat → Int) (i : Nat) : Int := sum n fun j => A i j * x j

/-- 축약 증명서 정리 (일반) : 사슬 C₂ →d₂ C₁ →d₁ C₀ (크기 n2, n1, n0) 와 정수 행렬 P (C₁→C₂), Q (C₀→C₁) 가
`d₂ P + Q d₁ = I` (C₁ 위 성분별) 를 만족하면, 모든 정수 고리 z (d₁ z = 0) 는 경계 z = d₂ (P z) 이다.
어느 차원에서나 같은 꼴이다 (H₁ 에는 모서리, H₂ 에는 삼각형을 가운데에 둔다). -/
theorem cycle_is_boundary (n0 n1 n2 : Nat) (dLo dHi P Q : Nat → Nat → Int)
    (hId : ∀ i, i < n1 → ∀ j, j < n1 →
      sum n2 (fun f => dHi i f * P f j) + sum n0 (fun v => Q i v * dLo v j) = if i = j then 1 else 0)
    (z : Nat → Int) (hz : ∀ v, v < n0 → mv n1 dLo z v = 0) :
    ∀ e, e < n1 → z e = mv n2 dHi (mv n1 P z) e := by
  intro e he
  have h1 : sum n1 (fun j => (if e = j then (1 : Int) else 0) * z j) = z e := by
    rw [sum_single he (fun k _ hk => by simp [Ne.symm hk])]
    simp
  have h2 : sum n1 (fun j => (if e = j then (1 : Int) else 0) * z j)
      = sum n1 (fun j => sum n2 (fun f => dHi e f * P f j * z j))
        + sum n1 (fun j => sum n0 (fun v => Q e v * dLo v j * z j)) := by
    rw [← sum_add]
    apply sum_congr
    intro j hj
    rw [← hId e he j hj, Int.add_mul, sum_mul, sum_mul]
  have h3 : sum n1 (fun j => sum n0 (fun v => Q e v * dLo v j * z j)) = 0 := by
    rw [sum_comm n1 n0 (fun j v => Q e v * dLo v j * z j)]
    apply sum_eq_zero
    intro v hv
    have hzv := hz v hv
    unfold mv at hzv
    rw [show (fun j => Q e v * dLo v j * z j) = (fun j => Q e v * (dLo v j * z j)) from
      funext fun j => Int.mul_assoc _ _ _, ← mul_sum, hzv, Int.mul_zero]
  rw [← h1, h2, h3, Int.add_zero, sum_comm n1 n2 (fun j f => dHi e f * P f j * z j)]
  unfold mv
  apply sum_congr
  intro f _
  rw [mul_sum]
  apply sum_congr
  intro j _
  rw [Int.mul_assoc]

/-- 공고리 시험 (일반) : w ∘ d₂ = 0 (모든 2-면에서) 이고 w·z ≠ 0 이면 z 는 어떤 정수 사슬의 경계도 아니다 -/
theorem not_boundary_of_cocycle (n1 n2 : Nat) (dHi : Nat → Nat → Int) (w z : Nat → Int)
    (hw : ∀ f, f < n2 → sum n1 (fun e => w e * dHi e f) = 0)
    (hwz : sum n1 (fun e => w e * z e) ≠ 0) :
    ¬ ∃ c : Nat → Int, ∀ e, e < n1 → z e = mv n2 dHi c e := by
  rintro ⟨c, hc⟩
  apply hwz
  calc sum n1 (fun e => w e * z e)
      = sum n1 (fun e => sum n2 (fun f => w e * dHi e f * c f)) := by
        apply sum_congr
        intro e he
        rw [hc e he]
        unfold mv
        rw [mul_sum]
        apply sum_congr
        intro f _
        rw [Int.mul_assoc]
    _ = sum n2 (fun f => sum n1 (fun e => w e * dHi e f * c f)) :=
        sum_comm n1 n2 (fun e f => w e * dHi e f * c f)
    _ = 0 := by
        apply sum_eq_zero
        intro f hf
        rw [← sum_mul n1 (c f) (fun e => w e * dHi e f), hw f hf, Int.zero_mul]

/-! ### 표로 적은 행렬 -/

/-- 목록의 목록에서 (i, j) 칸 (범위 밖은 0) -/
def ent (T : List (List Int)) (i j : Nat) : Int := (T.getD i []).getD j 0
/-- 행으로 저장 : rowM T i j = T[i][j] -/
def rowM (T : List (List Int)) : Nat → Nat → Int := fun i j => ent T i j
/-- 열로 저장 : colM T i j = T[j][i] -/
def colM (T : List (List Int)) : Nat → Nat → Int := fun i j => ent T j i
/-- 목록을 벡터로 -/
def vec (l : List Int) : Nat → Int := fun i => l.getD i 0

/-- 목록 내적 -/
def dotL : List Int → List Int → Int
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: l, b :: m => a * b + dotL l m

theorem sum_shift (n : Nat) (f : Nat → Int) : sum (n + 1) f = f 0 + sum n (fun k => f (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_succ, ih, sum_succ]; omega

theorem sum_dot (l m : List Int) (n : Nat) (h : l.length ≤ n) :
    sum n (fun k => l.getD k 0 * m.getD k 0) = dotL l m := by
  induction l generalizing m n with
  | nil =>
    show _ = 0
    exact sum_eq_zero fun k _ => by simp
  | cons a l ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      cases m with
      | nil =>
        show _ = 0
        exact sum_eq_zero fun k _ => by simp
      | cons b m =>
        rw [sum_shift]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [ih m n (Nat.le_of_succ_le_succ h)]
        rfl

/-- 표 증명서를 함수 꼴 등식으로 : 행 길이가 범위 안이면, 내적 등식이 `cycle_is_boundary` 의 가정이 된다 -/
theorem htpy_of_tables (n0 n1 n2 : Nat) (A B C D : List (List Int))
    (hA : ∀ i, i < n1 → (A.getD i []).length ≤ n2)
    (hC : ∀ i, i < n1 → (C.getD i []).length ≤ n0)
    (h : ∀ i, i < n1 → ∀ j, j < n1 →
      dotL (A.getD i []) (B.getD j []) + dotL (C.getD i []) (D.getD j []) = if i = j then 1 else 0) :
    ∀ i, i < n1 → ∀ j, j < n1 →
      sum n2 (fun f => rowM A i f * colM B f j) + sum n0 (fun v => rowM C i v * colM D v j)
        = if i = j then 1 else 0 := by
  intro i hi j hj
  unfold rowM colM ent
  rw [sum_dot _ _ _ (hA i hi), sum_dot _ _ _ (hC i hi)]
  exact h i hi j hj

/-- 표로 적은 행렬로 `cycle_is_boundary` : 경계가 있다 -/
theorem bounds_of_tables (n0 n1 n2 : Nat) (A B C D : List (List Int))
    (hA : ∀ i, i < n1 → (A.getD i []).length ≤ n2)
    (hC : ∀ i, i < n1 → (C.getD i []).length ≤ n0)
    (h : ∀ i, i < n1 → ∀ j, j < n1 →
      dotL (A.getD i []) (B.getD j []) + dotL (C.getD i []) (D.getD j []) = if i = j then 1 else 0)
    (z : Nat → Int) (hz : ∀ v, v < n0 → mv n1 (colM D) z v = 0) :
    ∃ c : Nat → Int, ∀ e, e < n1 → z e = mv n2 (rowM A) c e :=
  ⟨mv n1 (colM B) z,
    cycle_is_boundary n0 n1 n2 (colM D) (rowM A) (colM B) (rowM C)
      (htpy_of_tables n0 n1 n2 A B C D hA hC h) z hz⟩

/-! ### 경계 행렬 (린이 면 목록에서 계산) -/

/-- ∂σ 안의 τ 계수 : σ 에서 p 번째 꼭짓점을 빼면 τ 일 때 (−1)^p -/
def coef (τ σ : Face) : Int :=
  (List.range σ.length).foldl
    (fun acc p => if σ.eraseIdx p == τ then acc + (if p % 2 == 0 then 1 else -1) else acc) 0

/-- 행 = 낮은 면 : bdRows lo hi 의 i 행 j 칸 = ∂(hi_j) 안의 lo_i 계수 -/
def bdRows (lo hi : Cx) : List (List Int) := lo.map fun τ => hi.map fun σ => coef τ σ
/-- 행 = 높은 면 (열 저장) : bdCols lo hi 의 j 행 i 칸 = ∂(hi_j) 안의 lo_i 계수 -/
def bdCols (lo hi : Cx) : List (List Int) := hi.map fun σ => lo.map fun τ => coef τ σ

/-! ## 4. 증명서 (파이썬 생성, 커널 확인) -/

/-- 정팔면체 P 의 열 : 모서리 e ↦ 2-사슬 c_e (삼각형 8 칸) -/
def octaP : List (List Int) :=
  [[0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [1, -1, -1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 1, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0]]

/-- 정팔면체 Q 의 행 : 모서리 e 의 꼭짓점별 계수 (뿌리에서 오는 나무 길) -/
def octaQ : List (List Int) :=
  [[0, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0]]

/-- 16-포 경계 P 의 열 : 모서리 e ↦ 2-사슬 (삼각형 32 칸) -/
def cellP : List (List Int) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [-1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]]

/-- 16-포 경계 Q 의 행 : 모서리 e 의 꼭짓점별 계수 (나무 길) -/
def cellQ : List (List Int) :=
  [[0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0]]

/-- 16-포 경계 P₂ 의 열 : 삼각형 f ↦ 3-사슬 (사면체 16 칸) -/
def cellP2 : List (List Int) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, -1, -1, 1, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

/-- 16-포 경계 Q₂ 의 행 : 삼각형 f 의 모서리별 계수 (= P 를 뒤집어 읽은 것) -/
def cellQ2 : List (List Int) :=
  [[0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- 정팔면체 방향 사슬 (삼각형마다 ±1) -/
def octaTop : List Int := [1, -1, -1, 1, -1, 1, 1, -1]

/-- 16-포 경계 방향 사슬 (사면체마다 ±1) -/
def cellTop : List Int := [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]

/-- 원환면 공고리 w (모서리 21 칸) : 차이 1 ↦ 1, 2 ↦ −1, 3 ↦ 0 (방향 따라 부호) -/
def torusW : List Int := [1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 0, 1, 1, 0, 1, 1, -1, -1, 0]

/-- 원환면 고리 z : 0 → 1 → … → 6 → 0 -/
def torusZ : List Int := [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0]

/-- 네모 둘레 고리 (모서리 4 칸) -/
def squareZ : List Int := [1, -1, -1, 1]


/-! ## 5. 정팔면체 겉면 (S²) : H₁ = 0 -/

def octa : Cx := cross 3
def octaV : Cx := faces octa 1
def octaE : Cx := faces octa 2
def octaF : Cx := faces octa 3
/-- ∂₁ 을 모서리마다 적은 표 (모서리 e 의 행 = 꼭짓점 6 칸) -/
def octaD1 : List (List Int) := bdCols octaV octaE
/-- ∂₂ 를 모서리마다 적은 표 (모서리 e 의 행 = 삼각형 8 칸) -/
def octaD2 : List (List Int) := bdRows octaE octaF
/-- ∂₁ : (꼭짓점 v, 모서리 e) ↦ 계수 -/
def octa_d1 : Nat → Nat → Int := colM octaD1
/-- ∂₂ : (모서리 e, 삼각형 f) ↦ 계수 -/
def octa_d2 : Nat → Nat → Int := rowM octaD2

theorem octa_sizes : octaV.length = 6 ∧ octaE.length = 12 ∧ octaF.length = 8 := by decide +kernel

/-- 사슬 복합체 : ∂₁ ∂₂ = 0 -/
theorem octa_dd : ∀ v, v < 6 → ∀ f, f < 8 → sum 12 (fun e => octa_d1 v e * octa_d2 e f) = 0 := by
  decide +kernel

/-- 증명서 등식 ∂₂ P + Q ∂₁ = I (모서리 12 × 12) -/
theorem octa_cert : ∀ i, i < 12 → ∀ j, j < 12 →
    dotL (octaD2.getD i []) (octaP.getD j []) + dotL (octaQ.getD i []) (octaD1.getD j [])
      = if i = j then 1 else 0 := by
  decide +kernel

/-- 정팔면체 겉면의 H₁ = 0 : 모든 정수 1-고리는 어떤 정수 2-사슬의 경계다 -/
theorem octa_H1 (z : Nat → Int) (hz : ∀ v, v < 6 → mv 12 octa_d1 z v = 0) :
    ∃ c : Nat → Int, ∀ e, e < 12 → z e = mv 8 octa_d2 c e :=
  bounds_of_tables 6 12 8 octaD2 octaP octaQ octaD1 (by decide +kernel) (by decide +kernel) octa_cert z hz

/-- 꼭대기 고리 : 삼각형마다 ±1 인 2-고리가 있다 (3-면이 없으니 경계가 아니다 · H₂ ≠ 0) -/
theorem octa_top : (∀ e, e < 12 → mv 8 octa_d2 (vec octaTop) e = 0) ∧
    octaTop.length = 8 ∧ octaTop.all (fun x => x == 1 || x == -1) = true := by
  decide +kernel

/-! ## 6. 16-포 경계 (S³) : H₁ = 0, H₂ = 0 -/

def cell : Cx := cross 4
def cellV : Cx := faces cell 1
def cellE : Cx := faces cell 2
def cellF : Cx := faces cell 3
def cellT : Cx := faces cell 4
/-- ∂₁ 을 모서리마다 (꼭짓점 8 칸) -/
def cellD1 : List (List Int) := bdCols cellV cellE
/-- ∂₂ 를 모서리마다 (삼각형 32 칸) -/
def cellD2 : List (List Int) := bdRows cellE cellF
/-- ∂₂ 를 삼각형마다 (모서리 24 칸) -/
def cellD2c : List (List Int) := bdCols cellE cellF
/-- ∂₃ 을 삼각형마다 (사면체 16 칸) -/
def cellD3 : List (List Int) := bdRows cellF cellT
def cell_d1 : Nat → Nat → Int := colM cellD1
def cell_d2 : Nat → Nat → Int := rowM cellD2
def cell_d3 : Nat → Nat → Int := rowM cellD3

theorem cell_sizes : cellV.length = 8 ∧ cellE.length = 24 ∧ cellF.length = 32 ∧ cellT.length = 16 := by
  decide +kernel

/-- 두 표는 같은 ∂₂ 다 -/
theorem cell_d2_agree : ∀ e, e < 24 → ∀ f, f < 32 → colM cellD2c e f = cell_d2 e f := by
  decide +kernel

/-- 사슬 복합체 : ∂₁ ∂₂ = 0, ∂₂ ∂₃ = 0 -/
theorem cell_dd : (∀ v, v < 8 → ∀ f, f < 32 → sum 24 (fun e => cell_d1 v e * cell_d2 e f) = 0) ∧
    (∀ e, e < 24 → ∀ t, t < 16 → sum 32 (fun f => cell_d2 e f * cell_d3 f t) = 0) := by
  decide +kernel

/-- 증명서 등식 (H₁) : ∂₂ P + Q ∂₁ = I (모서리 24 × 24) -/
theorem cell_cert1 : ∀ i, i < 24 → ∀ j, j < 24 →
    dotL (cellD2.getD i []) (cellP.getD j []) + dotL (cellQ.getD i []) (cellD1.getD j [])
      = if i = j then 1 else 0 := by
  decide +kernel

/-- 증명서 등식 (H₂) : ∂₃ P₂ + Q₂ ∂₂ = I (삼각형 32 × 32) -/
theorem cell_cert2 : ∀ i, i < 32 → ∀ j, j < 32 →
    dotL (cellD3.getD i []) (cellP2.getD j []) + dotL (cellQ2.getD i []) (cellD2c.getD j [])
      = if i = j then 1 else 0 := by
  decide +kernel

/-- 16-포 경계의 H₁ = 0 -/
theorem cell_H1 (z : Nat → Int) (hz : ∀ v, v < 8 → mv 24 cell_d1 z v = 0) :
    ∃ c : Nat → Int, ∀ e, e < 24 → z e = mv 32 cell_d2 c e :=
  bounds_of_tables 8 24 32 cellD2 cellP cellQ cellD1 (by decide +kernel) (by decide +kernel) cell_cert1 z hz

/-- 16-포 경계의 H₂ = 0 : 모든 정수 2-고리는 어떤 정수 3-사슬의 경계다 -/
theorem cell_H2 (z : Nat → Int) (hz : ∀ e, e < 24 → mv 32 cell_d2 z e = 0) :
    ∃ c : Nat → Int, ∀ f, f < 32 → z f = mv 16 cell_d3 c f :=
  bounds_of_tables 24 32 16 cellD3 cellP2 cellQ2 cellD2c (by decide +kernel) (by decide +kernel) cell_cert2 z
    (fun e he => by
      rw [← hz e he]
      unfold mv
      apply sum_congr
      intro f hf
      rw [cell_d2_agree e he f hf])

/-- 꼭대기 고리 : 사면체마다 ±1 인 3-고리 (H₃ ≠ 0) -/
theorem cell_top : (∀ f, f < 32 → mv 16 cell_d3 (vec cellTop) f = 0) ∧
    cellTop.length = 16 ∧ cellTop.all (fun x => x == 1 || x == -1) = true := by
  decide +kernel

/-! ## 7. 음성 대조 -/

/-! ### 네모 (축 둘, S¹) : 둘레 고리는 경계가 아니다 -/

def square : Cx := cross 2
def sqV : Cx := faces square 1
def sqE : Cx := faces square 2
def sq_d1 : Nat → Nat → Int := colM (bdCols sqV sqE)

/-- 2-면이 없다 -/
theorem square_no_triangles : faces square 3 = [] := by decide +kernel

/-- 둘레 고리 z 는 고리다 (∂₁ z = 0) 이고 0 이 아니다 -/
theorem square_cycle : (∀ v, v < 4 → mv 4 sq_d1 (vec squareZ) v = 0) ∧ vec squareZ 0 ≠ 0 := by
  decide +kernel

/-- 어떤 ∂₂ 를 대도 (2-면 0 개) z 는 경계가 아니다 : H₁ ≠ 0 -/
theorem square_not_boundary (dHi : Nat → Nat → Int) :
    ¬ ∃ c : Nat → Int, ∀ e, e < 4 → vec squareZ e = mv 0 dHi c e :=
  not_boundary_of_cocycle 4 0 dHi (vec squareZ) (vec squareZ)
    (fun f hf => absurd hf (Nat.not_lt_zero f)) (by decide +kernel)

/-! ### 7 꼭짓점 원환면 : 공고리로 본 고리 -/

/-- 삼각형 {i, i+1, i+3}, {i, i+2, i+3} (mod 7) -/
def torus7 : Cx :=
  (List.range 7).map (fun i => isort [i, (i + 1) % 7, (i + 3) % 7]) ++
  (List.range 7).map (fun i => isort [i, (i + 2) % 7, (i + 3) % 7])

/-- 원환면 : 7, 21, 14, χ = 0, 닫힌 의사다양체 -/
theorem torus_shape : fvec torus7 3 = [7, 21, 14] ∧ euler torus7 3 = 0 ∧ closedPM torus7 2 = true := by
  decide +kernel

def torV : Cx := faces torus7 1
def torE : Cx := faces torus7 2
def torF : Cx := faces torus7 3
def tor_d1 : Nat → Nat → Int := colM (bdCols torV torE)
def tor_d2 : Nat → Nat → Int := rowM (bdRows torE torF)

/-- z (0 → 1 → … → 6 → 0) 는 고리, w 는 공고리 (w ∘ ∂₂ = 0), 짝 w·z = 7 -/
theorem torus_cert : (∀ v, v < 7 → mv 21 tor_d1 (vec torusZ) v = 0) ∧
    (∀ f, f < 14 → sum 21 (fun e => vec torusW e * tor_d2 e f) = 0) ∧
    sum 21 (fun e => vec torusW e * vec torusZ e) = 7 := by
  decide +kernel

/-- 원환면의 고리 z 는 어떤 정수 2-사슬의 경계도 아니다 : H₁ ≠ 0 -/
theorem torus_not_boundary : ¬ ∃ c : Nat → Int, ∀ e, e < 21 → vec torusZ e = mv 14 tor_d2 c e :=
  not_boundary_of_cocycle 21 14 tor_d2 (vec torusW) (vec torusZ) torus_cert.2.1
    (by rw [torus_cert.2.2]; decide)

end SphereJoin

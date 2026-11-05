/-
두 길 — 정사면체에서 면의 갯수와 면의 형태로 갈라져 6 에서 평면 (바닥) 에 닿음 (린 4 코어)

정다면체 {p, q} : 면은 정 p 각형, 꼭짓점마다 면 q 장. d = 2p + 2q − pq = 4 − (p − 2)(q − 2).
오일러 V − E + F = 2 와 pF = 2E = qV 에서 F = 4q/d · V = 4p/d · E = 2pq/d.

  1. 일반 정리 (모든 자연수 p, q ≥ 3) : d > 0 이면 p ≤ 5 · q ≤ 5, d = 0 이면 p ≤ 6 · q ≤ 6.
     → d > 0 인 짝은 정확히 다섯 (정다면체), d = 0 인 짝은 정확히 셋 (평면 타일 {3,6} · {4,4} · {6,3}).
  2. 한 꼭짓점에 모인 각 : 360p − 180q(p − 2) = 180 d (모든 정수) — 각의 합이 360° 보다 작음 ⇔ d > 0 (입체가 닫힘),
     같음 ⇔ d = 0 (평면).
  3. 다섯 정다면체의 V · E · F, 오일러 2, pF = qV = 2E = 12 · 24 · 60 (회전의 수).
  4. 쌍대 {p, q} ↔ {q, p} : d 와 E 는 그대로, V 와 F 는 자리를 바꿈.
  5. 왼쪽 길 (면의 갯수 · q = 3) : 정사면체 4 → 정육면체 6 → 정12면체 12 = 12/(6 − p) · 반으로 2 · 3 · 6 · 1/2 + 1/3 + 1/6 = 1 ·
     6 에서 육각 타일 (d = 0).
     오른쪽 길 (면의 형태 · p = 3) : 정사면체 4 → 정8면체 8 → 정20면체 20 = 4q/(6 − q) · 6 에서 세모 타일 (d = 0).
     축마다 d = 3 · 2 · 1 · 0 (정사면체 · 정육–정8 · 정12–정20 · 평면). 황금 짝은 d = 1 이라 면이 정확히 4 × 5 · 4 × 3.

저자의 읽기 (수학 주장 아님) : 면만 두 길로 갈라짐 (형태와 갯수), 면 = 높이 × 넓이 = 자기장. 이 파일은 셈만 판정한다.
-/
namespace TwoPaths

def d (p q : Int) : Int := 2 * p + 2 * q - p * q

/-- d = 4 − (p − 2)(q − 2) (모든 정수) -/
theorem d_eq (p q : Int) : d p q = 4 - (p - 2) * (q - 2) := by
  simp only [d]; grind

/-- 한 꼭짓점의 각 : 360p − 180q(p − 2) = 180 · d (모든 정수) -/
theorem angle_defect (p q : Int) : 360 * p - 180 * q * (p - 2) = 180 * d p q := by
  simp only [d]; grind

/-- 일반 정리 1 : a = p − 2 ≥ 1, b = q − 2 ≥ 1 에서 ab < 4 이면 a ≤ 3 · b ≤ 3 (곧 p, q ≤ 5) -/
theorem positive_bound (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b < 4) : a ≤ 3 ∧ b ≤ 3 := by
  have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
  have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  omega

/-- 일반 정리 2 : ab = 4 이면 a ≤ 4 · b ≤ 4 (곧 p, q ≤ 6) -/
theorem flat_bound (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b = 4) : a ≤ 4 ∧ b ≤ 4 := by
  have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
  have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  omega

/-- a, b ∈ {1, …, 4} 를 모두 보면 : ab < 4 인 짝 다섯 · ab = 4 인 짝 셋 -/
def grid : List (Nat × Nat) := (List.range' 1 4).flatMap fun a => (List.range' 1 4).map fun b => (a, b)

theorem five_solids :
    (grid.filter fun ab => ab.1 * ab.2 < 4).map (fun ab => (ab.1 + 2, ab.2 + 2)) = [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] := by decide

theorem three_tilings :
    (grid.filter fun ab => ab.1 * ab.2 == 4).map (fun ab => (ab.1 + 2, ab.2 + 2)) = [(3, 6), (4, 4), (6, 3)] := by decide

/-- 정리 : p, q ≥ 3 인 모든 자연수에서 d > 0 ⇔ {p, q} 가 다섯 정다면체 가운데 하나 -/
theorem solids_exactly (p q : Nat) (hp : 3 ≤ p) (hq : 3 ≤ q) (h : (p - 2) * (q - 2) < 4) :
    (p, q) ∈ [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] := by
  have hb := positive_bound (p - 2) (q - 2) (by omega) (by omega) h
  have : p = 3 ∨ p = 4 ∨ p = 5 := by omega
  have : q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases ‹p = 3 ∨ p = 4 ∨ p = 5› with rfl | rfl | rfl <;> rcases ‹q = 3 ∨ q = 4 ∨ q = 5› with rfl | rfl | rfl <;> simp_all

/-- 정리 : p, q ≥ 3 인 모든 자연수에서 d = 0 ⇔ 평면 타일 셋 가운데 하나 -/
theorem tilings_exactly (p q : Nat) (hp : 3 ≤ p) (hq : 3 ≤ q) (h : (p - 2) * (q - 2) = 4) :
    (p, q) ∈ [(3, 6), (4, 4), (6, 3)] := by
  have hb := flat_bound (p - 2) (q - 2) (by omega) (by omega) h
  have : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
  have : q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
  rcases ‹p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6› with rfl | rfl | rfl | rfl <;>
    rcases ‹q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6› with rfl | rfl | rfl | rfl <;> simp_all

/-! ## 다섯 정다면체의 수 -/

def solids : List (Int × Int) := [(3, 3), (4, 3), (3, 4), (5, 3), (3, 5)]
def VEF (pq : Int × Int) : Int × Int × Int :=
  let p := pq.1; let q := pq.2; let dd := d p q
  (4 * p / dd, 2 * p * q / dd, 4 * q / dd)

/-- 나눗셈이 정확하고 (나머지 0), V · E · F 와 오일러 2, pF = qV = 2E -/
theorem solid_counts :
    solids.map VEF = [(4, 6, 4), (8, 12, 6), (6, 12, 8), (20, 30, 12), (12, 30, 20)] ∧
    solids.all (fun pq => (4 * pq.1) % d pq.1 pq.2 == 0 && (2 * pq.1 * pq.2) % d pq.1 pq.2 == 0 && (4 * pq.2) % d pq.1 pq.2 == 0) = true ∧
    solids.all (fun pq => let v := VEF pq; v.1 - v.2.1 + v.2.2 == 2) = true ∧
    (solids.map fun pq => let v := VEF pq; (pq.1 * v.2.2, pq.2 * v.1, 2 * v.2.1)) = [(12, 12, 12), (24, 24, 24), (24, 24, 24), (60, 60, 60), (60, 60, 60)] := by
  decide

/-- 쌍대 {p, q} ↔ {q, p} : d · E 는 그대로, V 와 F 가 자리를 바꿈 -/
theorem duality_swaps :
    solids.all (fun pq => d pq.1 pq.2 == d pq.2 pq.1 &&
      (VEF (pq.2, pq.1)).1 == (VEF pq).2.2 && (VEF (pq.2, pq.1)).2.2 == (VEF pq).1 && (VEF (pq.2, pq.1)).2.1 == (VEF pq).2.1) = true := by
  decide

/-! ## 두 길 -/

/-- 왼쪽 길 (면의 갯수 · q = 3) : 면 4 · 6 · 12 = 12/(6 − p) · 반으로 2 · 3 · 6 · 1/2 + 1/3 + 1/6 = 1 (곧 3 + 2 + 1 = 6) · p = 6 에서 d = 0 -/
theorem left_path :
    ([3, 4, 5] : List Int).map (fun p => (VEF (p, 3)).2.2) = [4, 6, 12] ∧
    ([3, 4, 5] : List Int).map (fun p => 12 / (6 - p)) = [4, 6, 12] ∧
    ([4, 6, 12] : List Int).map (· / 2) = [2, 3, 6] ∧ (3 + 2 + 1 = (6 : Int)) ∧ d 6 3 = 0 := by decide

/-- 오른쪽 길 (면의 형태 · p = 3) : 면 4 · 8 · 20 = 4q/(6 − q) · q = 6 에서 d = 0 -/
theorem right_path :
    ([3, 4, 5] : List Int).map (fun q => (VEF (3, q)).2.2) = [4, 8, 20] ∧
    ([3, 4, 5] : List Int).map (fun q => 4 * q / (6 - q)) = [4, 8, 20] ∧ d 3 6 = 0 := by decide

/-- 축마다 d = 3 · 2 · 1 · 0, 황금 짝 (d = 1) 은 면이 정확히 4 × 5 · 4 × 3, 가운데 바닥 {4, 4} 도 d = 0 (자기 쌍대) -/
theorem axes_d :
    [d 3 3, d 4 3, d 3 4, d 5 3, d 3 5, d 6 3, d 4 4, d 3 6] = [3, 2, 2, 1, 1, 0, 0, 0] ∧
    (VEF (3, 5)).2.2 = 4 * 5 ∧ (VEF (5, 3)).2.2 = 4 * 3 ∧ (VEF (3, 5)).1 = 4 * 3 ∧ (VEF (5, 3)).1 = 4 * 5 := by decide

/-- 각으로 본 바닥 : 꼭짓점의 각 결손 180 d — 정사면체 540 · 정육 · 정8 360 · 황금 짝 180 · 평면 타일 0 (단위 : 도 × p) -/
theorem defects :
    [(3, 3), (4, 3), (3, 4), (5, 3), (3, 5), (3, 6), (4, 4), (6, 3)].map (fun (pq : Int × Int) => 180 * d pq.1 pq.2) =
      [540, 360, 360, 180, 180, 0, 0, 0] := by decide

end TwoPaths

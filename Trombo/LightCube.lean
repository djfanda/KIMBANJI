/-
빛의 큐브 — 린 4 커널 확인 (Mathlib 없이, 린 코어만)

여덟 색을 F₂³ 의 점으로 둔다 : K = 0 · R = 1 · G = 2 · Y = 3 · B = 4 · M = 5 · C = 6 · W = 7
(세 채널 R · G · B 의 켜짐과 꺼짐 · 더하기는 XOR).
· 파노 평면 : 0 이 아닌 일곱 점과, XOR 해서 0 이 되는 세 점씩의 줄 일곱.
· 코어 W 를 지나는 줄 3 · 지나지 않는 줄 4 · 두 무리의 짝 12 는 육각형의 여섯 점에서 두 번씩 만남.
· 쌍대 a ↦ a^⊥ : 코어 줄 = 짝 점 {Y, M, C} 의 쌍대 · 나머지 = 홀 점 {R, G, B, W} 의 쌍대.
· 줄 + K = F₂³ 의 판(넷) — 덧셈으로 닫힘.
· 해밍 부호 [7, 4] : 자리 i (0 … 6) 의 검사 열 = 점 i + 1 · 부호어 16 · 최소 거리 3 · 완전 · 신드롬 = 틀린 자리의 빛
  · 무게 3 인 부호어 7 개의 받침 = 파노의 줄 7 개.
· 삼각형 7 + 큐브 8 = 사면체 15.
· 군의 크기 : |GL(3, F₂)| = 168 = |SL(2, F₇)| / 2 · |SL(2, F₃)| = 24 · |GL(2, F₃)| = 48 · |SL(2, F₅)| = 120 · |SL(2, F₁₁)| = 1320.
· 작은 카케야 수 : AG(2, q) 에서 방향 q + 1 개마다 줄 하나를 품는 가장 작은 집합 — q = 2, 3, 4, 5 에서 3, 7, 10, 17 (모든 고름을 셈).

검증 : lean 빛의큐브.lean  (린 v4.34.0 · decide +kernel · #print axioms 출력이 공리 목록)
-/

namespace Trombo.LightCube

/-! ## 비트 셈 -/

def bit (m i : Nat) : Bool := (m >>> i) % 2 == 1
def popF : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + popF k (n / 2)
def pop (n : Nat) : Nat := popF 64 n

/-! ## 파노 평면 -/

def pts : List Nat := [1, 2, 3, 4, 5, 6, 7]
/-- 줄 = 점 비트 모음 (비트 p 가 점 p) · 세 점 · K 없음 · XOR 합 0 -/
def ptsOf (m : Nat) : List Nat := pts.filter (bit m)
def isLine (m : Nat) : Bool := !(bit m 0) && (ptsOf m).length == 3 && (ptsOf m).foldl (· ^^^ ·) 0 == 0
def lines : List Nat := (List.range 256).filter isLine

theorem fano_seven_lines : lines.length = 7 := by decide +kernel
theorem fano_three_per_point : pts.all (fun p => lines.countP (fun m => bit m p) == 3) = true := by decide +kernel
theorem fano_one_line_per_pair :
    pts.all (fun p => pts.all (fun q => p == q || lines.countP (fun m => bit m p && bit m q) == 1)) = true := by decide +kernel
theorem fano_lines_meet_once :
    lines.all (fun l => lines.all (fun m => l == m || pop (l &&& m) == 1)) = true := by decide +kernel

/-! ## 코어 W = 7 : 줄 3 + 4 · 짝 12 · 만나는 곳 -/

def core : List Nat := lines.filter (fun m => bit m 7)
def rest : List Nat := lines.filter (fun m => !(bit m 7))
def meets : List Nat := core.flatMap (fun l => rest.map (fun m => l &&& m))

theorem core_three_rest_four : core.length = 3 ∧ rest.length = 4 := by decide +kernel
theorem twelve_pairs_meet_on_hexagon :
    meets.length = 12 ∧ meets.all (fun x => pop x == 1) = true ∧
    [1, 2, 3, 4, 5, 6].all (fun p => meets.countP (fun x => x == 1 <<< p) == 2) = true ∧
    meets.countP (fun x => x == 1 <<< 7) = 0 := by decide +kernel

/-! ## 쌍대 a ↦ a^⊥ = {v ≠ 0 : a · v = 0} -/

def perp (a : Nat) : Nat := (pts.filter (fun v => pop (a &&& v) % 2 == 0)).foldl (fun s v => s ||| (1 <<< v)) 0
def evenPts : List Nat := pts.filter (fun p => pop p % 2 == 0)
def oddPts : List Nat := pts.filter (fun p => pop p % 2 == 1)

theorem duality_even_core_odd_rest :
    evenPts = [3, 5, 6] ∧ oddPts = [1, 2, 4, 7] ∧
    evenPts.all (fun p => core.contains (perp p)) = true ∧ oddPts.all (fun p => rest.contains (perp p)) = true ∧
    pts.all (fun p => isLine (perp p)) = true := by decide +kernel

/-! ## 줄 + K = 판(넷) — XOR 로 닫힘 -/

theorem line_plus_K_is_plane :
    lines.all (fun m => let s := 0 :: ptsOf m; s.all (fun a => s.all (fun b => s.contains (a ^^^ b)))) = true := by decide +kernel

/-! ## 해밍 부호 [7, 4] -/

/-- 7 비트 말 w 의 신드롬 = 켜진 자리 i 의 (i + 1) 을 모두 XOR -/
def syn (w : Nat) : Nat := (List.range 7).foldl (fun s i => if bit w i then s ^^^ (i + 1) else s) 0
def code : List Nat := (List.range 128).filter (fun w => syn w == 0)
/-- 부호어의 받침을 점 비트로 : 자리 i → 점 i + 1 -/
def supp (w : Nat) : Nat := w <<< 1

theorem hamming_sixteen : code.length = 16 := by decide +kernel
theorem hamming_min_distance_three : code.all (fun c => c == 0 || pop c ≥ 3) = true := by decide +kernel
theorem hamming_perfect :
    (List.range 128).all (fun w => code.countP (fun c => pop (w ^^^ c) ≤ 1) == 1) = true ∧ 16 * (1 + 7) = 2 ^ 7 := by
  decide +kernel
theorem hamming_syndrome_names_position :
    code.all (fun c => (List.range 7).all (fun i => syn (c ^^^ (1 <<< i)) == i + 1)) = true := by decide +kernel
theorem hamming_weights :
    code.countP (fun c => pop c == 0) = 1 ∧ code.countP (fun c => pop c == 3) = 7 ∧
    code.countP (fun c => pop c == 4) = 7 ∧ code.countP (fun c => pop c == 7) = 1 := by decide +kernel
theorem hamming_weight_three_are_fano_lines :
    (code.filter (fun c => pop c == 3)).all (fun c => lines.contains (supp c)) = true ∧
    lines.all (fun m => (code.filter (fun c => pop c == 3)).contains (m >>> 1)) = true := by decide +kernel

/-! ## 삼각형 7 + 큐브 8 = 사면체 15 -/

theorem triangle_cube_tetrahedron :
    (List.range 8).countP (fun s => s != 0) = 7 ∧ (List.range 16).countP (fun s => bit s 3) = 8 ∧
    (List.range 16).countP (fun s => s != 0) = 15 := by decide +kernel

/-! ## 군의 크기 — 갈루아의 사다리 -/

def det3F2 (m : Nat) : Nat :=
  let e := fun i => (m >>> i) % 2
  (e 0 * (e 4 * e 8 + e 5 * e 7) + e 1 * (e 3 * e 8 + e 5 * e 6) + e 2 * (e 3 * e 7 + e 4 * e 6)) % 2
def sl2 (p : Nat) : Nat :=
  (List.range (p ^ 4)).countP fun k =>
    let a := k % p; let b := k / p % p; let c := k / (p * p) % p; let d := k / (p * p * p)
    (a * d + (p - b * c % p)) % p == 1
def gl2 (p : Nat) : Nat :=
  (List.range (p ^ 4)).countP fun k =>
    let a := k % p; let b := k / p % p; let c := k / (p * p) % p; let d := k / (p * p * p)
    (a * d + (p - b * c % p)) % p != 0

theorem group_orders :
    (List.range 512).countP (fun m => det3F2 m == 1) = 168 ∧ sl2 7 = 336 ∧ sl2 3 = 24 ∧ gl2 3 = 48 ∧
    sl2 5 = 120 ∧ sl2 11 = 1320 := by decide +kernel

/-! ## 작은 카케야 수 — 모든 고름 -/

/-- 체 F_q 의 덧셈 · 곱셈 (q = 4 는 F₂[α]/(α² + α + 1) : 0, 1, α = 2, α² = 3) -/
def addF (q a b : Nat) : Nat := if q == 4 then a ^^^ b else (a + b) % q
def mulF (q a b : Nat) : Nat :=
  if q == 4 then (if a == 0 || b == 0 then 0 else
      let lg := fun x => if x == 1 then 0 else if x == 2 then 1 else 2
      let ex := fun t => if t == 0 then 1 else if t == 1 then 2 else 3
      ex ((lg a + lg b) % 3))
  else a * b % q
/-- 점 (x, y) ↦ 비트 x·q + y · 세로줄 x = c · 기울기 줄 y = m x + c -/
def vline (q c : Nat) : Nat := (List.range q).foldl (fun s y => s ||| (1 <<< (c * q + y))) 0
def sline (q m c : Nat) : Nat := (List.range q).foldl (fun s x => s ||| (1 <<< (x * q + addF q (mulF q m x) c))) 0
/-- 고름 k (q 진법 q + 1 자리) : 첫 자리 = 세로줄 · 다음 자리들 = 기울기 0 … q − 1 의 줄 -/
def pick (q k : Nat) : Nat :=
  (List.range q).foldl (fun s m => s ||| sline q m (k / q ^ (m + 1) % q)) (vline q (k % q))
/-- 모든 고름의 최솟값 — 고름 번호 k = i · q^k₂ + j 를 두 겹으로 돌린다 (커널이 긴 목록 하나를 펼치지 않게) -/
def kakeyaMin (q : Nat) : Nat :=
  let k1 := (q + 1) / 2; let k2 := q + 1 - k1
  (List.range (q ^ k1)).foldl (fun b i => (List.range (q ^ k2)).foldl (fun b' j => min b' (pop (pick q (i * q ^ k2 + j)))) b) (q * q)

theorem kakeya_small : kakeyaMin 2 = 3 ∧ kakeyaMin 3 = 7 ∧ kakeyaMin 4 = 10 := by decide +kernel
/-- q = 5 : 모든 고름 15,625 가지가 17 점 이상(다섯 조각으로 나눠 셈)이고, 고름 31 이 정확히 17 점 (최솟값의 증인) -/
theorem kakeya_five_0 : (List.range 25).all (fun i => (List.range 125).all fun j => pop (pick 5 ((0 + i) * 125 + j)) ≥ 17) = true := by
  decide +kernel
theorem kakeya_five_1 : (List.range 25).all (fun i => (List.range 125).all fun j => pop (pick 5 ((25 + i) * 125 + j)) ≥ 17) = true := by
  decide +kernel
theorem kakeya_five_2 : (List.range 25).all (fun i => (List.range 125).all fun j => pop (pick 5 ((50 + i) * 125 + j)) ≥ 17) = true := by
  decide +kernel
theorem kakeya_five_3 : (List.range 25).all (fun i => (List.range 125).all fun j => pop (pick 5 ((75 + i) * 125 + j)) ≥ 17) = true := by
  decide +kernel
theorem kakeya_five_4 : (List.range 25).all (fun i => (List.range 125).all fun j => pop (pick 5 ((100 + i) * 125 + j)) ≥ 17) = true := by
  decide +kernel
theorem kakeya_five_witness : pop (pick 5 31) = 17 := by decide +kernel

#print axioms fano_seven_lines
#print axioms fano_three_per_point
#print axioms fano_one_line_per_pair
#print axioms fano_lines_meet_once
#print axioms core_three_rest_four
#print axioms twelve_pairs_meet_on_hexagon
#print axioms duality_even_core_odd_rest
#print axioms line_plus_K_is_plane
#print axioms hamming_sixteen
#print axioms hamming_min_distance_three
#print axioms hamming_perfect
#print axioms hamming_syndrome_names_position
#print axioms hamming_weights
#print axioms hamming_weight_three_are_fano_lines
#print axioms triangle_cube_tetrahedron
#print axioms group_orders
#print axioms kakeya_small
#print axioms kakeya_five_0
#print axioms kakeya_five_1
#print axioms kakeya_five_2
#print axioms kakeya_five_3
#print axioms kakeya_five_4
#print axioms kakeya_five_witness

end Trombo.LightCube

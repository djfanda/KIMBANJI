/-
사방치기 — 점 · 선 · 면적 · 부피의 틀과 판의 칸 (린 4 커널 · Mathlib 없이)

· 틀의 셈 (빨강 · 움직이지 않는 칸) : 사영 공간 Pⁿ(F_p) 의 점 = 1 + p + ⋯ + pⁿ (n = 1 선 · 2 면 · 3 부피) — p = 2, 3, 5, 7.
· 원(이차 곡선) x² + y² = z² 은 P²(F_p) 에서 점 p + 1 (선과 같은 셈) — p = 3, 5, 7, 11, 13.
· 면(이차 곡면) : xy = zw 는 (p + 1)² (= 선 × 선) — p = 2, 3, 5, 7.
  x² + y² + z² = w² 는 p ≡ 1 (mod 4) 이면 (p + 1)², p ≡ 3 (mod 4) 이면 p² + 1 — p = 3, 5, 7, 11, 13.
· 사방치기 판 3 · 4 · 5 · 6 칸 = 정 6 · 8 · 12 · 20 면체 (면의 수) — 쌍대 짝 (3, 4) · (5, 6) 은 꼭짓점 수와 면 수를 바꾼다.
· (2, 3, 7) : 1/2 + 1/3 + 1/7 = 41/42 이고, 2 ≤ p ≤ q ≤ r ≤ 60 에서 1/p + 1/q + 1/r < 1 인 것 가운데
  1 − (1/p + 1/q + 1/r) ≥ 1/42 이며 등호는 (2, 3, 7) 하나뿐.
· 말뚝박기 (비둘기집) : p = 2 … 13 에서 0 아닌 a 를 곱하는 사상은 모든 칸을 덮는다 (역원) · 6 에서 2 는 덮지 못한다 (2 × 3 = 0).
· 공기 (F₅) : 2 의 거듭제곱 1 → 2 → 4 → 3 → 1 · 1 × 2 × 3 × 4 ≡ −1 (윌슨 · p = 3 … 23).
· 윷 : 네 가락 = 4 비트 (16 가지) · p = 2/3 이면 모 · 도 · 개 · 걸 · 윷 = 1 · 8 · 24 · 32 · 16 (/81) — «걸 개 윷 도 모» 순서와 맞고, p = 3/5 이면 어긋난다.
· 세줄고누 (3 × 3 판) : 가로 3 · 세로 3 · 대각 2 의 여덟 줄은 모두 F₃² 의 줄이고, F₃² 의 줄은 12 개
  (감아 도는 대각 4 를 더함) · 두 칸마다 정확히 한 줄.

검증 : lean 사방치기.lean  (린 v4.34.0 · decide +kernel · #print axioms)
-/

namespace Trombo.Hopscotch

def digs (p k n : Nat) : List Nat := (List.range k).map fun i => n / p ^ i % p
def normalized (l : List Nat) : Bool := match l.find? (· != 0) with
  | some x => x == 1
  | none => false
def projCount (p k : Nat) : Nat := (List.range (p ^ k)).countP fun n => normalized (digs p k n)

theorem frame_counts : [2, 3, 5, 7].all (fun p =>
    projCount p 2 == p + 1 && projCount p 3 == p * p + p + 1 && projCount p 4 == p * p * p + p * p + p + 1) = true := by
  decide +kernel

def formCount (p k : Nat) (f : List Nat → Nat) : Nat := (List.range (p ^ k)).countP fun n => let l := digs p k n; normalized l && f l % p == 0
def sq (l : List Nat) (i : Nat) : Nat := l.getD i 0 * l.getD i 0

theorem circle_is_line : [3, 5, 7, 11, 13].all (fun p => formCount p 3 (fun l => sq l 0 + sq l 1 + (p - 1) * sq l 2) == p + 1) = true := by
  decide +kernel
theorem quadric_split : [2, 3, 5, 7].all (fun p =>
    formCount p 4 (fun l => l.getD 0 0 * l.getD 1 0 + (p - 1) * (l.getD 2 0 * l.getD 3 0)) == (p + 1) * (p + 1)) = true := by
  decide +kernel
theorem quadric_sphere : [3, 5, 7, 11, 13].all (fun p =>
    formCount p 4 (fun l => sq l 0 + sq l 1 + sq l 2 + (p - 1) * sq l 3) == (if p % 4 == 1 then (p + 1) * (p + 1) else p * p + 1)) = true := by
  decide +kernel

def solid (p q : Nat) : Nat × Nat × Nat :=
  let E := 2 * p * q / (4 - (p - 2) * (q - 2))
  (2 * E / q, E, 2 * E / p)
/-- 사방치기 판의 가운데 넷 : 3 = 정육면체 {4, 3} · 4 = 정팔면체 {3, 4} · 5 = 정십이면체 {5, 3} · 6 = 정이십면체 {3, 5} -/
theorem hopscotch_middle : [solid 4 3, solid 3 4, solid 5 3, solid 3 5].map (fun s => s.2.2) = [6, 8, 12, 20] ∧
    (solid 4 3).1 = (solid 3 4).2.2 ∧ (solid 3 4).1 = (solid 4 3).2.2 ∧
    (solid 5 3).1 = (solid 3 5).2.2 ∧ (solid 3 5).1 = (solid 5 3).2.2 := by decide +kernel

def hyp (p q r : Nat) : Bool := p * q + q * r + r * p < p * q * r
theorem two_three_seven : 21 + 14 + 6 = 41 ∧
    (List.range 61).all (fun p => (List.range 61).all fun q => (List.range 61).all fun r =>
      !(2 ≤ p && p ≤ q && q ≤ r && hyp p q r) ||
        (42 * (p * q * r - p * q - q * r - r * p) ≥ p * q * r &&
          ((42 * (p * q * r - p * q - q * r - r * p) == p * q * r) == (p == 2 && q == 3 && r == 7)))) = true := by
  decide +kernel

/-! ## 세줄고누 — 3 × 3 판 = F₃² -/

def pt (a b : Nat) : Nat := 3 * (a % 3) + b % 3
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys
def isort : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (isort xs)
def dedup (l : List (List Nat)) : List (List Nat) := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
def agLine (a b d1 d2 : Nat) : List Nat := isort ((List.range 3).map fun t => pt (a + t * d1) (b + t * d2))
def agLines : List (List Nat) :=
  dedup ([(1, 0), (0, 1), (1, 1), (1, 2)].flatMap fun (d1, d2) => (List.range 9).map fun n => agLine (n / 3) (n % 3) d1 d2)
def tictactoe : List (List Nat) := [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]]

theorem gonu_lines : agLines.length = 12 ∧ tictactoe.all (fun l => agLines.contains l) = true ∧
    (List.range 9).all (fun x => (List.range 9).all fun y => x == y || (agLines.countP fun l => l.contains x && l.contains y) == 1) = true := by
  decide +kernel

/-! ## 말뚝박기 — 비둘기집 : 유한하면 1 : 1 이 곧 전부 → 나눗셈이 선다 -/

/-- x ↦ a·x (mod n) 이 n 칸을 모두 덮는가 -/
def mulOnto (n a : Nat) : Bool := (List.range n).all fun y => (List.range n).any fun x => a * x % n == y
theorem malttuk_pigeonhole : [2, 3, 5, 7, 11, 13].all (fun p => (List.range p).all fun a => a == 0 || mulOnto p a) = true ∧
    mulOnto 6 2 = false ∧ 2 * 3 % 6 = 0 := by decide +kernel

/-! ## 공기 — F₅ 의 네 고리 (×2) 와 꺾기 (윌슨 : 0 아닌 것을 모두 곱하면 −1) -/

theorem gonggi_wilson : (List.range 5).map (fun k => 2 ^ k % 5) = [1, 2, 4, 3, 1] ∧ 1 * 2 * 3 * 4 % 5 = 5 - 1 ∧
    [3, 5, 7, 11, 13, 17, 19, 23].all (fun p => (List.range p).foldl (fun s k => if k == 0 then s else s * k % p) 1 == p - 1) = true := by
  decide +kernel

/-! ## 윷놀이 — 네 가락 = 4 비트, 젖혀질 확률 p = 2/3 이면 도 · 개 · 걸 · 윷 · 모 = 8 · 24 · 32 · 16 · 1 (분모 81 = 3⁴) -/

def choose4 (k : Nat) : Nat := [1, 4, 6, 4, 1].getD k 0
/-- 젖혀진 가락 k 개의 무게 (p = a/(a + b)) : C(4, k) aᵏ b⁴⁻ᵏ -/
def yutW (a b k : Nat) : Nat := choose4 k * a ^ k * b ^ (4 - k)
theorem yut_two_thirds : (List.range 5).map (yutW 2 1) = [1, 8, 24, 32, 16] ∧ ((List.range 5).map (yutW 2 1)).foldl (· + ·) 0 = 81 ∧
    -- 걸 > 개 > 윷 > 도 > 모 (p = 2/3 이면 맞고, p = 3/5 이면 걸 = 개 · 도 > 윷 으로 어긋남)
    (yutW 2 1 3 > yutW 2 1 2 && yutW 2 1 2 > yutW 2 1 4 && yutW 2 1 4 > yutW 2 1 1 && yutW 2 1 1 > yutW 2 1 0) = true ∧
    (List.range 5).map (yutW 3 2) = [16, 96, 216, 216, 81] ∧ (2 ^ 4 = 16) := by decide +kernel

#print axioms frame_counts
#print axioms circle_is_line
#print axioms quadric_split
#print axioms quadric_sphere
#print axioms hopscotch_middle
#print axioms two_three_seven
#print axioms gonu_lines
#print axioms malttuk_pigeonhole
#print axioms gonggi_wilson
#print axioms yut_two_thirds

end Trombo.Hopscotch

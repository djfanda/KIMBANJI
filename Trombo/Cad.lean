/-
캐드 — 큐브의 알갱이를 정확히 세는 린 4 커널 확인 (Mathlib 없이)
· n × n × n 격자를 점 하나하나로 펼쳐 센다 : 점 · 단위 선분 · 단위 정사각형 · 단위 칸
· 3 × 3 × 3 : 64 · 144 · 108 · 27, 오일러 수 1, 합 343 = 7³, 조각 27 = 꼭짓점 8 + 모서리 12 + 면 6 + 가운데 1,
  겉면 54 · 속면 54(양쪽에서 세면 108) · 27 × 6 = 54 + 2 × 54
· 모든 n : (n+1)³ + 3n(n+1)² + 3n²(n+1) + n³ = (2n+1)³ 이고 점 + 정사각형 = 선분 + 칸 + 1 (오일러 수 1)
· 공의 부피 도미노의 대수 부분 : κ₂ₘ = πᵐ/m! · κ₂ₘ₊₁ = 2ᵐ⁺¹πᵐ/(2m+1)!! 가 모든 m 에서 κₙ = (2π/n)κₙ₋₂ 를 만족
  (자르기 적분 ∫₀¹(1 − r²)^((n−2)/2) r dr = 1/n 은 해석학이라 이 파일 밖)
· 정사면체의 꼭짓점 τ = (1 + √−3)/2 : τ² − τ + 1 = 0 (교차비 e^(iπ/3) 의 대수식) · 실수부 ½
-/

namespace Trombo.Cad

def allPts (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range (n + 1)).flatMap fun x => (List.range (n + 1)).flatMap fun y => (List.range (n + 1)).map fun z => (x, y, z)

def b2n (b : Bool) : Nat := if b then 1 else 0

def points (n : Nat) : Nat := (allPts n).length
def edges (n : Nat) : Nat :=
  (allPts n).foldl (fun s p => s + b2n (p.1 < n) + b2n (p.2.1 < n) + b2n (p.2.2 < n)) 0
def squares (n : Nat) : Nat :=
  (allPts n).foldl (fun s p => s + b2n (p.1 < n && p.2.1 < n) + b2n (p.1 < n && p.2.2 < n) + b2n (p.2.1 < n && p.2.2 < n)) 0
def cells (n : Nat) : Nat :=
  (allPts n).foldl (fun s p => s + b2n (p.1 < n && p.2.1 < n && p.2.2 < n)) 0

theorem cad_3 : points 3 = 64 ∧ edges 3 = 144 ∧ squares 3 = 108 ∧ cells 3 = 27 := by decide +kernel
theorem cad_3_euler_sum : points 3 + squares 3 = edges 3 + cells 3 + 1 ∧
    points 3 + edges 3 + squares 3 + cells 3 = 7 ^ 3 := by decide +kernel
/-- 펼쳐 센 수가 공식과 같다 (n = 0 … 6) -/
theorem cad_counts_small : ∀ n : Fin 7, points n.val = (n.val + 1) ^ 3 ∧ edges n.val = 3 * n.val * (n.val + 1) ^ 2 ∧
    squares n.val = 3 * n.val ^ 2 * (n.val + 1) ∧ cells n.val = n.val ^ 3 := by decide +kernel
/-- 모든 n : 네 수의 합은 (2n+1)³ -/
theorem cad_sum_formula (n : Nat) : (n + 1) ^ 3 + 3 * n * (n + 1) ^ 2 + 3 * n ^ 2 * (n + 1) + n ^ 3 = (2 * n + 1) ^ 3 := by grind
/-- 모든 n : 오일러 수 1 — 점 + 정사각형 = 선분 + 칸 + 1 -/
theorem cad_euler_formula (n : Nat) : (n + 1) ^ 3 + 3 * n ^ 2 * (n + 1) = 3 * n * (n + 1) ^ 2 + n ^ 3 + 1 := by grind

/-! 3 × 3 × 3 의 조각 27 — 바깥에 드러난 면의 수로 가른다 -/

def exposed (c : Nat × Nat × Nat) : Nat := b2n (c.1 == 0 || c.1 == 2) + b2n (c.2.1 == 0 || c.2.1 == 2) + b2n (c.2.2 == 0 || c.2.2 == 2)
def cubies : List (Nat × Nat × Nat) := (allPts 2)
def countExposed (k : Nat) : Nat := (cubies.filter fun c => exposed c == k).length

theorem cubies_8_12_6_1 : countExposed 3 = 8 ∧ countExposed 2 = 12 ∧ countExposed 1 = 6 ∧ countExposed 0 = 1 := by decide +kernel
/-- 겉면 54 = 각 조각의 드러난 면의 합 · 속면은 54 개(양쪽에서 세면 108) · 27 × 6 = 54 + 2 × 54 -/
theorem faces_54_108 : (cubies.map exposed).foldl (· + ·) 0 = 54 ∧ squares 3 - 54 = 54 ∧ 27 * 6 = 54 + 2 * 54 := by decide +kernel

/-! 공의 부피 도미노 — 대수 부분 -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
def dfact : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * dfact n

/-- 짝수 걸음 : κ₂ₘ₊₂ = (2π/(2m+2)) κ₂ₘ  ⇔  (2m + 2) · m! = 2 · (m + 1)! -/
theorem domino_even (m : Nat) : (2 * m + 2) * fact m = 2 * fact (m + 1) := by
  simp only [fact]; grind
/-- 홀수 걸음 : κ₂ₘ₊₃ = (2π/(2m+3)) κ₂ₘ₊₁  ⇔  2^(m+2) · (2m+3) · (2m+1)!! = 2 · 2^(m+1) · (2m+3)!! -/
theorem domino_odd (m : Nat) : 2 ^ (m + 2) * ((2 * m + 3) * dfact (2 * m + 1)) = 2 * 2 ^ (m + 1) * dfact (2 * m + 3) := by
  have h : dfact (2 * m + 3) = (2 * m + 3) * dfact (2 * m + 1) := rfl
  rw [h]; grind

/-! 정사면체의 꼭짓점 — 아이젠슈타인 수 x + y√−3 를 정수 짝으로 -/

def emul (a b : Int × Int) : Int × Int := (a.1 * b.1 - 3 * a.2 * b.2, a.1 * b.2 + a.2 * b.1)
/-- 2τ = 1 + √−3 이므로 4(τ² − τ + 1) = (2τ)² − 2·(2τ) + 4 = 0 -/
theorem tau_equianharmonic :
    let t : Int × Int := (1, 1)
    (emul t t).1 - 2 * t.1 + 4 = 0 ∧ (emul t t).2 - 2 * t.2 = 0 := by decide

#print axioms cad_3
#print axioms cad_3_euler_sum
#print axioms cad_counts_small
#print axioms cad_sum_formula
#print axioms cad_euler_formula
#print axioms cubies_8_12_6_1
#print axioms faces_54_108
#print axioms domino_even
#print axioms domino_odd
#print axioms tau_equianharmonic

end Trombo.Cad

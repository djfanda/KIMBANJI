/-
유한 큐브 쪽 리만 — 린 4 커널 확인 (Mathlib 없이, 린 코어만)

· 하세 부등식(유한체 위 타원곡선의 리만 가설) : 소수 p = 3, 5, 7, 11, 13, 17, 19, 23 에서
  y² = x³ + ax + b (a, b ∈ F_p) 의 매끈한 곡선 모두가 a_p² < 4p 를 만족한다 (a_p = p + 1 − N, N = 사영 점의 수).
  (하세 1933 · 베유 1948 의 정리 — 이 파일은 그 정리를 쓰지 않고 곡선 하나하나를 센다.)
· 꽉 참(도이링) : p = 5 … 23 에서 a² < 4p 인 정수 a 가 모두 어느 곡선의 a_p 로 나타난다.
· 제곱의 평행이동 : F₇ 의 제곱 {1, 2, 4} 의 평행이동 일곱 = 두 점마다 정확히 하나 (파노 평면) ·
  F₁₁ 의 제곱 {1, 3, 4, 5, 9} 의 평행이동 열하나 = 두 점마다 정확히 둘 (쌍평면).
· 홈과 돌기 : 2 ≤ n ≤ 32 에서 «n 이 소수 거듭제곱» 과 «n 원소 위의 체 곱셈표가 있다» 는 곧바로 셀 수 없으므로,
  여기서는 소수 거듭제곱의 목록만 셈으로 적는다.

검증 : lean 유한체리만.lean  (린 v4.34.0 · decide +kernel · #print axioms)
-/

namespace Trombo.FiniteRiemann

def powMod (b e m : Nat) : Nat := (List.range e).foldl (fun s _ => s * b % m) 1
/-- 르장드르 기호 (오일러 판정) -/
def chiP (p c : Nat) : Int := if c % p == 0 then 0 else if powMod (c % p) ((p - 1) / 2) p == 1 then 1 else -1
/-- a_p = −Σₓ χ(x³ + ax + b) (= p + 1 − N) -/
def trace (p a b : Nat) : Int := - (List.range p).foldl (fun s x => s + chiP p (x * x * x + a * x + b)) 0
def smoothE (p a b : Nat) : Bool := (4 * a * a * a + 27 * b * b) % p != 0
def hasseAll (p : Nat) : Bool :=
  (List.range p).all fun a => (List.range p).all fun b => !(smoothE p a b) || decide (trace p a b * trace p a b < 4 * (p : Int))
def fullRange (p : Nat) : Bool :=
  (List.range (2 * p + 1)).all fun k =>
    let t : Int := (k : Int) - (p : Int)
    !(decide (t * t < 4 * (p : Int))) || (List.range p).any fun a => (List.range p).any fun b => smoothE p a b && trace p a b == t

theorem hasse_small : hasseAll 3 = true ∧ hasseAll 5 = true ∧ hasseAll 7 = true ∧ hasseAll 11 = true ∧ hasseAll 13 = true := by
  decide +kernel
theorem hasse_more : hasseAll 17 = true ∧ hasseAll 19 = true ∧ hasseAll 23 = true := by decide +kernel
theorem full_range : fullRange 5 = true ∧ fullRange 7 = true ∧ fullRange 11 = true ∧ fullRange 13 = true := by decide +kernel
theorem full_range_more : fullRange 17 = true ∧ fullRange 19 = true ∧ fullRange 23 = true := by decide +kernel

/-! ## 제곱의 평행이동 — 파노 (7, 3, 1) · 쌍평면 (11, 5, 2) -/

def squares (p : Nat) : List Nat := ((List.range p).filter (· != 0)).filter fun c => chiP p c == 1
def blocks (p : Nat) : List (List Nat) := (List.range p).map fun t => (squares p).map fun s => (s + t) % p
def pairCount (p x y : Nat) : Nat := (blocks p).countP fun bl => bl.contains x && bl.contains y

theorem squares_7_11 : squares 7 = [1, 2, 4] ∧ squares 11 = [1, 3, 4, 5, 9] := by decide +kernel
theorem fano_from_F7 : (List.range 7).all (fun x => (List.range 7).all fun y => x == y || pairCount 7 x y == 1) = true := by
  decide +kernel
theorem biplane_from_F11 : (List.range 11).all (fun x => (List.range 11).all fun y => x == y || pairCount 11 x y == 2) = true := by
  decide +kernel

/-! ## 돌기(소수 거듭제곱) 목록 2 … 32 -/

def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range n).all fun d => d < 2 || n % d != 0
def isPrimePower (n : Nat) : Bool :=
  (List.range (n + 1)).any fun p => isPrime p && (List.range 6).any fun k => p ^ (k + 1) == n
theorem tabs_and_grooves :
    ((List.range 33).filter fun n => n ≥ 2 && isPrimePower n) = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32] ∧
    ((List.range 33).filter fun n => n ≥ 2 && !(isPrimePower n)) = [6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30] := by
  decide +kernel

#print axioms hasse_small
#print axioms hasse_more
#print axioms full_range
#print axioms full_range_more
#print axioms squares_7_11
#print axioms fano_from_F7
#print axioms biplane_from_F11
#print axioms tabs_and_grooves

end Trombo.FiniteRiemann

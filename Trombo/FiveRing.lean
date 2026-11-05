/-
다섯 보석 반지 — 정다면체는 다섯뿐 · 처음 다섯 피보나치 소수 (린 4 코어 · Mathlib 없음)
정다면체 {p, q} (면이 정 p 각형 · 꼭짓점마다 q 개) 가 서려면 꼭짓점의 각의 합이 한 바퀴보다 작아야 하고,
그 조건은 (p − 2)(q − 2) < 4 (p, q ≥ 3) 이다(고전 · 전언). 이 정수 부등식의 해가 꼭 다섯임을 커널이 센다.
-/
namespace FiveRing

def sols : List (Nat × Nat) :=
  ((List.range 10).flatMap fun p => (List.range 10).map fun q => (p, q)).filter
    fun (p, q) => 3 ≤ p && 3 ≤ q && (p - 2) * (q - 2) < 4

/-- p, q < 10 안에서 해는 꼭 다섯 : 정사면체 {3,3} · 정팔면체 {3,4} · 정20면체 {3,5} · 정육면체 {4,3} · 정12면체 {5,3} -/
theorem five_solids : sols = [(3,3), (3,4), (3,5), (4,3), (5,3)] := by decide

/-- 10 이상은 볼 필요가 없다 : p ≥ 6 이면 (p − 2)(q − 2) ≥ 4 · 1 = 4 -/
theorem no_large (p q : Nat) (hp : 6 ≤ p) (hq : 3 ≤ q) : 4 ≤ (p - 2) * (q - 2) :=
  calc 4 = 4 * 1 := rfl
    _ ≤ (p - 2) * (q - 2) := Nat.mul_le_mul (by omega) (by omega)

def fib : Nat → Nat
  | 0 => 0 | 1 => 1 | n + 2 => fib n + fib (n + 1)

def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

set_option maxRecDepth 20000 in
/-- 피보나치 수 F₀ … F₁₃ (233 까지) 가운데 소수는 2 · 3 · 5 · 13 · 89 · 233 — 100 아래는 꼭 다섯 -/
theorem five_golden_primes :
    ((List.range 14).map fib).filter (fun n => isPrime n && n < 100) = [2, 3, 5, 13, 89] := by decide +kernel

end FiveRing

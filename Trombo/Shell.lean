/-
껍질 — 안에서 보는 면과 밖에서 보는 면 (린 4 코어 · Mathlib 없음)
n × n × n 큐브를 단위 조각 n³ 개로 자르면, 밖으로 드러난 단위 면은 6n² 개, 조각 사이에 숨은 단위 면은 3n²(n − 1) 개다.
숨은 면 = 드러난 면 이 되는 크기는 n = 3 하나뿐 — 3 × 3 × 3 (조각 27 = 꼭짓점 8 + 모서리 12 + 면 6 + 가운데 1) 에서 안에서 보는 면 54 와
밖에서 보는 면 54 가 꼭 같다. n < 3 이면 안이 작고, n > 3 이면 안이 크다.
-/
namespace Shell

def outside (n : Nat) : Nat := 6 * n * n
def inside (n : Nat) : Nat := 3 * n * n * (n - 1)

theorem three : outside 3 = 54 ∧ inside 3 = 54 := by decide

/-- 숨은 면과 드러난 면이 같은 크기는 n = 3 뿐 (n ≥ 1) -/
theorem equal_iff (n : Nat) (h : 1 ≤ n) : inside n = outside n ↔ n = 3 := by
  unfold inside outside
  constructor
  · intro e
    have hn : 0 < n * n := Nat.mul_pos h h
    have : 3 * (n * n) * (n - 1) = 3 * (n * n) * 2 := by
      have e' : 3 * n * n * (n - 1) = 6 * n * n := e
      calc 3 * (n * n) * (n - 1) = 3 * n * n * (n - 1) := by rw [Nat.mul_assoc 3 n n]
        _ = 6 * n * n := e'
        _ = 3 * (n * n) * 2 := by rw [Nat.mul_assoc 6 n n, Nat.mul_comm 3 (n * n), Nat.mul_assoc (n*n) 3 2, Nat.mul_comm (n*n) 6]
    have h3 : 0 < 3 * (n * n) := by omega
    have := Nat.eq_of_mul_eq_mul_left h3 this
    omega
  · intro e; subst e; decide

/-- 조각 27 의 갈래 : 드러난 면이 3 · 2 · 1 · 0 개인 조각 수 8 · 12 · 6 · 1 -/
theorem pieces : 8 + 12 + 6 + 1 = 27 ∧ 8 * 3 + 12 * 2 + 6 * 1 + 1 * 0 = 54 := by decide

/-- 가운데 조각의 여섯 면은 모두 숨은 면 — 숨은 면 54 가운데 6 (= 1/9) -/
theorem center_share : 6 * 9 = 54 := by decide

end Shell

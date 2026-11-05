/-
스물넷 — 소수 큐브의 세 부호 · 색 큐브 · 팔원수 첨자 · 파노 평면 (린 4 코어, Mathlib 없이)
· sq_mod_24 : 6 과 서로소인 모든 자연수 n 에서 n² ≡ 1 (mod 24)
· sgn_mul   : 6 과 서로소인 모든 a, b 에서 세 부호는 곱을 XOR 로 옮긴다 — (ℤ/24)^× → (ℤ/2)³ 의 준동형
· sgn_units : 24 의 여덟 줄이 세 비트의 여덟 꼴과 하나씩 맞는다 (K B G C R M Y W)
· oct_index_xor : 팔원수 단위의 곱 eᵢeⱼ = ± e_(i XOR j) (64 칸)
· assoc_on_lines : 서로 다른 허수 단위 세 쌍 가운데 결합자가 0 인 것은 42 개이고 모두 파노 줄 {i, j, i XOR j} 위
· fano_seven : 파노 평면의 줄은 일곱
-/

namespace Trombo.TwentyFour

theorem sq_mod_24 (n : Nat) (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) : n ^ 2 % 24 = 1 := by
  have key : ∀ r, r < 24 → r % 2 = 1 → r % 3 ≠ 0 → r ^ 2 % 24 = 1 := by decide
  rw [Nat.pow_mod]
  exact key (n % 24) (Nat.mod_lt _ (by decide)) (by omega) (by omega)

/-- 세 부호 : (n ≡ 2 mod 3, n ≡ 3 mod 4, n ≡ 3 또는 5 mod 8) — 차례로 −3 · −1 · 2 가 비제곱인 줄 -/
def sgn (n : Nat) : Bool × Bool × Bool := (n % 3 == 2, n % 4 == 3, n % 8 == 3 || n % 8 == 5)

def bxor3 (a b : Bool × Bool × Bool) : Bool × Bool × Bool := (a.1 ^^ b.1, a.2.1 ^^ b.2.1, a.2.2 ^^ b.2.2)

theorem sgn_mod24 (n : Nat) : sgn n = sgn (n % 24) := by
  have h3 : n % 24 % 3 = n % 3 := by omega
  have h4 : n % 24 % 4 = n % 4 := by omega
  have h8 : n % 24 % 8 = n % 8 := by omega
  simp only [sgn, h3, h4, h8]

theorem sgn_mul (a b : Nat) (ha2 : a % 2 = 1) (ha3 : a % 3 ≠ 0) (hb2 : b % 2 = 1) (hb3 : b % 3 ≠ 0) :
    sgn (a * b) = bxor3 (sgn a) (sgn b) := by
  have key : ∀ r s : Fin 24, r.val % 2 = 1 → r.val % 3 ≠ 0 → s.val % 2 = 1 → s.val % 3 ≠ 0 →
      sgn (r.val * s.val % 24) = bxor3 (sgn r.val) (sgn s.val) := by decide
  rw [sgn_mod24 (a * b), sgn_mod24 a, sgn_mod24 b, Nat.mul_mod]
  exact key ⟨a % 24, Nat.mod_lt _ (by decide)⟩ ⟨b % 24, Nat.mod_lt _ (by decide)⟩
    (show a % 24 % 2 = 1 by omega) (show a % 24 % 3 ≠ 0 by omega)
    (show b % 24 % 2 = 1 by omega) (show b % 24 % 3 ≠ 0 by omega)

/-- 24 의 여덟 줄 1 · 5 · 7 · 11 · 13 · 17 · 19 · 23 → 세 비트(색 K · B · G · C · R · M · Y · W 의 비트 꼴) -/
theorem sgn_units :
    [1, 5, 7, 11, 13, 17, 19, 23].map sgn =
      [(false, false, false), (true, false, true), (false, true, false), (true, true, true),
       (false, false, true), (true, false, false), (false, true, true), (true, true, false)] := by decide

/-! 팔원수 — 케일리–딕슨 곱 (a, b)(c, d) = (ac − d̄b, da + bc̄) -/

def conj : List Int → List Int
  | [] => []
  | a :: t => a :: t.map (fun z => -z)

def cd : Nat → List Int → List Int → List Int
  | 0, x, y => [x.headD 0 * y.headD 0]
  | k + 1, x, y =>
    let h := 2 ^ k
    let a := x.take h; let b := x.drop h; let c := y.take h; let d := y.drop h
    List.zipWith (· - ·) (cd k a c) (cd k (conj d) b) ++ List.zipWith (· + ·) (cd k d a) (cd k b (conj c))

def unit (i n : Nat) : List Int := (List.range n).map fun j => if j = i then 1 else 0

theorem oct_index_xor : ∀ i, i < 8 → ∀ j, j < 8 →
    (cd 3 (unit i 8) (unit j 8) = unit (i ^^^ j) 8 ∨
     cd 3 (unit i 8) (unit j 8) = (unit (i ^^^ j) 8).map (fun z => -z)) := by decide +kernel

def assocZero (i j k : Nat) : Bool :=
  cd 3 (cd 3 (unit i 8) (unit j 8)) (unit k 8) == cd 3 (unit i 8) (cd 3 (unit j 8) (unit k 8))

/-- 서로 다른 허수 단위 (i, j, k) (차례 있음) 가운데 결합자가 0 인 것은 정확히 42 개 -/
def assocCount : Nat :=
  ((List.range 7).map (· + 1)).foldl (fun s i =>
    ((List.range 7).map (· + 1)).foldl (fun s j =>
      ((List.range 7).map (· + 1)).foldl (fun s k =>
        if i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ assocZero i j k then s + 1 else s) s) s) 0

theorem assoc_count_42 : assocCount = 42 := by decide +kernel

/-- 그 42 개는 모두 파노 줄 위 (k = i XOR j) -/
theorem assoc_on_lines : ∀ i j k : Fin 8,
    (0 < i.val ∧ 0 < j.val ∧ 0 < k.val ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ assocZero i.val j.val k.val = true) →
      k.val = i.val ^^^ j.val := by
  decide +kernel

/-- 파노 평면 : 1 ≤ i < j < k ≤ 7 이고 i XOR j = k 인 세 쌍(줄)은 일곱 -/
def fanoLines : List (Nat × Nat × Nat) :=
  ((List.range 8).flatMap fun i => (List.range 8).flatMap fun j => (List.range 8).filterMap fun k =>
    if 0 < i ∧ i < j ∧ j < k ∧ i ^^^ j = k then some (i, j, k) else none)

theorem fano_seven : fanoLines = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)] := by
  decide +kernel

#print axioms sq_mod_24
#print axioms sgn_mul
#print axioms sgn_units
#print axioms oct_index_xor
#print axioms assoc_count_42
#print axioms assoc_on_lines
#print axioms fano_seven

end Trombo.TwentyFour

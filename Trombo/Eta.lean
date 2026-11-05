/-
에타의 걸음 — 홀수 +, 짝수 −, 루트의 걸음으로 0 점을 찾다 (린 4 코어 · Mathlib 없이 · import 없음)

η(s) = Σ_{n≥1} (−1)^(n+1) n^(−s) = 1 − 2^(−s) + 3^(−s) − 4^(−s) + ⋯ = (1 − 2^(1−s)) ζ(s)   (Re s > 0 에서 수렴)

여기서 커널로 확인하는 것 :
· 계수 항등식 (일반 정리) : (1 − 2·2^(−s)) Σ n^(−s) 에서 n^(−s) 의 계수 — 홀수면 1, 짝수면 1 − 2 — 는
  모든 n ≥ 1 에서 (−1)^(n+1). 약수 합 (디리클레 곱) 으로 직접 센 계수도 n = 1 … 300 에서 같다.
· 시작점 : 첫 항은 1 (= √1) — 계수 · 조화수 H(1) · 교대 부분합 S_1 모두 1, r · r = 1 인 자연수 r 은 1 뿐.
· 오렘 (c. 1350 · 전언) : 조화수 H(N) 을 정확한 분수 (분자, 분모) 로 세어 k = 0 … 10 에서 2·H(2^k) ≥ 2 + k,
  덩어리 H(2^k) − H(2^(k−1)) ≥ ½ (k = 1 … 10) — 모두 교차 곱.
· 교대 부분합 S_N = Σ_{n ≤ N} (−1)^(n+1)/n 의 둥지 : m ≤ 40 에서
  S_2 < S_4 < ⋯ < S_(2m) < S_(2m−1) < ⋯ < S_3 < S_1,  S_(2m−1) − S_(2m) = 1/(2m).
· 짝수를 두 번 빼면 : S_N = H(N) − H(⌊N/2⌋) (N = 0 … 80) — ζ(1) 의 두 부분합의 차가 η(1) 의 부분합.

정직 : ζ(1) = ∞ (모든 k) 와 η(1) = log 2 는 해석학의 정리이고 여기서는 유한 범위만 커널로 센다.
리만 가설 (ζ 의 띠 안 영점이 모두 Re s = ½ 위) 은 열린 물음 □ 이며 이 파일이 다루지 않는다.

검증 : lean 에타.lean  (린 v4.34.0 · decide +kernel · 끝의 #print axioms 가 공리 목록)
-/

namespace Trombo.Eta

/-! ## 계수 항등식 — 홀수 +, 짝수 − -/

/-- (1 − 2·2^(−s)) Σ n^(−s) 에서 n^(−s) 의 계수 : ζ 에서 오는 1 에, 짝수면 2·2^(−s) ζ(s) 에서 오는 −2 를 더한다 -/
def coeff (n : Nat) : Int := if n % 2 = 1 then 1 else 1 - 2

/-- 정수의 거듭제곱 한 걸음 : b^(e+1) = b^e · b (코어의 Int.pow_succ) -/
theorem pow_succ_int (b : Int) (e : Nat) : b ^ (e + 1) = b ^ e * b := Int.pow_succ b e

/-- (−1)^(2m) = 1 -/
theorem neg_one_pow_two_mul (m : Nat) : (-1 : Int) ^ (2 * m) = 1 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pow_succ_int, pow_succ_int, ih]
    decide

/-- 계수 항등식 (일반 정리) : 모든 n ≥ 1 에서 «n 홀수면 1, 짝수면 1 − 2» = (−1)^(n+1) -/
theorem coeff_eq_neg_one_pow (n : Nat) (_hn : 1 ≤ n) : coeff n = (-1 : Int) ^ (n + 1) := by
  unfold coeff
  split
  next h =>
    -- 홀수 : n + 1 = 2·(n/2 + 1) → (−1)^(짝수) = 1
    rw [show n + 1 = 2 * (n / 2 + 1) by omega, neg_one_pow_two_mul]
  next h =>
    -- 짝수 : n + 1 = 2·(n/2) + 1 → (−1)^(홀수) = −1 = 1 − 2
    rw [show n + 1 = 2 * (n / 2) + 1 by omega, pow_succ_int, neg_one_pow_two_mul]
    decide

/-- 홀수 걸음은 +1, 짝수 걸음은 −1 (모든 m) -/
theorem odd_plus_even_minus (m : Nat) : coeff (2 * m + 1) = 1 ∧ coeff (2 * m + 2) = -1 := by
  constructor
  · unfold coeff
    split
    next => rfl
    next h => omega
  · unfold coeff
    split
    next h => omega
    next => decide

/-- 디리클레 곱의 계수 : (Σ a(d) d^(−s)) · (Σ b(m) m^(−s)) 에서 n^(−s) 의 계수 = Σ_{d ∣ n} a(d) · b(n/d) -/
def dirichlet_coeff (a b : Nat → Int) (n : Nat) : Int :=
  (List.range n).foldl (fun acc i => if n % (i + 1) == 0 then acc + a (i + 1) * b (n / (i + 1)) else acc) 0

/-- 1 − 2·2^(−s) 의 계수 : d = 1 에서 1, d = 2 에서 −2, 나머지 0 -/
def factor_two (d : Nat) : Int := if d == 1 then 1 else if d == 2 then -2 else 0

/-- ζ(s) = Σ n^(−s) 의 계수 : 모두 1 -/
def zeta_coeff (_ : Nat) : Int := 1

/-- 약수 합으로 직접 센 계수 = coeff — n = 1 … 300 -/
theorem dirichlet_product_coeff :
    (List.range 300).all (fun i => dirichlet_coeff factor_two zeta_coeff (i + 1) == coeff (i + 1)) = true := by
  decide +kernel

/-! ## 정확한 분수 — 조화수 H(N) 과 교대 부분합 S_N -/

/-- 자연수 분수 (p, q) 의 약분 -/
def reduce_nat (p q : Nat) : Nat × Nat := (p / Nat.gcd p q, q / Nat.gcd p q)

/-- 조화수 H(N) = 1 + 1/2 + ⋯ + 1/N — 정확한 분수 (분자, 분모), 걸음마다 약분 -/
def harmonic (N : Nat) : Nat × Nat :=
  (List.range N).foldl (fun acc i => reduce_nat (acc.1 * (i + 1) + acc.2) (acc.2 * (i + 1))) (0, 1)

/-- 정수 분자 · 자연수 분모 분수의 약분 -/
def reduce_int (p : Int) (q : Nat) : Int × Nat :=
  (p / ((Nat.gcd p.natAbs q : Nat) : Int), q / Nat.gcd p.natAbs q)

/-- 교대 부분합 S_N = Σ_{n ≤ N} coeff(n)/n = 1 − 1/2 + 1/3 − ⋯ ± 1/N — 정확한 분수 (정수 분자, 분모) -/
def alt_sum (N : Nat) : Int × Nat :=
  (List.range N).foldl (fun acc i =>
    reduce_int (acc.1 * ((i + 1 : Nat) : Int) + coeff (i + 1) * (acc.2 : Int)) (acc.2 * (i + 1))) (0, 1)

/-- 분수 x < y (분모 양수) — 교차 곱 -/
def lt_q (x y : Int × Nat) : Bool := decide (x.1 * (y.2 : Int) < y.1 * (x.2 : Int))
/-- 분수 x = y — 교차 곱 -/
def eq_q (x y : Int × Nat) : Bool := x.1 * (y.2 : Int) == y.1 * (x.2 : Int)
/-- 분수 x − y -/
def sub_q (x y : Int × Nat) : Int × Nat := (x.1 * (y.2 : Int) - y.1 * (x.2 : Int), x.2 * y.2)
/-- 자연수 분수를 정수 분자 분수로 -/
def to_q (x : Nat × Nat) : Int × Nat := ((x.1 : Int), x.2)

/-! ## 시작점 — 첫 항은 1 (= √1) -/

/-- r · r = 1 인 자연수 r 은 1 뿐 : √1 = 1 -/
theorem sqrt_one_is_one : ∀ r : Nat, r * r = 1 → r = 1
  | 0, h => by omega
  | 1, _ => rfl
  | r + 2, h => by
    have : 2 * 2 ≤ (r + 2) * (r + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- 시작점 : 첫 계수 1 · (−1)^(1+1) = 1 · H(1) = 1 · S_1 = 1 · 약수 합의 첫 계수 1 -/
theorem start_point :
    coeff 1 = 1 ∧ (-1 : Int) ^ (1 + 1) = 1 ∧ harmonic 1 = (1, 1) ∧ alt_sum 1 = (1, 1) ∧
      dirichlet_coeff factor_two zeta_coeff 1 = 1 := by
  decide +kernel

/-- 작은 값 : H(2) = 3/2 · H(3) = 11/6 · H(4) = 25/12 · S_2 = 1/2 · S_3 = 5/6 · S_4 = 7/12 -/
theorem small_values :
    harmonic 2 = (3, 2) ∧ harmonic 3 = (11, 6) ∧ harmonic 4 = (25, 12) ∧
      alt_sum 2 = (1, 2) ∧ alt_sum 3 = (5, 6) ∧ alt_sum 4 = (7, 12) := by
  decide +kernel

/-! ## 오렘 (c. 1350 · 전언) — 1 이 무한대 -/

/-- 2·H(2^k) ≥ 2 + k, 곧 H(2^k) ≥ 1 + k/2 — k = 0 … 10 (교차 곱 : (2 + k)·분모 ≤ 2·분자) -/
theorem oresme_doubling :
    (List.range 11).all (fun k => (2 + k) * (harmonic (2 ^ k)).2 ≤ 2 * (harmonic (2 ^ k)).1) = true := by
  decide +kernel

/-- 덩어리 H(2^(i+1)) − H(2^i) ≥ ½ — i = 0 … 9 (교차 곱 : a₂b₂ + 2a₁b₂ ≤ 2b₁a₂) -/
theorem oresme_blocks :
    (List.range 10).all (fun i =>
      (harmonic (2 ^ i)).2 * (harmonic (2 ^ (i + 1))).2 + 2 * ((harmonic (2 ^ i)).1 * (harmonic (2 ^ (i + 1))).2)
        ≤ 2 * ((harmonic (2 ^ (i + 1))).1 * (harmonic (2 ^ i)).2)) = true := by
  decide +kernel

/-! ## 교대 부분합의 둥지 — η(1) 의 걸음 -/

/-- 둥지 사슬의 번호 : 2, 4, …, 2m, 2m − 1, …, 3, 1 -/
def nest_chain (m : Nat) : List Nat :=
  (List.range m).map (fun j => 2 * j + 2) ++ (List.range m).reverse.map (fun j => 2 * j + 1)

/-- 분수 목록이 엄격히 오르는가 -/
def strictly_increasing : List (Int × Nat) → Bool
  | x :: y :: rest => lt_q x y && strictly_increasing (y :: rest)
  | _ => true

/-- 둥지 (m = 1 … 40) : S_2 < S_4 < ⋯ < S_(2m) < S_(2m−1) < ⋯ < S_3 < S_1 -/
theorem alternating_nest :
    (List.range 40).all (fun i => strictly_increasing ((nest_chain (i + 1)).map alt_sum)) = true := by
  decide +kernel

/-- 이웃한 두 부분합의 차 : S_(2m−1) − S_(2m) = 1/(2m) — m = 1 … 40 -/
theorem alternating_gap :
    (List.range 40).all (fun i => eq_q (sub_q (alt_sum (2 * i + 1)) (alt_sum (2 * i + 2))) (1, 2 * i + 2)) = true := by
  decide +kernel

/-- 짝수를 두 번 빼면 : S_N = H(N) − H(⌊N/2⌋) — N = 0 … 80 -/
theorem twice_even_removed :
    (List.range 81).all (fun N => eq_q (alt_sum N) (sub_q (to_q (harmonic N)) (to_q (harmonic (N / 2))))) = true := by
  decide +kernel

#print axioms pow_succ_int
#print axioms neg_one_pow_two_mul
#print axioms coeff_eq_neg_one_pow
#print axioms odd_plus_even_minus
#print axioms dirichlet_product_coeff
#print axioms sqrt_one_is_one
#print axioms start_point
#print axioms small_values
#print axioms oresme_doubling
#print axioms oresme_blocks
#print axioms alternating_nest
#print axioms alternating_gap
#print axioms twice_even_removed

end Trombo.Eta

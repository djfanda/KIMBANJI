/-
황금비와 소수 — 루트 5 의 다리 (린 4 코어만 · Mathlib 없음 · 커널 확인)
φ = (1 + √5)/2 의 거듭제곱은 피보나치 F · 뤼카 L 수로 적힌다 : φⁿ = (Lₙ + Fₙ√5)/2.
소수 p (p ≠ 2, 5) 에서 고전 정리(뤼카 1878 · 전언)는
  (5/p) = (p/5) (이차 상호 법칙의 한 사례 · 5 가 p 를 법으로 제곱수인가는 p mod 5 가 정한다)
  Fₚ ≡ (5/p) (mod p) · Lₚ ≡ 1 (mod p) · F_{p − (5/p)} ≡ 0 (mod p)
이 파일은 p < 2000 의 모든 소수에서 네 줄을 커널로 확인한다(② 유한 확인 — 모든 소수의 일반 증명은 아님).
(5/p) 는 오일러 판정 5^((p−1)/2) mod p 로 따로 셈하여 p mod 5 와 맞댄다.
-/
namespace GoldenPrime

/-- (Fₙ mod m, Fₙ₊₁ mod m) -/
def fib2 (m : Nat) : Nat → Nat × Nat
  | 0 => (0, 1 % m)
  | n + 1 => let q := fib2 m n; (q.2, (q.1 + q.2) % m)

/-- (Lₙ mod m, Lₙ₊₁ mod m) -/
def luc2 (m : Nat) : Nat → Nat × Nat
  | 0 => (2 % m, 1 % m)
  | n + 1 => let q := luc2 m n; (q.2, (q.1 + q.2) % m)

def powMod (b e m : Nat) : Nat := Nat.pow b e % m

/-- 2 ≤ d ≤ fuel 인 d 가운데 p 를 나누는 것이 있는가 -/
def hasDiv (p : Nat) : Nat → Bool
  | 0 => false
  | 1 => false
  | d + 1 => (p % (d + 1) == 0 && d + 1 < p) || hasDiv p d

/-- p ≤ 2000 이면 45² > p 이므로 약수 후보는 45 까지면 충분하다 -/
def isPrime (p : Nat) : Bool := p ≥ 2 && !hasDiv p 45

/-- 네 줄 : 오일러 판정 = p mod 5 의 규칙 · Fₚ ≡ (5/p) · Lₚ ≡ 1 · F_{p−(5/p)} ≡ 0 -/
def ok (p : Nat) : Bool :=
  let r := p % 5
  let qr := r == 1 || r == 4                       -- (p/5) = +1
  let e := powMod 5 ((p - 1) / 2) p                -- 오일러 : 1 이면 +1, p − 1 이면 −1
  let euler := if qr then e == 1 else e == p - 1
  let fp := (fib2 p p).1
  let fline := if qr then fp == 1 else fp == p - 1
  let lline := (luc2 p p).1 == 1
  let zline := (fib2 p (if qr then p - 1 else p + 1)).1 == 0
  euler && fline && lline && zline

def allUpTo : Nat → Bool
  | 0 => true
  | n + 1 => (if isPrime (n + 1) && n + 1 ≠ 2 && n + 1 ≠ 5 then ok (n + 1) else true) && allUpTo n

def countPrimes : Nat → Nat
  | 0 => 0
  | n + 1 => (if isPrime (n + 1) && n + 1 ≠ 2 && n + 1 ≠ 5 then 1 else 0) + countPrimes n

set_option maxRecDepth 100000 in
theorem golden_prime_lines : allUpTo 2000 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem golden_prime_count : countPrimes 2000 = 301 := by decide +kernel

/-- 반대 시험 : 합성수 21 에서는 Lₙ ≡ 1 줄이 깨진다(소수에서만 서는 문장) -/
theorem composite_fails : (luc2 21 21).1 ≠ 1 := by decide +kernel

end GoldenPrime

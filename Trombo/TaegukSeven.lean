/-
태극 아리랑 — q = 7 조각 (린 4 커널 · Mathlib 없이)
F₇ 위 모든 바이어슈트라스 식 7⁵ = 16807 개를 a1 = 0 … 6 의 일곱 조각으로 나누어,
조각마다 흠 있는 식이 7³ = 343 개이고 매끈한 곡선의 대각합이 모두 A7 = {−5, …, 5} 안에 있음을 센다.
A7 의 모든 a 가 a² ≤ 28 이고 a 마다 증인 곡선이 있다는 것은 태극아리랑.lean (box_lists · witnesses).
검증 : lean 태극아리랑_칠.lean
-/

namespace Trombo.TaegukSeven

/-! ## 체 -/

structure Fld where
  q : Nat
  add : Nat → Nat → Nat
  mul : Nat → Nat → Nat
  one : Nat → Nat

def primeF (p : Nat) : Fld := ⟨p, fun a b => (a + b) % p, fun a b => (a * b) % p, fun n => n % p⟩
def gf4mul (a b : Nat) : Nat := ([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD a []).getD b 0
def gf4 : Fld := ⟨4, fun a b => a ^^^ b, gf4mul, fun n => n % 2⟩
/-- F₉ = F₃[i] : 원소 u + 3v ↔ u + v·i -/
def gf9add (a b : Nat) : Nat := (a % 3 + b % 3) % 3 + 3 * ((a / 3 + b / 3) % 3)
def gf9mul (a b : Nat) : Nat := (a % 3 * (b % 3) + 2 * (a / 3) * (b / 3)) % 3 + 3 * ((a % 3 * (b / 3) + a / 3 * (b % 3)) % 3)
def gf9 : Fld := ⟨9, gf9add, gf9mul, fun n => n % 3⟩

/-! ## 바이어슈트라스 식 -/

def lhs (K : Fld) (a1 a3 x y : Nat) : Nat := K.add (K.add (K.mul y y) (K.mul a1 (K.mul x y))) (K.mul a3 y)
def rhs (K : Fld) (a2 a4 a6 x : Nat) : Nat := K.add (K.add (K.add (K.mul x (K.mul x x)) (K.mul a2 (K.mul x x))) (K.mul a4 x)) a6
def onC (K : Fld) (a1 a2 a3 a4 a6 x y : Nat) : Bool := lhs K a1 a3 x y == rhs K a2 a4 a6 x
def gradZero (K : Fld) (a1 a2 a3 a4 x y : Nat) : Bool :=
  K.mul a1 y == K.add (K.add (K.mul (K.one 3) (K.mul x x)) (K.mul (K.one 2) (K.mul a2 x))) a4 &&
  K.add (K.add (K.mul (K.one 2) y) (K.mul a1 x)) a3 == 0
def countN (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Nat :=
  1 + (List.range K.q).foldl (fun s x => s + (List.range K.q).countP fun y => onC K a1 a2 a3 a4 a6 x y) 0
def singular (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Bool :=
  (List.range K.q).any fun x => (List.range K.q).any fun y => onC K a1 a2 a3 a4 a6 x y && gradZero K a1 a2 a3 a4 x y
def traceA (K : Fld) (a1 a2 a3 a4 a6 : Nat) : Int := ((K.q + 1 : Nat) : Int) - ((countN K a1 a2 a3 a4 a6 : Nat) : Int)

/-- 조각 (a1 고정) : 매끈하면 대각합이 목록 안 -/
def chunkOK (K : Fld) (aset : List Int) (a1 : Nat) : Bool :=
  (List.range K.q).all fun a2 => (List.range K.q).all fun a3 => (List.range K.q).all fun a4 => (List.range K.q).all fun a6 =>
    singular K a1 a2 a3 a4 a6 || aset.contains (traceA K a1 a2 a3 a4 a6)
def chunkSing (K : Fld) (a1 : Nat) : Nat :=
  (List.range K.q).foldl (fun s a2 => s + (List.range K.q).foldl (fun t a3 => t + (List.range K.q).foldl
    (fun u a4 => u + (List.range K.q).countP fun a6 => singular K a1 a2 a3 a4 a6) 0) 0) 0
def boxAll (q : Nat) (aset : List Int) : Bool := aset.all fun a => decide (a * a ≤ 4 * (q : Int))
def witOK (K : Fld) (w : List (Int × List Nat)) : Bool :=
  w.all fun (a, e) => match e with
    | [a1, a2, a3, a4, a6] => !(singular K a1 a2 a3 a4 a6) && traceA K a1 a2 a3 a4 a6 == a
    | _ => false

def A2 : List Int := [-2, -1, 0, 1, 2]
def A3 : List Int := [-3, -2, -1, 0, 1, 2, 3]
def A4 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
def A5 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
def A7 : List Int := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]


theorem taeguk_seven_0 : chunkOK (primeF 7) A7 0 = true ∧ chunkSing (primeF 7) 0 = 343 := by decide +kernel
theorem taeguk_seven_1 : chunkOK (primeF 7) A7 1 = true ∧ chunkSing (primeF 7) 1 = 343 := by decide +kernel
theorem taeguk_seven_2 : chunkOK (primeF 7) A7 2 = true ∧ chunkSing (primeF 7) 2 = 343 := by decide +kernel
theorem taeguk_seven_3 : chunkOK (primeF 7) A7 3 = true ∧ chunkSing (primeF 7) 3 = 343 := by decide +kernel
theorem taeguk_seven_4 : chunkOK (primeF 7) A7 4 = true ∧ chunkSing (primeF 7) 4 = 343 := by decide +kernel
theorem taeguk_seven_5 : chunkOK (primeF 7) A7 5 = true ∧ chunkSing (primeF 7) 5 = 343 := by decide +kernel
theorem taeguk_seven_6 : chunkOK (primeF 7) A7 6 = true ∧ chunkSing (primeF 7) 6 = 343 := by decide +kernel

#print axioms taeguk_seven_0
#print axioms taeguk_seven_1
#print axioms taeguk_seven_2
#print axioms taeguk_seven_3
#print axioms taeguk_seven_4
#print axioms taeguk_seven_5
#print axioms taeguk_seven_6

end Trombo.TaegukSeven

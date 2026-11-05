/-
클라인 4 차 곡선의 점 세기 — 유한한 소수 범위에서 커널이 센다 (린 4 코어만 · Mathlib 없음)

고전 사실 (이름만 대고 여기서 증명하지 않음) :
  클라인(1879)의 4 차 곡선 C : x³y + y³z + z³x = 0 (종수 3) 의 야코비안 J 는
  유리수체 위에서 타원곡선 E = 49a1 : y² + xy = x³ − x² − 2x − 1 을 실 원분체 K = Q(ζ₇)⁺ 에서
  Q 로 내린 바일 제한 Res_{K/Q} E 와 동종이고, K 위에서는 E³ 과 동종이다.
  그 결과로 좋은 소수 p (p ≠ 7) 마다
      #C(F_p) = p + 1 − a_p(E) · (1 + χ(p) + χ(p)²)
  가 성립한다. 여기서 χ 는 법 7 의 세제곱 지표이고, 1 + χ(p) + χ(p)² 은 p ≡ ±1 (법 7) 이면 3, 아니면 0 이다.
  (Q 위에서 J ~ E³ 이라고 두면 틀린다 : p = 11 에서 #C = 12 인데 p + 1 − 3a_p = 0 이다. E³ 은 K 위에서만.)

이 모듈이 커널로 확인하는 것 :
  1. 사영 평면 P²(F_p) 의 C 위 점 수 #C(F_p) 를 정규화된 대표로 직접 센다
     (z = 1 인 점 · z = 0 이고 y = 1 인 점 · [1 : 0 : 0]).
  2. E 의 아핀 해를 직접 세고 무한원점 하나를 더해 #E(F_p) 를 얻고, a_p = p + 1 − #E(F_p) 로 둔다.
  3. 법 7 의 세제곱 지표 χ 를 아이젠슈타인 정수 ℤ[ω] 의 값으로 적고, 곱셈적이며 자명하지 않고
     세제곱이 1 임을, 그리고 1 + χ + χ² 이 3 또는 0 임을 여섯 나머지 모두에서 확인한다.
  4. 위 등식을 2 ≤ p < 400 인 모든 소수 p ≠ 7 (77 개) 에서 확인한다 (정리 `klein_count_lt_400`).
     커널 확인은 열네 구간으로 나눠 세 모듈에 두었다 : 이 모듈은 2 ≤ p < 167 ,
     `Trombo.KleinCount2` 는 167 ≤ p < 307 , `Trombo.KleinCount3` 는 307 ≤ p < 400 과 모아 놓은 정리.
     (구간 하나가 커널 메모리를 약 2.2 GB 쓴다. 병렬 정교화를 꺼서 한 번에 한 구간만 확인한다.)
     나쁜 소수 7 은 등식 없이 점 수만 적는다 : #C(F_7) = 8 , #E(F_7) = 8 .
  5. p = 2, 3, 5 에서는 F_p[t]/(f) 를 직접 만들고 (0 아닌 원소마다 역원이 있음을 확인해 체임을 보인다),
     #C(F_{p^k}) (k = 1, 2, 3) 를 세어 뉴턴 항등식으로 6 차 특성다항식을 얻은 뒤,
     모형 Π_{t ∈ {1, χ(p), χ(p)²}} (T² − a_p t T + p t²) 와 계수까지 같음을 확인한다.
     (특성다항식은 함수 등식 꼴 [1, −c₁, c₂, −c₃, p c₂, −p² c₁, p³] 을 가정하고 k ≤ 3 의 거듭제곱 합에서 정한다.
     F₁₂₅ 는 목록 방식으로 세면 커널 메모리가 넘쳐서, 원소를 자연수 하나로 적는 빠른 곱으로 세고,
     그 빠른 곱이 목록 곱과 F₈ · F₂₇ 의 모든 짝에서 같음을 따로 확인했다.
     11 · 13 처럼 F_{p³} 가 큰 소수는 커널 비용 때문에 하지 않았다.)

계산 방식 : 세는 함수는 `Nat.rec` 와 `Nat.add` · `Nat.mul` · `Nat.mod` · `Nat.beq` 를 직접 써서
커널이 큰 수 산술을 바로 쓰게 했다. `native_decide` 는 쓰지 않는다.

여기서 하지 않는 것 : 야코비안의 분해(동종)는 증명하지 않는다. 확인하는 것은 적힌 유한 범위의
점 세기 등식뿐이며, 모든 소수에 대한 등식도 아니다. 호지 추측 일반에 대해서는 아무것도 주장하지 않는다.
-/
namespace Trombo.KleinCount

-- 커널 확인을 한 번에 하나씩 하도록 병렬 정교화를 끈다 (메모리 상한 때문)
set_option Elab.async false

/-! ## 1. F_p 위의 점 세기 (자연수 산술 · 나머지 p) -/

/-- 클라인 곡선 z = 1 조각의 한 줄 : 고정된 x (x³ 은 미리 계산해 x3) 에 대해
y (x³ + y²) + x = x³y + y³ + x ≡ 0 (법 p) 인 y < n 의 수 -/
def kleinRow (p x x3 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun y acc => Nat.add acc
      (cond (Nat.beq (Nat.mod (Nat.add (Nat.mul y (Nat.add x3 (Nat.mul y y))) x) p) 0) 1 0)) n

/-- z = 1 조각 전체 : x < n 의 줄을 모두 더함 -/
def kleinAff (p n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.add acc (kleinRow p x (Nat.mod (Nat.mul x (Nat.mul x x)) p) p)) n

/-- z = 0 · y = 1 조각 : 식이 x³ = 0 이 되므로 x³ ≡ 0 인 x < n 의 수 -/
def kleinInf (p n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.add acc (cond (Nat.beq (Nat.mod (Nat.mul x (Nat.mul x x)) p) 0) 1 0)) n

/-- #C(F_p) : z = 1 인 점 + (z = 0, y = 1) 인 점 + [1 : 0 : 0] (z = y = 0 이면 식이 늘 0) -/
def kleinN (p : Nat) : Nat := kleinAff p p + kleinInf p p + 1

/-- 타원곡선 49a1 의 한 줄 : y² + xy = x³ − x² − 2x − 1 을 뺄셈 없이
y (y + x) + (x + 1)² ≡ x³ (법 p) 로 적고, 그런 y < n 의 수 (c = (x + 1)² mod p , x3 = x³ mod p) -/
def ellRow (p x c x3 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun y acc => Nat.add acc
      (cond (Nat.beq (Nat.mod (Nat.add (Nat.mul y (Nat.add y x)) c) p) x3) 1 0)) n

def ellAff (p n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.add acc
      (ellRow p x (Nat.mod (Nat.mul (Nat.add x 1) (Nat.add x 1)) p) (Nat.mod (Nat.mul x (Nat.mul x x)) p) p)) n

/-- #E(F_p) : 아핀 해 + 무한원점 하나 -/
def ellN (p : Nat) : Nat := ellAff p p + 1

/-- a_p = p + 1 − #E(F_p) -/
def ap (p : Nat) : Int := (p : Int) + 1 - (ellN p : Int)

/-- 뺄셈 없이 적은 식이 원래 식과 같다 : y² + xy + (x + 1)² = x³ ⇔ y² + xy = x³ − x² − 2x − 1 (정수에서) -/
theorem ell_rewrite (x y : Int) :
    y * (y + x) + (x + 1) * (x + 1) - x * (x * x) = (y * y + x * y) - (x * x * x - x * x - 2 * x - 1) := by
  grind

/-- 클라인 식의 z = 1 조각 : x³·y + y³·1 + 1³·x = y (x³ + y²) + x -/
theorem klein_rewrite (x y : Int) : x * x * x * y + y * y * y * 1 + 1 * 1 * 1 * x = y * (x * (x * x) + y * y) + x := by
  grind

/-! ## 2. 아이젠슈타인 정수와 법 7 의 세제곱 지표 -/

/-- a + bω , ω² = −1 − ω -/
structure Eis where
  a : Int
  b : Int
deriving DecidableEq, Repr

def Eis.add (x y : Eis) : Eis := ⟨x.a + y.a, x.b + y.b⟩
def Eis.neg (x : Eis) : Eis := ⟨-x.a, -x.b⟩
/-- (a + bω)(c + dω) = (ac − bd) + (ad + bc − bd)ω -/
def Eis.mul (x y : Eis) : Eis := ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩
def Eis.ofInt (n : Int) : Eis := ⟨n, 0⟩

def ω : Eis := ⟨0, 1⟩
def one : Eis := ⟨1, 0⟩

/-- 법 7 의 세제곱 지표 : 생성원 3 (3⁰, 3¹, …, 3⁵ ≡ 1, 3, 2, 6, 4, 5) 에 대해 χ(3^k) = ω^k .
7 의 배수에는 0 -/
def chi (n : Nat) : Eis :=
  match n % 7 with
  | 1 => one
  | 6 => one
  | 3 => ω
  | 4 => ω
  | 2 => Eis.mul ω ω
  | 5 => Eis.mul ω ω
  | _ => ⟨0, 0⟩

/-- ω² + ω + 1 = 0 , ω³ = 1 -/
theorem omega_rel : (Eis.mul ω ω).add (ω.add one) = ⟨0, 0⟩ ∧ Eis.mul (Eis.mul ω ω) ω = one := by decide

/-- 3 은 법 7 의 생성원 : 3⁰ … 3⁵ 의 나머지가 1, 3, 2, 6, 4, 5 로 모두 다르다 -/
theorem three_generates : (List.range 6).map (fun k => 3 ^ k % 7) = [1, 3, 2, 6, 4, 5] := by decide

/-- χ 는 곱셈적이다 : 1 ≤ a, b ≤ 6 의 서른여섯 짝 모두 χ(ab) = χ(a) χ(b) -/
theorem chi_mul : (List.range 7).all (fun a => (List.range 7).all (fun b =>
    a == 0 || b == 0 || chi (a * b) == Eis.mul (chi a) (chi b))) = true := by decide

/-- χ 는 세제곱 지표다 : χ(a)³ = 1 (a = 1 … 6) 이고 χ(3) = ω ≠ 1 (자명하지 않음) -/
theorem chi_cube : (List.range 7).all (fun a => a == 0 || Eis.mul (Eis.mul (chi a) (chi a)) (chi a) == one) = true ∧
    chi 3 ≠ one := by decide

/-- χ(a) = 1 인 a 는 정확히 세제곱수 ±1 (법 7) 이다 -/
theorem chi_kernel : (List.range 7).filter (fun a => chi a == one) = [1, 6] ∧
    ((List.range 7).filter (fun a => a != 0)).map (fun a => a ^ 3 % 7) = [1, 1, 6, 1, 6, 6] := by decide

/-- 1 + χ(n) + χ(n)² -/
def chiSum (n : Nat) : Eis := (one.add (chi n)).add (Eis.mul (chi n) (chi n))

/-- 정수로 읽은 1 + χ(p) + χ(p)² -/
def chiSumInt (p : Nat) : Int := if p % 7 == 1 || p % 7 == 6 then 3 else 0

/-- 7 과 서로소인 p 에서 1 + χ(p) + χ(p)² 은 허수부가 0 이고, p ≡ ±1 (법 7) 이면 3, 아니면 0 -/
theorem chiSum_eq (p : Nat) (h : p % 7 ≠ 0) : chiSum p = Eis.ofInt (chiSumInt p) := by
  have hr : p % 7 < 7 := Nat.mod_lt _ (by decide)
  have key : ∀ r, r < 7 → r ≠ 0 →
      chiSum r = Eis.ofInt (if r % 7 == 1 || r % 7 == 6 then 3 else 0) := by decide
  have e1 : chiSum p = chiSum (p % 7) := by simp [chiSum, chi]
  have e2 : chiSumInt p = (if p % 7 % 7 == 1 || p % 7 % 7 == 6 then 3 else 0) := by
    simp [chiSumInt]
  rw [e1, e2]
  exact key _ hr h

/-! ## 3. 소수 판정과 범위 확인의 건전성 -/

/-- 2 ≤ d < m 인 d 가 하나도 n 을 나누지 않으면 true -/
def divFree (n m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun d acc => and acc (or (Nat.blt d 2) (not (Nat.beq (Nat.mod n d) 0)))) m

theorem divFree_succ (n m : Nat) :
    divFree n (m + 1) = (divFree n m && (Nat.blt m 2 || !Nat.beq (n % m) 0)) := rfl

/-- `Nat.beq a b = false` 는 a ≠ b 와 같다 (코어에 이 이름의 보조정리가 없어 직접 증명) -/
theorem beq_false_iff (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · exact Nat.ne_of_beq_eq_false
  · intro h
    cases hb : Nat.beq a b with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem divFree_iff (n m : Nat) : divFree n m = true ↔ ∀ d, d < m → 2 ≤ d → n % d ≠ 0 := by
  induction m with
  | zero => exact ⟨fun _ d hd => absurd hd (Nat.not_lt_zero d), fun _ => rfl⟩
  | succ m ih =>
    rw [divFree_succ, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff, ih]
    constructor
    · intro hh d hd h2d
      by_cases hdm : d = m
      · subst hdm
        cases hh.2 with
        | inl h => exact absurd h (by omega)
        | inr h => exact h
      · exact hh.1 d (by omega) h2d
    · intro h
      refine ⟨fun d hd h2d => h d (by omega) h2d, ?_⟩
      by_cases hm : m < 2
      · exact Or.inl hm
      · exact Or.inr (h m (by omega) (by omega))

/-- 소수 판정 (나눗셈 시도) -/
def isPrimeB (n : Nat) : Bool := Nat.ble 2 n && divFree n n

/-- 소수 (명제) -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem isPrimeB_of_prime {p : Nat} (hp : Prime p) : isPrimeB p = true := by
  unfold isPrimeB
  rw [Bool.and_eq_true, divFree_iff, Nat.ble_eq]
  refine ⟨hp.1, fun d hd h2d h0 => ?_⟩
  cases hp.2 d (Nat.dvd_of_mod_eq_zero h0) with
  | inl h => omega
  | inr h => omega

/-- 한 소수에서 맞출 등식 : #C(F_p) = p + 1 − a_p (1 + χ(p) + χ(p)²) -/
def kleinOK (p : Nat) : Bool := (kleinN p : Int) == (p : Int) + 1 - ap p * chiSumInt p

/-- lo ≤ p < lo + n 인 소수 p ≠ 7 모두에서 kleinOK -/
def checkFrom (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => checkFrom lo n && (!(isPrimeB (lo + n) && !Nat.beq (lo + n) 7) || kleinOK (lo + n))

theorem checkFrom_sound (lo n : Nat) (h : checkFrom lo n = true) :
    ∀ p, lo ≤ p → p < lo + n → Prime p → p ≠ 7 →
      (kleinN p : Int) = (p : Int) + 1 - ap p * chiSumInt p := by
  induction n with
  | zero => intro p h1 h2; omega
  | succ n ih =>
    simp only [checkFrom, Bool.and_eq_true] at h
    intro p h1 h2 hp h7
    by_cases hpn : p = lo + n
    · subst hpn
      have hb : isPrimeB (lo + n) = true := isPrimeB_of_prime hp
      have h7' : Nat.beq (lo + n) 7 = false := (beq_false_iff _ _).mpr h7
      have := h.2
      rw [hb, h7'] at this
      simpa [kleinOK] using this
    · exact ih h.1 p h1 (by omega) hp h7

/-- 정수 등식을 ℤ[ω] 값의 χ 로 옮기기 : 7 과 서로소인 p 에서 정수 등식이 서면
#C(F_p) = p + 1 − a_p (1 + χ(p) + χ(p)²) 이 ℤ[ω] 에서도 선다 -/
theorem eis_of_int (p : Nat) (h7 : p % 7 ≠ 0)
    (h : (kleinN p : Int) = (p : Int) + 1 - ap p * chiSumInt p) :
    Eis.ofInt (kleinN p) = (Eis.ofInt ((p : Int) + 1)).add (Eis.neg (Eis.mul (Eis.ofInt (ap p)) (chiSum p))) := by
  rw [chiSum_eq p h7, h]
  simp only [Eis.ofInt, Eis.add, Eis.neg, Eis.mul, Eis.mk.injEq]
  constructor <;> omega

/-- 7 이 아닌 소수는 7 로 나누어떨어지지 않는다 -/
theorem mod7_ne_zero {p : Nat} (hp : Prime p) (h7 : p ≠ 7) : p % 7 ≠ 0 := by
  intro h0
  cases hp.2 7 (Nat.dvd_of_mod_eq_zero h0) with
  | inl h => omega
  | inr h => omega

/-! ## 4. 커널 확인 (구간을 나눠서 · 이 모듈에는 2 ≤ p < 167 만 · 나머지는 `KleinCount2` · `KleinCount3`) -/

theorem chunk_2_167 : checkFrom 2 165 = true := by decide +kernel

/-- 범위 안 소수의 수 : 2 ≤ p < 400 의 소수는 78 개, 7 을 빼면 77 개 -/
def primeCount : Nat → Nat
  | 0 => 0
  | n + 1 => primeCount n + (if isPrimeB n then 1 else 0)

theorem prime_count_400 : primeCount 400 = 78 := by decide +kernel

/-- 나쁜 소수 7 (E 와 C 모두 나쁜 환원) : 등식 없이 점 수만 -/
theorem bad_prime_seven : kleinN 7 = 8 ∧ ellN 7 = 8 ∧ ap 7 = 0 := by decide +kernel

/-- 예 : p = 11 (χ ≠ 1) 은 #C = 12 = 12 − 4·0 , p = 29 (χ = 1) 은 #C = 24 = 30 − 2·3 , p = 43 은 #C = 80 = 44 + 12·3 -/
theorem examples :
    (kleinN 11, ap 11) = (12, 4) ∧ (kleinN 29, ap 29) = (24, 2) ∧ (kleinN 43, ap 43) = (80, -12) := by
  decide +kernel

/-! ## 5. 작은 소수의 확대체 F_{p²} · F_{p³} 와 6 차 특성다항식 -/

/-- F_p[t]/(f) 의 원소 : 길이 k 의 계수 목록 (높은 차수부터) -/
abbrev Poly := List Nat

/-- 같은 길이 두 목록의 칸별 합 (나머지 p) -/
def addV (p : Nat) : Poly → Poly → Poly
  | a :: as, b :: bs => Nat.mod (Nat.add a b) p :: addV p as bs
  | _, _ => []

/-- 앞쪽 k 칸에만 더하기 (나머지는 그대로) -/
def addFront : Poly → Poly → Poly
  | a :: as, b :: bs => Nat.add a b :: addFront as bs
  | as, [] => as
  | [], _ => []

/-- 다항식 곱 (높은 차수부터 · 나머지 없이) -/
def conv : Poly → Poly → Poly
  | [], _ => []
  | [a], b => b.map (Nat.mul a)
  | a :: a' :: as, b => addFront (b.map (Nat.mul a) ++ (a' :: as).map (fun _ => 0)) (0 :: conv (a' :: as) b)

/-- t^k = Σ low_j t^j 로 차수 낮추기 : lowRev = [low_{k−1}, …, low_0] (연료 = 길이) -/
def reduce (k : Nat) (lowRev : Poly) : Nat → Poly → Poly
  | 0, l => l
  | fuel + 1, c :: rest => if rest.length < k then c :: rest else reduce k lowRev fuel (addFront rest (lowRev.map (Nat.mul c)))
  | _ + 1, [] => []

/-- 유한체 F_p[t]/(f) 의 자료 : 소수 p, 차수 k, t^k 를 낮은 차수로 쓴 계수 (높은 차수부터) -/
structure Fld where
  p : Nat
  k : Nat
  lowRev : Poly

def Fld.mul (F : Fld) (a b : Poly) : Poly := (reduce F.k F.lowRev (2 * F.k) (conv a b)).map (fun c => Nat.mod c F.p)
def Fld.add (F : Fld) (a b : Poly) : Poly := addV F.p a b
def Fld.zero (F : Fld) : Poly := (List.range F.k).map (fun _ => 0)
def Fld.one (F : Fld) : Poly := (List.range F.k).map (fun i => if i + 1 == F.k then 1 else 0)
def isZeroV (a : Poly) : Bool := a.all (fun c => Nat.beq c 0)

/-- 길이 k 의 모든 계수 목록 (p^k 개) -/
def allV (p : Nat) : Nat → List Poly
  | 0 => [[]]
  | k + 1 => (List.range p).flatMap (fun c => (allV p k).map (c :: ·))

def Fld.elems (F : Fld) : List Poly := allV F.p F.k

/-- 체 확인 : 0 아닌 원소마다 곱해서 1 이 되는 짝이 있다 -/
def Fld.isField (F : Fld) : Bool :=
  F.elems.all (fun a => isZeroV a || F.elems.any (fun b => F.mul a b == F.one))

/-- #C(F_q) : z = 1 인 (x, y) 의 수 + x³ = 0 인 x 의 수 + 1 -/
def Fld.kleinN (F : Fld) : Nat :=
  let E := F.elems
  let cubes := E.map (fun x => (x, F.mul x (F.mul x x)))
  let aff := cubes.foldl (fun acc (x, x3) =>
    acc + (cubes.filter (fun (y, y3) => isZeroV (F.add (F.add (F.mul x3 y) y3) x))).length) 0
  let inf := (cubes.filter (fun (_, x3) => isZeroV x3)).length
  aff + inf + 1

/-- 쓰는 체 여섯 : F₄ = F₂[t]/(t² + t + 1) , F₈ = F₂[t]/(t³ + t + 1) , F₉ = F₃[t]/(t² + 1) ,
F₂₇ = F₃[t]/(t³ + 2t + 1) , F₂₅ = F₅[t]/(t² − 2) , F₁₂₅ = F₅[t]/(t³ + t + 1) ; 차수 1 은 F_p 자체 -/
def F2_1 : Fld := ⟨2, 1, [0]⟩
def F2_2 : Fld := ⟨2, 2, [1, 1]⟩
def F2_3 : Fld := ⟨2, 3, [0, 1, 1]⟩
def F3_1 : Fld := ⟨3, 1, [0]⟩
def F3_2 : Fld := ⟨3, 2, [0, 2]⟩
def F3_3 : Fld := ⟨3, 3, [0, 1, 2]⟩
def F5_1 : Fld := ⟨5, 1, [0]⟩
def F5_2 : Fld := ⟨5, 2, [0, 2]⟩
def F5_3 : Fld := ⟨5, 3, [0, 4, 4]⟩

theorem fields_ok : F2_2.isField = true ∧ F2_3.isField = true ∧ F3_2.isField = true ∧ F3_3.isField = true ∧
    F5_2.isField = true := by decide +kernel

/-- 크기 확인 : 원소 수가 p^k -/
theorem field_sizes : F2_2.elems.length = 4 ∧ F2_3.elems.length = 8 ∧ F3_2.elems.length = 9 ∧
    F3_3.elems.length = 27 ∧ F5_2.elems.length = 25 := by decide +kernel

/-- 차수 1 의 세기가 1 절의 세기와 같다 (두 방식의 맞대기) -/
theorem degree_one_agrees : F2_1.kleinN = kleinN 2 ∧ F3_1.kleinN = kleinN 3 ∧ F5_1.kleinN = kleinN 5 := by
  decide +kernel

theorem count_p2 : (F2_1.kleinN, F2_2.kleinN, F2_3.kleinN) = (3, 5, 24) := by decide +kernel
theorem count_p3 : (F3_1.kleinN, F3_2.kleinN, F3_3.kleinN) = (4, 10, 28) := by decide +kernel
theorem count_p5_12 : (F5_1.kleinN, F5_2.kleinN) = (6, 26) := by decide +kernel

/-! ### 3 차 확대체를 자연수 하나로 적어 빠르게 세기

목록으로 적은 `Fld` 로 F₁₂₅ 를 세면 커널 메모리가 6 GB 를 넘어 멈춘다 (이 기계에서 확인).
그래서 3 차 확대체 F_p[t]/(t³ − l₂t² − l₁t − l₀) 의 원소 a₂t² + a₁t + a₀ 를
자연수 a₂p² + a₁p + a₀ (각 aᵢ < p) 하나로 적고, 곱을 닫힌 식으로 계산한다.
t³ = l₂t² + l₁t + l₀ , t⁴ = (l₂² + l₁)t² + (l₂l₁ + l₀)t + l₂l₀ 를 써서 차수를 낮춘다.
이 빠른 곱이 목록 곱 `Fld.mul` 과 F₈ · F₂₇ 의 모든 짝에서 같음을 먼저 확인한다 (`mul3_agrees`). -/

/-- 자연수 부호 e 를 계수 목록 [a₂, a₁, a₀] 로 -/
def dec3 (p e : Nat) : Poly := [Nat.mod (Nat.div e (Nat.mul p p)) p, Nat.mod (Nat.div e p) p, Nat.mod e p]

/-- 3 차 확대체의 곱 (부호끼리) -/
def mul3 (p l2 l1 l0 a b : Nat) : Nat :=
  let a2 := Nat.mod (Nat.div a (Nat.mul p p)) p
  let a1 := Nat.mod (Nat.div a p) p
  let a0 := Nat.mod a p
  let b2 := Nat.mod (Nat.div b (Nat.mul p p)) p
  let b1 := Nat.mod (Nat.div b p) p
  let b0 := Nat.mod b p
  let c4 := Nat.mul a2 b2
  let c3 := Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1)
  let c2 := Nat.add (Nat.add (Nat.mul a0 b2) (Nat.mul a1 b1)) (Nat.mul a2 b0)
  let c1 := Nat.add (Nat.mul a0 b1) (Nat.mul a1 b0)
  let c0 := Nat.mul a0 b0
  let r2 := Nat.mod (Nat.add (Nat.add c2 (Nat.mul c3 l2)) (Nat.mul c4 (Nat.add (Nat.mul l2 l2) l1))) p
  let r1 := Nat.mod (Nat.add (Nat.add c1 (Nat.mul c3 l1)) (Nat.mul c4 (Nat.add (Nat.mul l2 l1) l0))) p
  let r0 := Nat.mod (Nat.add (Nat.add c0 (Nat.mul c3 l0)) (Nat.mul c4 (Nat.mul l2 l0))) p
  Nat.add (Nat.mul (Nat.add (Nat.mul r2 p) r1) p) r0

/-- 3 차 확대체의 합 (계수별 · 나머지 p) -/
def add3 (p a b : Nat) : Nat :=
  let r2 := Nat.mod (Nat.add (Nat.div a (Nat.mul p p)) (Nat.div b (Nat.mul p p))) p
  let r1 := Nat.mod (Nat.add (Nat.mod (Nat.div a p) p) (Nat.mod (Nat.div b p) p)) p
  let r0 := Nat.mod (Nat.add (Nat.mod a p) (Nat.mod b p)) p
  Nat.add (Nat.mul (Nat.add (Nat.mul r2 p) r1) p) r0

/-- 빠른 곱이 목록 곱과 같다 : 모든 a, b < p³ 에서 dec3 (mul3 a b) = Fld.mul (dec3 a) (dec3 b) -/
def mul3Agrees (F : Fld) (l2 l1 l0 : Nat) : Bool :=
  let q := F.p * F.p * F.p
  (List.range q).all (fun a => (List.range q).all (fun b =>
    dec3 F.p (mul3 F.p l2 l1 l0 a b) == F.mul (dec3 F.p a) (dec3 F.p b)))

/-- 3 차 확대체에서 클라인 곡선 z = 1 조각의 한 줄 : x³y + y³ + x = 0 인 y < n 의 수 -/
def klein3Row (p l2 l1 l0 x x3 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun y acc => Nat.add acc
      (cond (Nat.beq (add3 p (add3 p (mul3 p l2 l1 l0 x3 y) (mul3 p l2 l1 l0 y (mul3 p l2 l1 l0 y y))) x) 0) 1 0)) n

def klein3Aff (p l2 l1 l0 q n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.add acc (klein3Row p l2 l1 l0 x (mul3 p l2 l1 l0 x (mul3 p l2 l1 l0 x x)) q)) n

def klein3Inf (p l2 l1 l0 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.add acc (cond (Nat.beq (mul3 p l2 l1 l0 x (mul3 p l2 l1 l0 x x)) 0) 1 0)) n

/-- #C(F_{p³}) (부호 방식) -/
def klein3N (p l2 l1 l0 : Nat) : Nat :=
  let q := Nat.mul p (Nat.mul p p)
  klein3Aff p l2 l1 l0 q q + klein3Inf p l2 l1 l0 q + 1

/-- 체 확인 (부호 방식) : 1 ≤ a < n 마다 a·b = 1 인 b < q 가 있다 -/
def inv3Row (p l2 l1 l0 a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun b acc => or acc (Nat.beq (mul3 p l2 l1 l0 a b) 1)) n

def isField3 (p l2 l1 l0 : Nat) : Bool :=
  let q := Nat.mul p (Nat.mul p p)
  Nat.rec (motive := fun _ => Bool) true
    (fun a acc => and acc (or (Nat.beq a 0) (inv3Row p l2 l1 l0 a q))) q

/-- 빠른 곱의 맞대기 : F₈ (l = 0, 1, 1) · F₂₇ (l = 0, 1, 2) 의 모든 짝에서 목록 곱과 같다 -/
theorem mul3_agrees : mul3Agrees F2_3 0 1 1 = true ∧ mul3Agrees F3_3 0 1 2 = true := by decide +kernel

/-- 부호 방식의 세기가 목록 방식의 세기와 같다 (F₈ , F₂₇) -/
theorem klein3_agrees : klein3N 2 0 1 1 = F2_3.kleinN ∧ klein3N 3 0 1 2 = F3_3.kleinN := by decide +kernel

/-- F₁₂₅ = F₅[t]/(t³ + t + 1) (t³ = 4t + 4) 는 체이고, 클라인 곡선의 점은 126 개 -/
theorem field_125 : isField3 5 0 4 4 = true := by decide +kernel
theorem count_p5_3 : klein3N 5 0 4 4 = 126 := by decide +kernel

/-- 점 수 N₁, N₂, N₃ 에서 특성다항식 (높은 차수부터) :
s_k = p^k + 1 − N_k , c₁ = s₁ , c₂ = (s₁² − s₂)/2 , c₃ = (s₁³ − 3s₁s₂ + 2s₃)/6 (나눗셈이 정확한지도 확인) -/
def charPoly (p : Int) (N1 N2 N3 : Int) : Option (List Int) :=
  let s1 := p + 1 - N1
  let s2 := p ^ 2 + 1 - N2
  let s3 := p ^ 3 + 1 - N3
  let e2 := s1 * s1 - s2
  let e3 := s1 ^ 3 - 3 * s1 * s2 + 2 * s3
  if e2 % 2 == 0 && e3 % 6 == 0 then
    let c1 := s1
    let c2 := e2 / 2
    let c3 := e3 / 6
    some [1, -c1, c2, -c3, p * c2, -(p * p * c1), p ^ 3]
  else none

/-- ℤ[ω] 계수 다항식의 곱 (높은 차수부터) -/
def eAddFront : List Eis → List Eis → List Eis
  | a :: as, b :: bs => a.add b :: eAddFront as bs
  | as, [] => as
  | [], _ => []

instance : OfNat Eis 0 := ⟨⟨0, 0⟩⟩

def eConv : List Eis → List Eis → List Eis
  | [], _ => []
  | [a], b => b.map (Eis.mul a)
  | a :: a' :: as, b => eAddFront (b.map (Eis.mul a) ++ (a' :: as).map (fun _ => 0)) (0 :: eConv (a' :: as) b)

/-- 모형 : Π_{t ∈ {1, χ(p), χ(p)²}} (T² − a t T + p t²) -/
def model (p : Nat) (a : Int) : List Eis :=
  let quad (t : Eis) : List Eis := [one, Eis.neg (Eis.mul (Eis.ofInt a) t), Eis.mul (Eis.ofInt p) (Eis.mul t t)]
  eConv (eConv (quad one) (quad (chi p))) (quad (Eis.mul (chi p) (chi p)))

/-- p = 2 : 특성다항식 T⁶ + 5T³ + 8 = 모형 (a₂ = 1 , χ(2) = ω²) -/
theorem charpoly_p2 :
    ap 2 = 1 ∧ charPoly 2 3 5 24 = some [1, 0, 0, 5, 0, 0, 8] ∧
      model 2 (ap 2) = [1, 0, 0, 5, 0, 0, 8].map Eis.ofInt := by decide +kernel

/-- p = 3 : 특성다항식 T⁶ + 27 = 모형 (a₃ = 0 , 초특이) -/
theorem charpoly_p3 :
    ap 3 = 0 ∧ charPoly 3 4 10 28 = some [1, 0, 0, 0, 0, 0, 27] ∧
      model 3 (ap 3) = [1, 0, 0, 0, 0, 0, 27].map Eis.ofInt := by decide +kernel

/-- p = 5 : 특성다항식 T⁶ + 125 = 모형 (a₅ = 0 , 초특이) -/
theorem charpoly_p5 :
    ap 5 = 0 ∧ charPoly 5 6 26 126 = some [1, 0, 0, 0, 0, 0, 125] ∧
      model 5 (ap 5) = [1, 0, 0, 0, 0, 0, 125].map Eis.ofInt := by decide +kernel

end Trombo.KleinCount

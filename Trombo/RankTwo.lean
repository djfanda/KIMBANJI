/-
계수 2 곡선 18 개 — 대수 쪽 증명서 (린 4 코어 · Mathlib 없음 · 유한 자료)

배경. 유리수 위 타원곡선 E 에서 버치–스위너턴다이어 (BSD) 추측은 대수적 계수 rank E(ℚ) 와
L(E, s) 의 s = 1 에서의 영점 차수 (해석적 계수) 가 같다고 말한다. 크레모나 표의 계수 2 곡선 18 개
(도체 389 ~ 997) 에서 «L(E,1) = L′(E,1) = 0, L″(E,1) ≠ 0» 은 린 밖에서 공 산술로 잰 것이고 (②),
이 모듈은 그것을 다시 하지 않는다. 해석적 계수 2 는 ② 로 남는다. BSD 일반은 다루지 않는다.

이 모듈에서 커널이 확인하는 것 (decide +kernel · 유한 계산) :

1. 곡선마다 크레모나 생성원 두 개 P, Q 가 y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆ 위의 유리점이다
   (분수 그대로). 크레모나 [X, Y, Z] 는 점 (X/Z, Y/Z) (817a1 · 997b1 의 둘째 생성원은 Z = 8).
   유리수 현–접선 덧셈으로 P + Q, P − Q, 2P, 2Q 가 다시 곡선 위에 있고,
   |m|, |n| ≤ 3, (m, n) ≠ (0, 0) 이면 mP + nQ ≠ O (작은 관계 없음) 이다.

2. 독립 증명서 (ℓ = 2). 곡선마다 작은 소수 몇 개를 골라 :
   · p 는 소수 · p ≥ 3 · p ∤ Δ (그래서 p ∤ N, 좋은 환원) · p 는 P, Q 좌표의 분모를 나누지 않고,
     환원점 P̄, Q̄ 가 Ẽ(F_p) 위에 있다.
   · 0 이 아닌 칸 (a, b) = (1, 0), (0, 1), (1, 1) 마다 어떤 p 에서 aP̄ + bQ̄ 가
     2·Ẽ(F_p) = {2S : S ∈ Ẽ(F_p)} 에 없다. 2·Ẽ(F_p) 는 Ẽ(F_p) 를 전부 열거 (x, y ∈ [0, p) 모두 +
     무한원점) 해서 하나하나 두 배 한 것이다. 특히 aP̄ + bQ̄ ≠ O.
   · 고른 p 들의 #Ẽ(F_p) 의 최대공약수가 1 이다.
   그 결과를 명제로 옮긴 것이 `cert_sound` 와 곡선별 `indep_…` 정리이다.

3. 근호수. 도체에 제곱 인수가 없는 (준안정) 15 곡선에서 나쁜 소수 p 마다 :
   p 소수 · N = ∏ p · |Δ| = ∏ p^e (판별식의 소인수가 바로 나쁜 소수) · c₄ ≢ 0 (mod p) 이고,
   a_p = p + 1 − #Ẽ(F_p) (특이점 포함 F_p² 전수 셈, 큰 p 는 x 구간 덩어리로 나눠 셈) 가 ±1,
   w = −∏_{p | N} (−a_p) = +1 이며 표의 근호수와 같다.
   준안정이 아닌 664a1 (N = 2³·83), 916c1 (N = 2²·229), 944e1 (N = 2⁴·59) 은 3 을 건너뛴다.

형식화하지 않은 것 (전언 · 표준 정리 인용) :
   · F_p 위 현–접선 공식이 Ẽ(F_p) 의 군 법칙이고, 좋은 p 에서 환원 E(ℚ) → Ẽ(F_p) 가 군 준동형이다.
     (역원은 페르마 a^(p−2) 로 계산한다 — p 소수이므로 참 역원이라는 것도 전언.)
   · p ≥ 3 좋은 소수에서 꼬임 E(ℚ)_tors 는 Ẽ(F_p) 로 단사 → |E(ℚ)_tors| 가 gcd #Ẽ(F_p) = 1 을
     나누므로 꼬임이 없다 (표의 |T| = 1 과 맞음).
   · 그러면 «2 의 증명서 ⇒ rank E(ℚ) ≥ 2» : rank ≤ 1 이면 E(ℚ) ≅ ℤ^r (r ≤ 1) 이라
     E(ℚ)/2E(ℚ) 의 크기가 2 이하이고, P, Q, P + Q 중 하나가 2E(ℚ) 에 든다 (셋 다 0 아닌 칸이면
     P ≡ Q 라서 P + Q ≡ 0). 환원하면 그 칸의 aP̄ + bQ̄ 가 2·Ẽ(F_p) 에 들어 2 의 확인과 모순.
   · «c₄ ≢ 0, p | Δ ⇒ 곱셈적 환원», «곱셈적 환원에서 w_p = −a_p», «w = −∏ w_p» (전역 근호수의 곱 공식).
   · 해석적 계수 2 (L″(E,1) ≠ 0) 는 ② (공 산술), 린 밖.

sorry · native_decide · 새 공리 없음. 자료 : 크레모나 ecdata allcurves · allgens (계수둘.json).
만든 이 : 밀레니엄빈칸/계수둘_린증명서.py
-/
namespace Trombo.RankTwo

/-! ## 0. 곡선 · 판별식 · 소수 -/

/-- 바이어슈트라스 곡선 y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆ 의 다섯 계수 -/
structure Cv where
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a6 : Int
deriving DecidableEq, Repr

namespace Cv
/-- b₂ = a₁² + 4a₂ -/
def b2 (c : Cv) : Int := c.a1 * c.a1 + 4 * c.a2
/-- b₄ = 2a₄ + a₁a₃ -/
def b4 (c : Cv) : Int := 2 * c.a4 + c.a1 * c.a3
/-- b₆ = a₃² + 4a₆ -/
def b6 (c : Cv) : Int := c.a3 * c.a3 + 4 * c.a6
/-- b₈ = a₁²a₆ + 4a₂a₆ − a₁a₃a₄ + a₂a₃² − a₄² -/
def b8 (c : Cv) : Int :=
  c.a1 * c.a1 * c.a6 + 4 * c.a2 * c.a6 - c.a1 * c.a3 * c.a4 + c.a2 * c.a3 * c.a3 - c.a4 * c.a4
/-- 판별식 Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ -/
def disc (c : Cv) : Int :=
  -c.b2 * c.b2 * c.b8 - 8 * c.b4 * c.b4 * c.b4 - 27 * c.b6 * c.b6 + 9 * c.b2 * c.b4 * c.b6
/-- c₄ = b₂² − 24b₄ -/
def c4 (c : Cv) : Int := c.b2 * c.b2 - 24 * c.b4
end Cv

/-- 나눗셈 시험으로 본 소수 : 2 ≤ n 이고 2 ≤ d < n 인 d 가 n 을 나누지 않는다 -/
def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

/-! ## 1. 유리수 위 점과 덧셈 -/

/-- 유리점 : none 이 무한원점 O -/
abbrev PtQ := Option (Rat × Rat)

/-- 점이 곡선 위에 있는가 (분수 그대로) -/
def onQ (c : Cv) : PtQ → Bool
  | none => true
  | some (x, y) => y * y + c.a1 * x * y + c.a3 * y == x * x * x + c.a2 * x * x + c.a4 * x + c.a6

/-- −(x, y) = (x, −y − a₁x − a₃) -/
def negQ (c : Cv) : PtQ → PtQ
  | none => none
  | some (x, y) => some (x, -y - c.a1 * x - c.a3)

/-- 기울기 λ 와 절편 ν 로 셋째 교점을 뒤집은 점 -/
def chordQ (c : Cv) (x1 x2 l v : Rat) : PtQ :=
  let x3 := l * l + c.a1 * l - c.a2 - x1 - x2
  some (x3, -(l + c.a1) * x3 - v - c.a3)

/-- 현–접선 덧셈 (일반 바이어슈트라스 꼴) -/
def addQ (c : Cv) : PtQ → PtQ → PtQ
  | none, q => q
  | some p, none => some p
  | some (x1, y1), some (x2, y2) =>
    if x1 == x2 then
      if y1 + y2 + c.a1 * x2 + c.a3 == 0 then none
      else
        let d := 2 * y1 + c.a1 * x1 + c.a3
        chordQ c x1 x2 ((3 * x1 * x1 + 2 * c.a2 * x1 + c.a4 - c.a1 * y1) / d)
          ((-x1 * x1 * x1 + c.a4 * x1 + 2 * c.a6 - c.a3 * y1) / d)
    else
      chordQ c x1 x2 ((y2 - y1) / (x2 - x1)) ((y1 * x2 - y2 * x1) / (x2 - x1))

/-- n·P (n ≥ 0) -/
def nsmulQ (c : Cv) (P : PtQ) : Nat → PtQ
  | 0 => none
  | n + 1 => addQ c (nsmulQ c P n) P

/-- m·P (m 정수) -/
def zsmulQ (c : Cv) (m : Int) (P : PtQ) : PtQ :=
  if 0 ≤ m then nsmulQ c P m.toNat else negQ c (nsmulQ c P m.natAbs)

/-! ## 2. F_p 위 점과 덧셈 -/

/-- F_p 의 점 : 좌표는 정수 (0 ≤ · < p 로 맞춘다), none 이 O -/
abbrev PtF := Option (Int × Int)

/-- z mod p (0 ≤ · < p) -/
def md (p : Nat) (z : Int) : Int := z % (p : Int)

/-- 페르마 역원 a^(p−2) mod p (p 소수, p ∤ a 일 때 참 역원) -/
def invF (p : Nat) (a : Int) : Int := (((md p a).toNat ^ (p - 2)) % p : Nat)

/-- 셋째 교점을 뒤집은 점 (mod p) -/
def chordF (p : Nat) (c : Cv) (x1 x2 l v : Int) : PtF :=
  let x3 := md p (l * l + c.a1 * l - c.a2 - x1 - x2)
  some (x3, md p (-(l + c.a1) * x3 - v - c.a3))

/-- 현–접선 덧셈 (mod p) -/
def addF (p : Nat) (c : Cv) : PtF → PtF → PtF
  | none, q => q
  | some q, none => some q
  | some (x1, y1), some (x2, y2) =>
    if x1 == x2 then
      if md p (y1 + y2 + c.a1 * x2 + c.a3) == 0 then none
      else
        let e := invF p (2 * y1 + c.a1 * x1 + c.a3)
        chordF p c x1 x2 (md p ((3 * x1 * x1 + 2 * c.a2 * x1 + c.a4 - c.a1 * y1) * e))
          (md p ((-x1 * x1 * x1 + c.a4 * x1 + 2 * c.a6 - c.a3 * y1) * e))
    else
      let e := invF p (x2 - x1)
      chordF p c x1 x2 (md p ((y2 - y1) * e)) (md p ((y1 * x2 - y2 * x1) * e))

/-- n·P (mod p) -/
def nsmulF (p : Nat) (c : Cv) (P : PtF) : Nat → PtF
  | 0 => none
  | n + 1 => addF p c (nsmulF p c P n) P

/-- 두 배 2S -/
def dblF (p : Nat) (c : Cv) (S : PtF) : PtF := addF p c S S

/-- 점이 Ẽ(F_p) 위에 있는가 -/
def onF (p : Nat) (c : Cv) : PtF → Bool
  | none => true
  | some (x, y) => md p (y * y + c.a1 * x * y + c.a3 * y - (x * x * x + c.a2 * x * x + c.a4 * x + c.a6)) == 0

/-- 분수 r = num/den 의 환원 (p ∤ den) -/
def redQ (p : Nat) (r : Rat) : Int := md p (r.num * invF p r.den)

/-- 유리점의 환원 -/
def redPt (p : Nat) (P : Rat × Rat) : PtF := some (redQ p P.1, redQ p P.2)

/-- Ẽ(F_p) 전부 : 무한원점 + x, y ∈ [0, p) 인 해 전부 -/
def ptsF (p : Nat) (c : Cv) : List PtF :=
  none :: (List.range p).flatMap fun (x : Nat) =>
    ((List.range p).filter fun (y : Nat) => onF p c (some ((x : Int), (y : Int)))).map
      fun (y : Nat) => some ((x : Int), (y : Int))

/-- R 이 2·Ẽ(F_p) 에 없다 : Ẽ(F_p) 의 어떤 S 도 2S = R 이 아니다 -/
def notDbl (p : Nat) (c : Cv) (R : PtF) : Bool := (ptsF p c).all fun S => dblF p c S != R

/-- Ẽ(F_p) 의 점이라는 명제 : O 이거나 좌표가 [0, p) 인 해 -/
def IsPtF (p : Nat) (c : Cv) (S : PtF) : Prop :=
  S = none ∨ ∃ x y : Nat, x < p ∧ y < p ∧ S = some ((x : Int), (y : Int)) ∧ onF p c S = true

/-- 열거가 Ẽ(F_p) 를 빠짐없이 덮는다 -/
theorem mem_ptsF {p : Nat} {c : Cv} {S : PtF} (h : IsPtF p c S) : S ∈ ptsF p c := by
  rcases h with rfl | ⟨x, y, hx, hy, rfl, hon⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨x, hx, y, ⟨hy, hon⟩, rfl⟩

/-- notDbl 의 뜻 : Ẽ(F_p) 의 모든 S 에서 2S ≠ R -/
theorem notDbl_sound {p : Nat} {c : Cv} {R : PtF} (h : notDbl p c R = true) :
    ∀ S, IsPtF p c S → dblF p c S ≠ R := by
  intro S hS
  have := (List.all_eq_true.mp h) S (mem_ptsF hS)
  simpa using this

/-! ## 3. 점 세기 #Ẽ(F_p) — 전수 (특이점 포함) -/

/-- 계수를 p 로 줄인 자연수 다섯 -/
structure K where
  a1 : Nat
  a2 : Nat
  a3 : Nat
  a4 : Nat
  a6 : Nat
deriving DecidableEq, Repr

/-- 계수의 mod p 환원 -/
def Cv.modp (c : Cv) (p : Nat) : K :=
  ⟨(c.a1 % (p : Int)).toNat, (c.a2 % (p : Int)).toNat, (c.a3 % (p : Int)).toNat,
   (c.a4 % (p : Int)).toNat, (c.a6 % (p : Int)).toNat⟩

/-- y ∈ [0, n) 중 y² + by ≡ r (mod p) 인 것의 수 -/
def cntY (p b r : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun y acc => cond (Nat.beq ((y * y + b * y) % p) r) (acc + 1) acc) n

/-- x 하나에서 y² + (a₁x + a₃)y ≡ x³ + a₂x² + a₄x + a₆ (mod p) 인 y ∈ [0, p) 의 수 -/
def cntAt (p : Nat) (k : K) (x : Nat) : Nat :=
  cntY p ((k.a1 * x + k.a3) % p) ((x * x * x + k.a2 * x * x + k.a4 * x + k.a6) % p) p

/-- x ∈ [lo, lo + n) 의 해 수 -/
def cntRange (p : Nat) (k : K) (lo : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => acc + cntAt p k (lo + j)) n

/-- #Ẽ(F_p) : F_p² 의 해 전부 (특이점 포함) + 무한원점 -/
def card (p : Nat) (c : Cv) : Nat := 1 + cntRange p (c.modp p) 0 p

theorem cntRange_succ (p : Nat) (k : K) (lo n : Nat) :
    cntRange p k lo (n + 1) = cntRange p k lo n + cntAt p k (lo + n) := rfl

/-- 구간을 둘로 나눈다 -/
theorem cntRange_add (p : Nat) (k : K) (lo m n : Nat) :
    cntRange p k lo (m + n) = cntRange p k lo m + cntRange p k (lo + m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, cntRange_succ, ih, cntRange_succ, Nat.add_assoc, Nat.add_assoc lo m n]

/-- 덩어리 둘을 잇는다 (이음매 lo + m = lo′, 길이 m + n = L, 합 a + b = S 는 따로 확인) -/
theorem chain {p : Nat} {k : K} {lo m n a b lo' L S : Nat} (h1 : cntRange p k lo m = a)
    (h2 : cntRange p k lo' n = b) (hlo : lo + m = lo') (hL : m + n = L) (hS : a + b = S) :
    cntRange p k lo L = S := by
  subst hlo hL hS
  rw [cntRange_add, h1, h2]

/-! ## 4. 곡선 자료 -/

/-- 곡선 한 줄 : 이름 · 도체 N · 근호수 w · |T| · 계수 · 생성원 P, Q · 증명서 소수 -/
structure Rec where
  name : String
  N : Nat
  w : Int
  T : Nat
  c : Cv
  P : Rat × Rat
  Q : Rat × Rat
  ps : List Nat

/-- 389a1 : N = 389 -/
def c389a1 : Rec where
  name := "389a1"
  N := 389
  w := 1
  T := 1
  c := ⟨0, 1, 1, -2, 0⟩
  P := ((0 : Rat), (0 : Rat))
  Q := ((1 : Rat), (0 : Rat))
  ps := [3, 5, 11]

/-- 433a1 : N = 433 -/
def c433a1 : Rec where
  name := "433a1"
  N := 433
  w := 1
  T := 1
  c := ⟨1, 0, 0, 0, 1⟩
  P := ((0 : Rat), (1 : Rat))
  Q := ((-1 : Rat), (1 : Rat))
  ps := [3, 5, 7]

/-- 446d1 : N = 446 -/
def c446d1 : Rec where
  name := "446d1"
  N := 446
  w := 1
  T := 1
  c := ⟨1, -1, 0, -4, 4⟩
  P := ((2 : Rat), (0 : Rat))
  Q := ((1 : Rat), (0 : Rat))
  ps := [3, 5, 13]

/-- 563a1 : N = 563 -/
def c563a1 : Rec where
  name := "563a1"
  N := 563
  w := 1
  T := 1
  c := ⟨1, 1, 1, -15, 16⟩
  P := ((2 : Rat), (-2 : Rat))
  Q := ((4 : Rat), (4 : Rat))
  ps := [3, 5, 11]

/-- 571b1 : N = 571 -/
def c571b1 : Rec where
  name := "571b1"
  N := 571
  w := 1
  T := 1
  c := ⟨0, 1, 1, -4, 2⟩
  P := ((1 : Rat), (0 : Rat))
  Q := ((0 : Rat), (1 : Rat))
  ps := [3, 5, 11]

/-- 643a1 : N = 643 -/
def c643a1 : Rec where
  name := "643a1"
  N := 643
  w := 1
  T := 1
  c := ⟨1, 0, 0, -4, 3⟩
  P := ((1 : Rat), (0 : Rat))
  Q := ((2 : Rat), (1 : Rat))
  ps := [3, 5, 7]

/-- 655a1 : N = 655 -/
def c655a1 : Rec where
  name := "655a1"
  N := 655
  w := 1
  T := 1
  c := ⟨0, 0, 1, -13, 18⟩
  P := ((1 : Rat), (2 : Rat))
  Q := ((3 : Rat), (2 : Rat))
  ps := [3, 11]

/-- 664a1 : N = 664 -/
def c664a1 : Rec where
  name := "664a1"
  N := 664
  w := 1
  T := 1
  c := ⟨0, 0, 0, -7, 10⟩
  P := ((1 : Rat), (2 : Rat))
  Q := ((3 : Rat), (4 : Rat))
  ps := [3, 5, 13]

/-- 681c1 : N = 681 -/
def c681c1 : Rec where
  name := "681c1"
  N := 681
  w := 1
  T := 1
  c := ⟨0, -1, 1, 0, 2⟩
  P := ((0 : Rat), (1 : Rat))
  Q := ((3 : Rat), (4 : Rat))
  ps := [5, 7, 13]

/-- 707a1 : N = 707 -/
def c707a1 : Rec where
  name := "707a1"
  N := 707
  w := 1
  T := 1
  c := ⟨0, 1, 1, -12, 12⟩
  P := ((3 : Rat), (3 : Rat))
  Q := ((1 : Rat), (1 : Rat))
  ps := [3, 5, 11]

/-- 709a1 : N = 709 -/
def c709a1 : Rec where
  name := "709a1"
  N := 709
  w := 1
  T := 1
  c := ⟨0, -1, 1, -2, 0⟩
  P := ((0 : Rat), (0 : Rat))
  Q := ((-1 : Rat), (0 : Rat))
  ps := [3, 7]

/-- 718b1 : N = 718 -/
def c718b1 : Rec where
  name := "718b1"
  N := 718
  w := 1
  T := 1
  c := ⟨1, 0, 1, -5, 0⟩
  P := ((-1 : Rat), (2 : Rat))
  Q := ((3 : Rat), (2 : Rat))
  ps := [3, 5, 7, 11]

/-- 794a1 : N = 794 -/
def c794a1 : Rec where
  name := "794a1"
  N := 794
  w := 1
  T := 1
  c := ⟨1, 0, 1, -3, 2⟩
  P := ((1 : Rat), (0 : Rat))
  Q := ((-1 : Rat), (2 : Rat))
  ps := [3, 5, 7, 11]

/-- 817a1 : N = 817 -/
def c817a1 : Rec where
  name := "817a1"
  N := 817
  w := 1
  T := 1
  c := ⟨0, 1, 1, 1, 6⟩
  P := ((4 : Rat), (9 : Rat))
  Q := (mkRat (-3) 4, mkRat (15) 8)
  ps := [3, 5, 11]

/-- 916c1 : N = 916 -/
def c916c1 : Rec where
  name := "916c1"
  N := 916
  w := 1
  T := 1
  c := ⟨0, 0, 0, -4, 1⟩
  P := ((0 : Rat), (1 : Rat))
  Q := ((2 : Rat), (1 : Rat))
  ps := [3, 7, 23]

/-- 944e1 : N = 944 -/
def c944e1 : Rec where
  name := "944e1"
  N := 944
  w := 1
  T := 1
  c := ⟨0, 0, 0, -19, 34⟩
  P := ((1 : Rat), (4 : Rat))
  Q := ((3 : Rat), (2 : Rat))
  ps := [3, 11, 13]

/-- 997b1 : N = 997 -/
def c997b1 : Rec where
  name := "997b1"
  N := 997
  w := 1
  T := 1
  c := ⟨0, -1, 1, -5, -3⟩
  P := ((-1 : Rat), (0 : Rat))
  Q := (mkRat (-3) 4, mkRat (-3) 8)
  ps := [3, 5, 7, 11]

/-- 997c1 : N = 997 -/
def c997c1 : Rec where
  name := "997c1"
  N := 997
  w := 1
  T := 1
  c := ⟨0, -1, 1, -24, 54⟩
  P := ((3 : Rat), (0 : Rat))
  Q := ((1 : Rat), (5 : Rat))
  ps := [3, 5, 7]

/-- 크레모나 표의 계수 2 곡선 18 개 (도체 ≤ 999) -/
def all18 : List Rec :=
  [c389a1,
   c433a1,
   c446d1,
   c563a1,
   c571b1,
   c643a1,
   c655a1,
   c664a1,
   c681c1,
   c707a1,
   c709a1,
   c718b1,
   c794a1,
   c817a1,
   c916c1,
   c944e1,
   c997b1,
   c997c1]

theorem all18_length : all18.length = 18 := rfl

/-! ## 5. 생성원은 유리점이다 · 유리수 덧셈의 닫힘 · 작은 관계 없음 -/

/-- 두 생성원이 곡선 위에 있다 -/
def gensOn (r : Rec) : Bool := onQ r.c (some r.P) && onQ r.c (some r.Q)

/-- P + Q, P − Q, 2P, 2Q 가 O 가 아니고 다시 곡선 위에 있다 -/
def closure (r : Rec) : Bool :=
  let P : PtQ := some r.P
  let Q : PtQ := some r.Q
  [addQ r.c P Q, addQ r.c P (negQ r.c Q), addQ r.c P P, addQ r.c Q Q].all
    (fun R => R != none && onQ r.c R)

/-- −3 ≤ m, n ≤ 3, (m, n) ≠ (0, 0) 이면 mP + nQ ≠ O -/
def noSmall (r : Rec) : Bool :=
  let rng : List Int := [-3, -2, -1, 0, 1, 2, 3]
  rng.all fun m => rng.all fun n =>
    (m == 0 && n == 0) || addQ r.c (zsmulQ r.c m (some r.P)) (zsmulQ r.c n (some r.Q)) != none

/-- 18 곡선 모두 두 생성원이 곡선 위에 있다 (분수 그대로) -/
theorem gens_on_all : all18.all gensOn = true := by decide +kernel

/-- 18 곡선 모두 P + Q, P − Q, 2P, 2Q 가 곡선 위에 있다 -/
theorem closure_all : all18.all closure = true := by decide +kernel

/-- 389a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_389a1 : noSmall c389a1 = true := by decide +kernel

/-- 433a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_433a1 : noSmall c433a1 = true := by decide +kernel

/-- 446d1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_446d1 : noSmall c446d1 = true := by decide +kernel

/-- 563a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_563a1 : noSmall c563a1 = true := by decide +kernel

/-- 571b1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_571b1 : noSmall c571b1 = true := by decide +kernel

/-- 643a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_643a1 : noSmall c643a1 = true := by decide +kernel

/-- 655a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_655a1 : noSmall c655a1 = true := by decide +kernel

/-- 664a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_664a1 : noSmall c664a1 = true := by decide +kernel

/-- 681c1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_681c1 : noSmall c681c1 = true := by decide +kernel

/-- 707a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_707a1 : noSmall c707a1 = true := by decide +kernel

/-- 709a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_709a1 : noSmall c709a1 = true := by decide +kernel

/-- 718b1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_718b1 : noSmall c718b1 = true := by decide +kernel

/-- 794a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_794a1 : noSmall c794a1 = true := by decide +kernel

/-- 817a1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_817a1 : noSmall c817a1 = true := by decide +kernel

/-- 916c1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_916c1 : noSmall c916c1 = true := by decide +kernel

/-- 944e1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_944e1 : noSmall c944e1 = true := by decide +kernel

/-- 997b1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_997b1 : noSmall c997b1 = true := by decide +kernel

/-- 997c1 : |m|, |n| ≤ 3 인 작은 관계 mP + nQ = O 없음 -/
theorem noSmall_997c1 : noSmall c997c1 = true := by decide +kernel

/-! ## 6. 독립 증명서 (ℓ = 2) -/

/-- 0 이 아닌 칸 (a, b) ∈ {0,1}² -/
def classes : List (Nat × Nat) := [(1, 0), (0, 1), (1, 1)]

/-- aP̄ + bQ̄ (mod p) -/
def comb (r : Rec) (p : Nat) (ab : Nat × Nat) : PtF :=
  addF p r.c (nsmulF p r.c (redPt p r.P) ab.1) (nsmulF p r.c (redPt p r.Q) ab.2)

/-- p 가 좋은 소수 : 소수 · p ≥ 3 · p ∤ Δ · p ∤ 분모 · 환원점이 Ẽ(F_p) 위 -/
def goodAt (r : Rec) (p : Nat) : Bool :=
  isPrime p && 3 ≤ p && r.c.disc % (p : Int) != 0 &&
  r.P.1.den % p != 0 && r.P.2.den % p != 0 && r.Q.1.den % p != 0 && r.Q.2.den % p != 0 &&
  onF p r.c (redPt p r.P) && onF p r.c (redPt p r.Q)

/-- p 가 칸 (a, b) 를 가른다 : p 가 좋고 aP̄ + bQ̄ ∉ 2·Ẽ(F_p) -/
def sepAt (r : Rec) (p : Nat) (ab : Nat × Nat) : Bool :=
  goodAt r p && notDbl p r.c (comb r p ab)

/-- 고른 p 들의 #Ẽ(F_p) 의 최대공약수 -/
def gcdCard (r : Rec) : Nat := r.ps.foldl (fun g p => Nat.gcd g (card p r.c)) 0

/-- 칸 하나를 가르는 소수가 증명서 목록에 있다 -/
def classOk (r : Rec) (ab : Nat × Nat) : Bool := r.ps.any fun p => sepAt r p ab

/-- 2 의 증명서의 뜻 (명제) : 칸마다 좋은 소수 p 가 있어 Ẽ(F_p) 의 어떤 S 도 2S = aP̄ + bQ̄ 가 아니다.
특히 aP̄ + bQ̄ ≠ O -/
def Indep2 (r : Rec) : Prop :=
  ∀ ab ∈ classes, ∃ p ∈ r.ps, goodAt r p = true ∧
    (∀ S, IsPtF p r.c S → dblF p r.c S ≠ comb r p ab) ∧ comb r p ab ≠ none

/-- Bool 확인 → 명제 -/
theorem cert_sound (r : Rec) (h : classes.all (classOk r) = true) : Indep2 r := by
  intro ab hab
  have h1 := (List.all_eq_true.mp h) ab hab
  obtain ⟨p, hp, hs⟩ := List.any_eq_true.mp h1
  simp only [sepAt, Bool.and_eq_true] at hs
  have hd := notDbl_sound hs.2
  refine ⟨p, hp, hs.1, hd, ?_⟩
  have h0 := hd none (Or.inl rfl)
  intro hc
  exact h0 (by rw [hc]; rfl)

/-- 389a1 : 칸 (1, 0) 는 p = 11 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_389a1_10 : sepAt c389a1 11 (1, 0) = true := by decide +kernel

/-- 389a1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_389a1_01 : sepAt c389a1 3 (0, 1) = true := by decide +kernel

/-- 389a1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_389a1_11 : sepAt c389a1 3 (1, 1) = true := by decide +kernel

theorem card_389a1_3 : card 3 c389a1.c = 6 := by decide +kernel
theorem card_389a1_5 : card 5 c389a1.c = 9 := by decide +kernel
theorem card_389a1_11 : card 11 c389a1.c = 16 := by decide +kernel

/-- 389a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 9, |2·Ẽ(F_p)| = 9 · p = 11 : #Ẽ(F_p) = 16, |2·Ẽ(F_p)| = 4 · 칸 (1, 0) ↦ p = 11, (0, 1) ↦ p = 3, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_389a1 : Indep2 c389a1 ∧ gcdCard c389a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c389a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨11, by decide, sep_389a1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_389a1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_389a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 433a1 : 칸 (1, 0) 는 p = 3 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_433a1_10 : sepAt c433a1 3 (1, 0) = true := by decide +kernel

/-- 433a1 : 칸 (0, 1) 는 p = 5 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_433a1_01 : sepAt c433a1 5 (0, 1) = true := by decide +kernel

/-- 433a1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_433a1_11 : sepAt c433a1 3 (1, 1) = true := by decide +kernel

theorem card_433a1_3 : card 3 c433a1.c = 6 := by decide +kernel
theorem card_433a1_5 : card 5 c433a1.c = 10 := by decide +kernel
theorem card_433a1_7 : card 7 c433a1.c = 11 := by decide +kernel

/-- 433a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 7 : #Ẽ(F_p) = 11, |2·Ẽ(F_p)| = 11 · 칸 (1, 0) ↦ p = 3, (0, 1) ↦ p = 5, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_433a1 : Indep2 c433a1 ∧ gcdCard c433a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c433a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨3, by decide, sep_433a1_10⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_433a1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_433a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 446d1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_446d1_10 : sepAt c446d1 5 (1, 0) = true := by decide +kernel

/-- 446d1 : 칸 (0, 1) 는 p = 5 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_446d1_01 : sepAt c446d1 5 (0, 1) = true := by decide +kernel

/-- 446d1 : 칸 (1, 1) 는 p = 13 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_13)) -/
theorem sep_446d1_11 : sepAt c446d1 13 (1, 1) = true := by decide +kernel

theorem card_446d1_3 : card 3 c446d1.c = 7 := by decide +kernel
theorem card_446d1_5 : card 5 c446d1.c = 10 := by decide +kernel
theorem card_446d1_13 : card 13 c446d1.c = 20 := by decide +kernel

/-- 446d1 : p = 3 : #Ẽ(F_p) = 7, |2·Ẽ(F_p)| = 7 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 13 : #Ẽ(F_p) = 20, |2·Ẽ(F_p)| = 10 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 5, (1, 1) ↦ p = 13 · gcd = 1 -/
theorem indep_446d1 : Indep2 c446d1 ∧ gcdCard c446d1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c446d1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_446d1_10⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_446d1_01⟩
      · exact List.any_eq_true.mpr ⟨13, by decide, sep_446d1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 563a1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_563a1_10 : sepAt c563a1 5 (1, 0) = true := by decide +kernel

/-- 563a1 : 칸 (0, 1) 는 p = 11 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_563a1_01 : sepAt c563a1 11 (0, 1) = true := by decide +kernel

/-- 563a1 : 칸 (1, 1) 는 p = 5 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_563a1_11 : sepAt c563a1 5 (1, 1) = true := by decide +kernel

theorem card_563a1_3 : card 3 c563a1.c = 5 := by decide +kernel
theorem card_563a1_5 : card 5 c563a1.c = 10 := by decide +kernel
theorem card_563a1_11 : card 11 c563a1.c = 16 := by decide +kernel

/-- 563a1 : p = 3 : #Ẽ(F_p) = 5, |2·Ẽ(F_p)| = 5 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 11 : #Ẽ(F_p) = 16, |2·Ẽ(F_p)| = 4 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 11, (1, 1) ↦ p = 5 · gcd = 1 -/
theorem indep_563a1 : Indep2 c563a1 ∧ gcdCard c563a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c563a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_563a1_10⟩
      · exact List.any_eq_true.mpr ⟨11, by decide, sep_563a1_01⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_563a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 571b1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_571b1_10 : sepAt c571b1 5 (1, 0) = true := by decide +kernel

/-- 571b1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_571b1_01 : sepAt c571b1 3 (0, 1) = true := by decide +kernel

/-- 571b1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_571b1_11 : sepAt c571b1 3 (1, 1) = true := by decide +kernel

theorem card_571b1_3 : card 3 c571b1.c = 6 := by decide +kernel
theorem card_571b1_5 : card 5 c571b1.c = 8 := by decide +kernel
theorem card_571b1_11 : card 11 c571b1.c = 15 := by decide +kernel

/-- 571b1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 8, |2·Ẽ(F_p)| = 2 · p = 11 : #Ẽ(F_p) = 15, |2·Ẽ(F_p)| = 15 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 3, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_571b1 : Indep2 c571b1 ∧ gcdCard c571b1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c571b1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_571b1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_571b1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_571b1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 643a1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_643a1_10 : sepAt c643a1 5 (1, 0) = true := by decide +kernel

/-- 643a1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_643a1_01 : sepAt c643a1 3 (0, 1) = true := by decide +kernel

/-- 643a1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_643a1_11 : sepAt c643a1 3 (1, 1) = true := by decide +kernel

theorem card_643a1_3 : card 3 c643a1.c = 6 := by decide +kernel
theorem card_643a1_5 : card 5 c643a1.c = 8 := by decide +kernel
theorem card_643a1_7 : card 7 c643a1.c = 11 := by decide +kernel

/-- 643a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 8, |2·Ẽ(F_p)| = 4 · p = 7 : #Ẽ(F_p) = 11, |2·Ẽ(F_p)| = 11 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 3, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_643a1 : Indep2 c643a1 ∧ gcdCard c643a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c643a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_643a1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_643a1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_643a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 655a1 : 칸 (1, 0) 는 p = 11 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_655a1_10 : sepAt c655a1 11 (1, 0) = true := by decide +kernel

/-- 655a1 : 칸 (0, 1) 는 p = 11 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_655a1_01 : sepAt c655a1 11 (0, 1) = true := by decide +kernel

/-- 655a1 : 칸 (1, 1) 는 p = 11 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_655a1_11 : sepAt c655a1 11 (1, 1) = true := by decide +kernel

theorem card_655a1_3 : card 3 c655a1.c = 7 := by decide +kernel
theorem card_655a1_11 : card 11 c655a1.c = 16 := by decide +kernel

/-- 655a1 : p = 3 : #Ẽ(F_p) = 7, |2·Ẽ(F_p)| = 7 · p = 11 : #Ẽ(F_p) = 16, |2·Ẽ(F_p)| = 4 · 칸 (1, 0) ↦ p = 11, (0, 1) ↦ p = 11, (1, 1) ↦ p = 11 · gcd = 1 -/
theorem indep_655a1 : Indep2 c655a1 ∧ gcdCard c655a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c655a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨11, by decide, sep_655a1_10⟩
      · exact List.any_eq_true.mpr ⟨11, by decide, sep_655a1_01⟩
      · exact List.any_eq_true.mpr ⟨11, by decide, sep_655a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 664a1 : 칸 (1, 0) 는 p = 13 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_13)) -/
theorem sep_664a1_10 : sepAt c664a1 13 (1, 0) = true := by decide +kernel

/-- 664a1 : 칸 (0, 1) 는 p = 5 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_664a1_01 : sepAt c664a1 5 (0, 1) = true := by decide +kernel

/-- 664a1 : 칸 (1, 1) 는 p = 5 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_664a1_11 : sepAt c664a1 5 (1, 1) = true := by decide +kernel

theorem card_664a1_3 : card 3 c664a1.c = 7 := by decide +kernel
theorem card_664a1_5 : card 5 c664a1.c = 10 := by decide +kernel
theorem card_664a1_13 : card 13 c664a1.c = 18 := by decide +kernel

/-- 664a1 : p = 3 : #Ẽ(F_p) = 7, |2·Ẽ(F_p)| = 7 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 13 : #Ẽ(F_p) = 18, |2·Ẽ(F_p)| = 9 · 칸 (1, 0) ↦ p = 13, (0, 1) ↦ p = 5, (1, 1) ↦ p = 5 · gcd = 1 -/
theorem indep_664a1 : Indep2 c664a1 ∧ gcdCard c664a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c664a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨13, by decide, sep_664a1_10⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_664a1_01⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_664a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 681c1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_681c1_10 : sepAt c681c1 5 (1, 0) = true := by decide +kernel

/-- 681c1 : 칸 (0, 1) 는 p = 13 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_13)) -/
theorem sep_681c1_01 : sepAt c681c1 13 (0, 1) = true := by decide +kernel

/-- 681c1 : 칸 (1, 1) 는 p = 5 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_681c1_11 : sepAt c681c1 5 (1, 1) = true := by decide +kernel

theorem card_681c1_5 : card 5 c681c1.c = 10 := by decide +kernel
theorem card_681c1_7 : card 7 c681c1.c = 11 := by decide +kernel
theorem card_681c1_13 : card 13 c681c1.c = 16 := by decide +kernel

/-- 681c1 : p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 7 : #Ẽ(F_p) = 11, |2·Ẽ(F_p)| = 11 · p = 13 : #Ẽ(F_p) = 16, |2·Ẽ(F_p)| = 8 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 13, (1, 1) ↦ p = 5 · gcd = 1 -/
theorem indep_681c1 : Indep2 c681c1 ∧ gcdCard c681c1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c681c1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_681c1_10⟩
      · exact List.any_eq_true.mpr ⟨13, by decide, sep_681c1_01⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_681c1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 707a1 : 칸 (1, 0) 는 p = 3 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_707a1_10 : sepAt c707a1 3 (1, 0) = true := by decide +kernel

/-- 707a1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_707a1_01 : sepAt c707a1 3 (0, 1) = true := by decide +kernel

/-- 707a1 : 칸 (1, 1) 는 p = 11 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_707a1_11 : sepAt c707a1 11 (1, 1) = true := by decide +kernel

theorem card_707a1_3 : card 3 c707a1.c = 6 := by decide +kernel
theorem card_707a1_5 : card 5 c707a1.c = 9 := by decide +kernel
theorem card_707a1_11 : card 11 c707a1.c = 16 := by decide +kernel

/-- 707a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 9, |2·Ẽ(F_p)| = 9 · p = 11 : #Ẽ(F_p) = 16, |2·Ẽ(F_p)| = 8 · 칸 (1, 0) ↦ p = 3, (0, 1) ↦ p = 3, (1, 1) ↦ p = 11 · gcd = 1 -/
theorem indep_707a1 : Indep2 c707a1 ∧ gcdCard c707a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c707a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨3, by decide, sep_707a1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_707a1_01⟩
      · exact List.any_eq_true.mpr ⟨11, by decide, sep_707a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 709a1 : 칸 (1, 0) 는 p = 7 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_709a1_10 : sepAt c709a1 7 (1, 0) = true := by decide +kernel

/-- 709a1 : 칸 (0, 1) 는 p = 7 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_709a1_01 : sepAt c709a1 7 (0, 1) = true := by decide +kernel

/-- 709a1 : 칸 (1, 1) 는 p = 7 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_709a1_11 : sepAt c709a1 7 (1, 1) = true := by decide +kernel

theorem card_709a1_3 : card 3 c709a1.c = 5 := by decide +kernel
theorem card_709a1_7 : card 7 c709a1.c = 12 := by decide +kernel

/-- 709a1 : p = 3 : #Ẽ(F_p) = 5, |2·Ẽ(F_p)| = 5 · p = 7 : #Ẽ(F_p) = 12, |2·Ẽ(F_p)| = 3 · 칸 (1, 0) ↦ p = 7, (0, 1) ↦ p = 7, (1, 1) ↦ p = 7 · gcd = 1 -/
theorem indep_709a1 : Indep2 c709a1 ∧ gcdCard c709a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c709a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨7, by decide, sep_709a1_10⟩
      · exact List.any_eq_true.mpr ⟨7, by decide, sep_709a1_01⟩
      · exact List.any_eq_true.mpr ⟨7, by decide, sep_709a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 718b1 : 칸 (1, 0) 는 p = 11 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_718b1_10 : sepAt c718b1 11 (1, 0) = true := by decide +kernel

/-- 718b1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_718b1_01 : sepAt c718b1 3 (0, 1) = true := by decide +kernel

/-- 718b1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_718b1_11 : sepAt c718b1 3 (1, 1) = true := by decide +kernel

theorem card_718b1_3 : card 3 c718b1.c = 6 := by decide +kernel
theorem card_718b1_5 : card 5 c718b1.c = 9 := by decide +kernel
theorem card_718b1_7 : card 7 c718b1.c = 13 := by decide +kernel
theorem card_718b1_11 : card 11 c718b1.c = 18 := by decide +kernel

/-- 718b1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 9, |2·Ẽ(F_p)| = 9 · p = 7 : #Ẽ(F_p) = 13, |2·Ẽ(F_p)| = 13 · p = 11 : #Ẽ(F_p) = 18, |2·Ẽ(F_p)| = 9 · 칸 (1, 0) ↦ p = 11, (0, 1) ↦ p = 3, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_718b1 : Indep2 c718b1 ∧ gcdCard c718b1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c718b1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨11, by decide, sep_718b1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_718b1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_718b1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 794a1 : 칸 (1, 0) 는 p = 11 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_794a1_10 : sepAt c794a1 11 (1, 0) = true := by decide +kernel

/-- 794a1 : 칸 (0, 1) 는 p = 3 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_794a1_01 : sepAt c794a1 3 (0, 1) = true := by decide +kernel

/-- 794a1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_794a1_11 : sepAt c794a1 3 (1, 1) = true := by decide +kernel

theorem card_794a1_3 : card 3 c794a1.c = 6 := by decide +kernel
theorem card_794a1_5 : card 5 c794a1.c = 10 := by decide +kernel
theorem card_794a1_7 : card 7 c794a1.c = 11 := by decide +kernel
theorem card_794a1_11 : card 11 c794a1.c = 12 := by decide +kernel

/-- 794a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 7 : #Ẽ(F_p) = 11, |2·Ẽ(F_p)| = 11 · p = 11 : #Ẽ(F_p) = 12, |2·Ẽ(F_p)| = 6 · 칸 (1, 0) ↦ p = 11, (0, 1) ↦ p = 3, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_794a1 : Indep2 c794a1 ∧ gcdCard c794a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c794a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨11, by decide, sep_794a1_10⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_794a1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_794a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 817a1 : 칸 (1, 0) 는 p = 3 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_817a1_10 : sepAt c817a1 3 (1, 0) = true := by decide +kernel

/-- 817a1 : 칸 (0, 1) 는 p = 5 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_817a1_01 : sepAt c817a1 5 (0, 1) = true := by decide +kernel

/-- 817a1 : 칸 (1, 1) 는 p = 3 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_3)) -/
theorem sep_817a1_11 : sepAt c817a1 3 (1, 1) = true := by decide +kernel

theorem card_817a1_3 : card 3 c817a1.c = 6 := by decide +kernel
theorem card_817a1_5 : card 5 c817a1.c = 8 := by decide +kernel
theorem card_817a1_11 : card 11 c817a1.c = 17 := by decide +kernel

/-- 817a1 : p = 3 : #Ẽ(F_p) = 6, |2·Ẽ(F_p)| = 3 · p = 5 : #Ẽ(F_p) = 8, |2·Ẽ(F_p)| = 4 · p = 11 : #Ẽ(F_p) = 17, |2·Ẽ(F_p)| = 17 · 칸 (1, 0) ↦ p = 3, (0, 1) ↦ p = 5, (1, 1) ↦ p = 3 · gcd = 1 -/
theorem indep_817a1 : Indep2 c817a1 ∧ gcdCard c817a1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c817a1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨3, by decide, sep_817a1_10⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_817a1_01⟩
      · exact List.any_eq_true.mpr ⟨3, by decide, sep_817a1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 916c1 : 칸 (1, 0) 는 p = 7 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_916c1_10 : sepAt c916c1 7 (1, 0) = true := by decide +kernel

/-- 916c1 : 칸 (0, 1) 는 p = 7 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_916c1_01 : sepAt c916c1 7 (0, 1) = true := by decide +kernel

/-- 916c1 : 칸 (1, 1) 는 p = 23 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_23)) -/
theorem sep_916c1_11 : sepAt c916c1 23 (1, 1) = true := by decide +kernel

theorem card_916c1_3 : card 3 c916c1.c = 7 := by decide +kernel
theorem card_916c1_7 : card 7 c916c1.c = 12 := by decide +kernel
theorem card_916c1_23 : card 23 c916c1.c = 30 := by decide +kernel

/-- 916c1 : p = 3 : #Ẽ(F_p) = 7, |2·Ẽ(F_p)| = 7 · p = 7 : #Ẽ(F_p) = 12, |2·Ẽ(F_p)| = 6 · p = 23 : #Ẽ(F_p) = 30, |2·Ẽ(F_p)| = 15 · 칸 (1, 0) ↦ p = 7, (0, 1) ↦ p = 7, (1, 1) ↦ p = 23 · gcd = 1 -/
theorem indep_916c1 : Indep2 c916c1 ∧ gcdCard c916c1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c916c1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨7, by decide, sep_916c1_10⟩
      · exact List.any_eq_true.mpr ⟨7, by decide, sep_916c1_01⟩
      · exact List.any_eq_true.mpr ⟨23, by decide, sep_916c1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 944e1 : 칸 (1, 0) 는 p = 11 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_944e1_10 : sepAt c944e1 11 (1, 0) = true := by decide +kernel

/-- 944e1 : 칸 (0, 1) 는 p = 11 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_11)) -/
theorem sep_944e1_01 : sepAt c944e1 11 (0, 1) = true := by decide +kernel

/-- 944e1 : 칸 (1, 1) 는 p = 13 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_13)) -/
theorem sep_944e1_11 : sepAt c944e1 13 (1, 1) = true := by decide +kernel

theorem card_944e1_3 : card 3 c944e1.c = 7 := by decide +kernel
theorem card_944e1_11 : card 11 c944e1.c = 18 := by decide +kernel
theorem card_944e1_13 : card 13 c944e1.c = 20 := by decide +kernel

/-- 944e1 : p = 3 : #Ẽ(F_p) = 7, |2·Ẽ(F_p)| = 7 · p = 11 : #Ẽ(F_p) = 18, |2·Ẽ(F_p)| = 9 · p = 13 : #Ẽ(F_p) = 20, |2·Ẽ(F_p)| = 10 · 칸 (1, 0) ↦ p = 11, (0, 1) ↦ p = 11, (1, 1) ↦ p = 13 · gcd = 1 -/
theorem indep_944e1 : Indep2 c944e1 ∧ gcdCard c944e1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c944e1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨11, by decide, sep_944e1_10⟩
      · exact List.any_eq_true.mpr ⟨11, by decide, sep_944e1_01⟩
      · exact List.any_eq_true.mpr ⟨13, by decide, sep_944e1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 997b1 : 칸 (1, 0) 는 p = 5 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_997b1_10 : sepAt c997b1 5 (1, 0) = true := by decide +kernel

/-- 997b1 : 칸 (0, 1) 는 p = 7 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_997b1_01 : sepAt c997b1 7 (0, 1) = true := by decide +kernel

/-- 997b1 : 칸 (1, 1) 는 p = 5 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_997b1_11 : sepAt c997b1 5 (1, 1) = true := by decide +kernel

theorem card_997b1_3 : card 3 c997b1.c = 5 := by decide +kernel
theorem card_997b1_5 : card 5 c997b1.c = 10 := by decide +kernel
theorem card_997b1_7 : card 7 c997b1.c = 10 := by decide +kernel
theorem card_997b1_11 : card 11 c997b1.c = 14 := by decide +kernel

/-- 997b1 : p = 3 : #Ẽ(F_p) = 5, |2·Ẽ(F_p)| = 5 · p = 5 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 7 : #Ẽ(F_p) = 10, |2·Ẽ(F_p)| = 5 · p = 11 : #Ẽ(F_p) = 14, |2·Ẽ(F_p)| = 7 · 칸 (1, 0) ↦ p = 5, (0, 1) ↦ p = 7, (1, 1) ↦ p = 5 · gcd = 1 -/
theorem indep_997b1 : Indep2 c997b1 ∧ gcdCard c997b1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c997b1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨5, by decide, sep_997b1_10⟩
      · exact List.any_eq_true.mpr ⟨7, by decide, sep_997b1_01⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_997b1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-- 997c1 : 칸 (1, 0) 는 p = 7 에서 갈린다 (1·P̄ + 0·Q̄ ∉ 2·Ẽ(F_7)) -/
theorem sep_997c1_10 : sepAt c997c1 7 (1, 0) = true := by decide +kernel

/-- 997c1 : 칸 (0, 1) 는 p = 5 에서 갈린다 (0·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_997c1_01 : sepAt c997c1 5 (0, 1) = true := by decide +kernel

/-- 997c1 : 칸 (1, 1) 는 p = 5 에서 갈린다 (1·P̄ + 1·Q̄ ∉ 2·Ẽ(F_5)) -/
theorem sep_997c1_11 : sepAt c997c1 5 (1, 1) = true := by decide +kernel

theorem card_997c1_3 : card 3 c997c1.c = 5 := by decide +kernel
theorem card_997c1_5 : card 5 c997c1.c = 8 := by decide +kernel
theorem card_997c1_7 : card 7 c997c1.c = 12 := by decide +kernel

/-- 997c1 : p = 3 : #Ẽ(F_p) = 5, |2·Ẽ(F_p)| = 5 · p = 5 : #Ẽ(F_p) = 8, |2·Ẽ(F_p)| = 4 · p = 7 : #Ẽ(F_p) = 12, |2·Ẽ(F_p)| = 6 · 칸 (1, 0) ↦ p = 7, (0, 1) ↦ p = 5, (1, 1) ↦ p = 5 · gcd = 1 -/
theorem indep_997c1 : Indep2 c997c1 ∧ gcdCard c997c1 = 1 := by
  refine ⟨cert_sound _ ?_, ?_⟩
  · have h : ∀ ab ∈ classes, classOk c997c1 ab = true := by
      intro ab hab
      simp only [classes, List.mem_cons, List.mem_nil_iff, or_false] at hab
      rcases hab with rfl | rfl | rfl

      · exact List.any_eq_true.mpr ⟨7, by decide, sep_997c1_10⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_997c1_01⟩
      · exact List.any_eq_true.mpr ⟨5, by decide, sep_997c1_11⟩
    exact List.all_eq_true.mpr h
  · decide +kernel

/-! ## 7. 준안정 곡선의 근호수 -/

/-- 나쁜 소수 (p, Δ 의 지수 e) 목록이 맞다 : p 소수 · N = ∏ p · |Δ| = ∏ p^e · c₄ ≢ 0 (mod p) -/
def semiOk (r : Rec) (bad : List (Nat × Nat)) : Bool :=
  bad.all (fun pe => isPrime pe.1 && r.c.c4 % (pe.1 : Int) != 0) &&
  r.N == (bad.map (·.1)).foldl (· * ·) 1 &&
  r.c.disc.natAbs == (bad.map (fun pe => pe.1 ^ pe.2)).foldl (· * ·) 1

/-- w = −∏ (−a_p) -/
def rootW (as : List Int) : Int := -((as.map (fun t => -t)).foldl (· * ·) 1)

/-- ns 는 나쁜 소수마다의 #Ẽ(F_p). a_p = p + 1 − n_p 가 ±1 이고 w = −∏(−a_p) = +1 = 표의 근호수 -/
def rootOk (r : Rec) (bad : List (Nat × Nat)) (ns : List Nat) : Bool :=
  let as : List Int := (bad.zip ns).map (fun q => (q.1.1 : Int) + 1 - q.2)
  semiOk r bad && ns.length == bad.length &&
  as.all (fun t => t == 1 || t == -1) && rootW as == 1 && r.w == 1

/-- 389a1 의 계수 mod 389 -/
def k389a1_389 : K := ⟨0, 1, 1, 387, 0⟩
theorem k389a1_389_eq : c389a1.c.modp 389 = k389a1_389 := by decide +kernel

theorem cr_389a1_389_0 : cntRange 389 k389a1_389 0 257 = 265 := by decide +kernel
theorem cr_389a1_389_1 : cntRange 389 k389a1_389 257 132 = 123 := by decide +kernel

/-- #Ẽ(F_389) = 389 (a_389 = +1) — x 구간 2 덩어리 -/
theorem cardBad_389a1_389 : card 389 c389a1.c = 389 := by
  have h1 : cntRange 389 k389a1_389 257 132 = 123 := cr_389a1_389_1
  have h0 : cntRange 389 k389a1_389 0 389 = 388 := chain cr_389a1_389_0 h1 rfl rfl rfl
  rw [card, k389a1_389_eq, h0]

/-- 389a1 : N = 389 준안정 · a_389 = +1 · w = −∏(−a_p) = +1 -/
theorem root_389a1 : rootOk c389a1 [(389, 1)] [card 389 c389a1.c] = true := by
  rw [cardBad_389a1_389]; decide +kernel

/-- 433a1 의 계수 mod 433 -/
def k433a1_433 : K := ⟨1, 0, 0, 0, 1⟩
theorem k433a1_433_eq : c433a1.c.modp 433 = k433a1_433 := by decide +kernel

theorem cr_433a1_433_0 : cntRange 433 k433a1_433 0 230 = 213 := by decide +kernel
theorem cr_433a1_433_1 : cntRange 433 k433a1_433 230 203 = 219 := by decide +kernel

/-- #Ẽ(F_433) = 433 (a_433 = +1) — x 구간 2 덩어리 -/
theorem cardBad_433a1_433 : card 433 c433a1.c = 433 := by
  have h1 : cntRange 433 k433a1_433 230 203 = 219 := cr_433a1_433_1
  have h0 : cntRange 433 k433a1_433 0 433 = 432 := chain cr_433a1_433_0 h1 rfl rfl rfl
  rw [card, k433a1_433_eq, h0]

/-- 433a1 : N = 433 준안정 · a_433 = +1 · w = −∏(−a_p) = +1 -/
theorem root_433a1 : rootOk c433a1 [(433, 1)] [card 433 c433a1.c] = true := by
  rw [cardBad_433a1_433]; decide +kernel

/-- 446d1 의 계수 mod 2 -/
def k446d1_2 : K := ⟨1, 1, 0, 0, 0⟩
theorem k446d1_2_eq : c446d1.c.modp 2 = k446d1_2 := by decide +kernel

theorem cr_446d1_2_0 : cntRange 2 k446d1_2 0 2 = 3 := by decide +kernel

/-- #Ẽ(F_2) = 4 (a_2 = -1) — x 구간 1 덩어리 -/
theorem cardBad_446d1_2 : card 2 c446d1.c = 4 := by
  have h0 : cntRange 2 k446d1_2 0 2 = 3 := cr_446d1_2_0
  rw [card, k446d1_2_eq, h0]

/-- 446d1 의 계수 mod 223 -/
def k446d1_223 : K := ⟨1, 222, 0, 219, 4⟩
theorem k446d1_223_eq : c446d1.c.modp 223 = k446d1_223 := by decide +kernel

theorem cr_446d1_223_0 : cntRange 223 k446d1_223 0 223 = 222 := by decide +kernel

/-- #Ẽ(F_223) = 223 (a_223 = +1) — x 구간 1 덩어리 -/
theorem cardBad_446d1_223 : card 223 c446d1.c = 223 := by
  have h0 : cntRange 223 k446d1_223 0 223 = 222 := cr_446d1_223_0
  rw [card, k446d1_223_eq, h0]

/-- 446d1 : N = 446 준안정 · a_2 = -1, a_223 = +1 · w = −∏(−a_p) = +1 -/
theorem root_446d1 : rootOk c446d1 [(2, 2), (223, 1)] [card 2 c446d1.c, card 223 c446d1.c] = true := by
  rw [cardBad_446d1_2, cardBad_446d1_223]; decide +kernel

/-- 563a1 의 계수 mod 563 -/
def k563a1_563 : K := ⟨1, 1, 1, 548, 16⟩
theorem k563a1_563_eq : c563a1.c.modp 563 = k563a1_563 := by decide +kernel

theorem cr_563a1_563_0 : cntRange 563 k563a1_563 0 177 = 186 := by decide +kernel
theorem cr_563a1_563_1 : cntRange 563 k563a1_563 177 177 = 164 := by decide +kernel
theorem cr_563a1_563_2 : cntRange 563 k563a1_563 354 177 = 180 := by decide +kernel
theorem cr_563a1_563_3 : cntRange 563 k563a1_563 531 32 = 32 := by decide +kernel

/-- #Ẽ(F_563) = 563 (a_563 = +1) — x 구간 4 덩어리 -/
theorem cardBad_563a1_563 : card 563 c563a1.c = 563 := by
  have h3 : cntRange 563 k563a1_563 531 32 = 32 := cr_563a1_563_3
  have h2 : cntRange 563 k563a1_563 354 209 = 212 := chain cr_563a1_563_2 h3 rfl rfl rfl
  have h1 : cntRange 563 k563a1_563 177 386 = 376 := chain cr_563a1_563_1 h2 rfl rfl rfl
  have h0 : cntRange 563 k563a1_563 0 563 = 562 := chain cr_563a1_563_0 h1 rfl rfl rfl
  rw [card, k563a1_563_eq, h0]

/-- 563a1 : N = 563 준안정 · a_563 = +1 · w = −∏(−a_p) = +1 -/
theorem root_563a1 : rootOk c563a1 [(563, 1)] [card 563 c563a1.c] = true := by
  rw [cardBad_563a1_563]; decide +kernel

/-- 571b1 의 계수 mod 571 -/
def k571b1_571 : K := ⟨0, 1, 1, 567, 2⟩
theorem k571b1_571_eq : c571b1.c.modp 571 = k571b1_571 := by decide +kernel

theorem cr_571b1_571_0 : cntRange 571 k571b1_571 0 175 = 173 := by decide +kernel
theorem cr_571b1_571_1 : cntRange 571 k571b1_571 175 175 = 191 := by decide +kernel
theorem cr_571b1_571_2 : cntRange 571 k571b1_571 350 175 = 154 := by decide +kernel
theorem cr_571b1_571_3 : cntRange 571 k571b1_571 525 46 = 52 := by decide +kernel

/-- #Ẽ(F_571) = 571 (a_571 = +1) — x 구간 4 덩어리 -/
theorem cardBad_571b1_571 : card 571 c571b1.c = 571 := by
  have h3 : cntRange 571 k571b1_571 525 46 = 52 := cr_571b1_571_3
  have h2 : cntRange 571 k571b1_571 350 221 = 206 := chain cr_571b1_571_2 h3 rfl rfl rfl
  have h1 : cntRange 571 k571b1_571 175 396 = 397 := chain cr_571b1_571_1 h2 rfl rfl rfl
  have h0 : cntRange 571 k571b1_571 0 571 = 570 := chain cr_571b1_571_0 h1 rfl rfl rfl
  rw [card, k571b1_571_eq, h0]

/-- 571b1 : N = 571 준안정 · a_571 = +1 · w = −∏(−a_p) = +1 -/
theorem root_571b1 : rootOk c571b1 [(571, 1)] [card 571 c571b1.c] = true := by
  rw [cardBad_571b1_571]; decide +kernel

/-- 643a1 의 계수 mod 643 -/
def k643a1_643 : K := ⟨1, 0, 0, 639, 3⟩
theorem k643a1_643_eq : c643a1.c.modp 643 = k643a1_643 := by decide +kernel

theorem cr_643a1_643_0 : cntRange 643 k643a1_643 0 155 = 168 := by decide +kernel
theorem cr_643a1_643_1 : cntRange 643 k643a1_643 155 155 = 146 := by decide +kernel
theorem cr_643a1_643_2 : cntRange 643 k643a1_643 310 155 = 155 := by decide +kernel
theorem cr_643a1_643_3 : cntRange 643 k643a1_643 465 155 = 147 := by decide +kernel
theorem cr_643a1_643_4 : cntRange 643 k643a1_643 620 23 = 26 := by decide +kernel

/-- #Ẽ(F_643) = 643 (a_643 = +1) — x 구간 5 덩어리 -/
theorem cardBad_643a1_643 : card 643 c643a1.c = 643 := by
  have h4 : cntRange 643 k643a1_643 620 23 = 26 := cr_643a1_643_4
  have h3 : cntRange 643 k643a1_643 465 178 = 173 := chain cr_643a1_643_3 h4 rfl rfl rfl
  have h2 : cntRange 643 k643a1_643 310 333 = 328 := chain cr_643a1_643_2 h3 rfl rfl rfl
  have h1 : cntRange 643 k643a1_643 155 488 = 474 := chain cr_643a1_643_1 h2 rfl rfl rfl
  have h0 : cntRange 643 k643a1_643 0 643 = 642 := chain cr_643a1_643_0 h1 rfl rfl rfl
  rw [card, k643a1_643_eq, h0]

/-- 643a1 : N = 643 준안정 · a_643 = +1 · w = −∏(−a_p) = +1 -/
theorem root_643a1 : rootOk c643a1 [(643, 1)] [card 643 c643a1.c] = true := by
  rw [cardBad_643a1_643]; decide +kernel

/-- 655a1 의 계수 mod 5 -/
def k655a1_5 : K := ⟨0, 0, 1, 2, 3⟩
theorem k655a1_5_eq : c655a1.c.modp 5 = k655a1_5 := by decide +kernel

theorem cr_655a1_5_0 : cntRange 5 k655a1_5 0 5 = 6 := by decide +kernel

/-- #Ẽ(F_5) = 7 (a_5 = -1) — x 구간 1 덩어리 -/
theorem cardBad_655a1_5 : card 5 c655a1.c = 7 := by
  have h0 : cntRange 5 k655a1_5 0 5 = 6 := cr_655a1_5_0
  rw [card, k655a1_5_eq, h0]

/-- 655a1 의 계수 mod 131 -/
def k655a1_131 : K := ⟨0, 0, 1, 118, 18⟩
theorem k655a1_131_eq : c655a1.c.modp 131 = k655a1_131 := by decide +kernel

theorem cr_655a1_131_0 : cntRange 131 k655a1_131 0 131 = 130 := by decide +kernel

/-- #Ẽ(F_131) = 131 (a_131 = +1) — x 구간 1 덩어리 -/
theorem cardBad_655a1_131 : card 131 c655a1.c = 131 := by
  have h0 : cntRange 131 k655a1_131 0 131 = 130 := cr_655a1_131_0
  rw [card, k655a1_131_eq, h0]

/-- 655a1 : N = 655 준안정 · a_5 = -1, a_131 = +1 · w = −∏(−a_p) = +1 -/
theorem root_655a1 : rootOk c655a1 [(5, 2), (131, 1)] [card 5 c655a1.c, card 131 c655a1.c] = true := by
  rw [cardBad_655a1_5, cardBad_655a1_131]; decide +kernel

/-- 681c1 의 계수 mod 3 -/
def k681c1_3 : K := ⟨0, 2, 1, 0, 2⟩
theorem k681c1_3_eq : c681c1.c.modp 3 = k681c1_3 := by decide +kernel

theorem cr_681c1_3_0 : cntRange 3 k681c1_3 0 3 = 4 := by decide +kernel

/-- #Ẽ(F_3) = 5 (a_3 = -1) — x 구간 1 덩어리 -/
theorem cardBad_681c1_3 : card 3 c681c1.c = 5 := by
  have h0 : cntRange 3 k681c1_3 0 3 = 4 := cr_681c1_3_0
  rw [card, k681c1_3_eq, h0]

/-- 681c1 의 계수 mod 227 -/
def k681c1_227 : K := ⟨0, 226, 1, 0, 2⟩
theorem k681c1_227_eq : c681c1.c.modp 227 = k681c1_227 := by decide +kernel

theorem cr_681c1_227_0 : cntRange 227 k681c1_227 0 227 = 226 := by decide +kernel

/-- #Ẽ(F_227) = 227 (a_227 = +1) — x 구간 1 덩어리 -/
theorem cardBad_681c1_227 : card 227 c681c1.c = 227 := by
  have h0 : cntRange 227 k681c1_227 0 227 = 226 := cr_681c1_227_0
  rw [card, k681c1_227_eq, h0]

/-- 681c1 : N = 681 준안정 · a_3 = -1, a_227 = +1 · w = −∏(−a_p) = +1 -/
theorem root_681c1 : rootOk c681c1 [(3, 2), (227, 1)] [card 3 c681c1.c, card 227 c681c1.c] = true := by
  rw [cardBad_681c1_3, cardBad_681c1_227]; decide +kernel

/-- 707a1 의 계수 mod 7 -/
def k707a1_7 : K := ⟨0, 1, 1, 2, 5⟩
theorem k707a1_7_eq : c707a1.c.modp 7 = k707a1_7 := by decide +kernel

theorem cr_707a1_7_0 : cntRange 7 k707a1_7 0 7 = 8 := by decide +kernel

/-- #Ẽ(F_7) = 9 (a_7 = -1) — x 구간 1 덩어리 -/
theorem cardBad_707a1_7 : card 7 c707a1.c = 9 := by
  have h0 : cntRange 7 k707a1_7 0 7 = 8 := cr_707a1_7_0
  rw [card, k707a1_7_eq, h0]

/-- 707a1 의 계수 mod 101 -/
def k707a1_101 : K := ⟨0, 1, 1, 89, 12⟩
theorem k707a1_101_eq : c707a1.c.modp 101 = k707a1_101 := by decide +kernel

theorem cr_707a1_101_0 : cntRange 101 k707a1_101 0 101 = 100 := by decide +kernel

/-- #Ẽ(F_101) = 101 (a_101 = +1) — x 구간 1 덩어리 -/
theorem cardBad_707a1_101 : card 101 c707a1.c = 101 := by
  have h0 : cntRange 101 k707a1_101 0 101 = 100 := cr_707a1_101_0
  rw [card, k707a1_101_eq, h0]

/-- 707a1 : N = 707 준안정 · a_7 = -1, a_101 = +1 · w = −∏(−a_p) = +1 -/
theorem root_707a1 : rootOk c707a1 [(7, 2), (101, 1)] [card 7 c707a1.c, card 101 c707a1.c] = true := by
  rw [cardBad_707a1_7, cardBad_707a1_101]; decide +kernel

/-- 709a1 의 계수 mod 709 -/
def k709a1_709 : K := ⟨0, 708, 1, 707, 0⟩
theorem k709a1_709_eq : c709a1.c.modp 709 = k709a1_709 := by decide +kernel

theorem cr_709a1_709_0 : cntRange 709 k709a1_709 0 141 = 149 := by decide +kernel
theorem cr_709a1_709_1 : cntRange 709 k709a1_709 141 141 = 128 := by decide +kernel
theorem cr_709a1_709_2 : cntRange 709 k709a1_709 282 141 = 132 := by decide +kernel
theorem cr_709a1_709_3 : cntRange 709 k709a1_709 423 141 = 148 := by decide +kernel
theorem cr_709a1_709_4 : cntRange 709 k709a1_709 564 141 = 149 := by decide +kernel
theorem cr_709a1_709_5 : cntRange 709 k709a1_709 705 4 = 2 := by decide +kernel

/-- #Ẽ(F_709) = 709 (a_709 = +1) — x 구간 6 덩어리 -/
theorem cardBad_709a1_709 : card 709 c709a1.c = 709 := by
  have h5 : cntRange 709 k709a1_709 705 4 = 2 := cr_709a1_709_5
  have h4 : cntRange 709 k709a1_709 564 145 = 151 := chain cr_709a1_709_4 h5 rfl rfl rfl
  have h3 : cntRange 709 k709a1_709 423 286 = 299 := chain cr_709a1_709_3 h4 rfl rfl rfl
  have h2 : cntRange 709 k709a1_709 282 427 = 431 := chain cr_709a1_709_2 h3 rfl rfl rfl
  have h1 : cntRange 709 k709a1_709 141 568 = 559 := chain cr_709a1_709_1 h2 rfl rfl rfl
  have h0 : cntRange 709 k709a1_709 0 709 = 708 := chain cr_709a1_709_0 h1 rfl rfl rfl
  rw [card, k709a1_709_eq, h0]

/-- 709a1 : N = 709 준안정 · a_709 = +1 · w = −∏(−a_p) = +1 -/
theorem root_709a1 : rootOk c709a1 [(709, 1)] [card 709 c709a1.c] = true := by
  rw [cardBad_709a1_709]; decide +kernel

/-- 718b1 의 계수 mod 2 -/
def k718b1_2 : K := ⟨1, 0, 1, 1, 0⟩
theorem k718b1_2_eq : c718b1.c.modp 2 = k718b1_2 := by decide +kernel

theorem cr_718b1_2_0 : cntRange 2 k718b1_2 0 2 = 3 := by decide +kernel

/-- #Ẽ(F_2) = 4 (a_2 = -1) — x 구간 1 덩어리 -/
theorem cardBad_718b1_2 : card 2 c718b1.c = 4 := by
  have h0 : cntRange 2 k718b1_2 0 2 = 3 := cr_718b1_2_0
  rw [card, k718b1_2_eq, h0]

/-- 718b1 의 계수 mod 359 -/
def k718b1_359 : K := ⟨1, 0, 1, 354, 0⟩
theorem k718b1_359_eq : c718b1.c.modp 359 = k718b1_359 := by decide +kernel

theorem cr_718b1_359_0 : cntRange 359 k718b1_359 0 278 = 282 := by decide +kernel
theorem cr_718b1_359_1 : cntRange 359 k718b1_359 278 81 = 76 := by decide +kernel

/-- #Ẽ(F_359) = 359 (a_359 = +1) — x 구간 2 덩어리 -/
theorem cardBad_718b1_359 : card 359 c718b1.c = 359 := by
  have h1 : cntRange 359 k718b1_359 278 81 = 76 := cr_718b1_359_1
  have h0 : cntRange 359 k718b1_359 0 359 = 358 := chain cr_718b1_359_0 h1 rfl rfl rfl
  rw [card, k718b1_359_eq, h0]

/-- 718b1 : N = 718 준안정 · a_2 = -1, a_359 = +1 · w = −∏(−a_p) = +1 -/
theorem root_718b1 : rootOk c718b1 [(2, 4), (359, 1)] [card 2 c718b1.c, card 359 c718b1.c] = true := by
  rw [cardBad_718b1_2, cardBad_718b1_359]; decide +kernel

/-- 794a1 의 계수 mod 2 -/
def k794a1_2 : K := ⟨1, 0, 1, 1, 0⟩
theorem k794a1_2_eq : c794a1.c.modp 2 = k794a1_2 := by decide +kernel

theorem cr_794a1_2_0 : cntRange 2 k794a1_2 0 2 = 3 := by decide +kernel

/-- #Ẽ(F_2) = 4 (a_2 = -1) — x 구간 1 덩어리 -/
theorem cardBad_794a1_2 : card 2 c794a1.c = 4 := by
  have h0 : cntRange 2 k794a1_2 0 2 = 3 := cr_794a1_2_0
  rw [card, k794a1_2_eq, h0]

/-- 794a1 의 계수 mod 397 -/
def k794a1_397 : K := ⟨1, 0, 1, 394, 2⟩
theorem k794a1_397_eq : c794a1.c.modp 397 = k794a1_397 := by decide +kernel

theorem cr_794a1_397_0 : cntRange 397 k794a1_397 0 251 = 237 := by decide +kernel
theorem cr_794a1_397_1 : cntRange 397 k794a1_397 251 146 = 159 := by decide +kernel

/-- #Ẽ(F_397) = 397 (a_397 = +1) — x 구간 2 덩어리 -/
theorem cardBad_794a1_397 : card 397 c794a1.c = 397 := by
  have h1 : cntRange 397 k794a1_397 251 146 = 159 := cr_794a1_397_1
  have h0 : cntRange 397 k794a1_397 0 397 = 396 := chain cr_794a1_397_0 h1 rfl rfl rfl
  rw [card, k794a1_397_eq, h0]

/-- 794a1 : N = 794 준안정 · a_2 = -1, a_397 = +1 · w = −∏(−a_p) = +1 -/
theorem root_794a1 : rootOk c794a1 [(2, 2), (397, 1)] [card 2 c794a1.c, card 397 c794a1.c] = true := by
  rw [cardBad_794a1_2, cardBad_794a1_397]; decide +kernel

/-- 817a1 의 계수 mod 19 -/
def k817a1_19 : K := ⟨0, 1, 1, 1, 6⟩
theorem k817a1_19_eq : c817a1.c.modp 19 = k817a1_19 := by decide +kernel

theorem cr_817a1_19_0 : cntRange 19 k817a1_19 0 19 = 20 := by decide +kernel

/-- #Ẽ(F_19) = 21 (a_19 = -1) — x 구간 1 덩어리 -/
theorem cardBad_817a1_19 : card 19 c817a1.c = 21 := by
  have h0 : cntRange 19 k817a1_19 0 19 = 20 := cr_817a1_19_0
  rw [card, k817a1_19_eq, h0]

/-- 817a1 의 계수 mod 43 -/
def k817a1_43 : K := ⟨0, 1, 1, 1, 6⟩
theorem k817a1_43_eq : c817a1.c.modp 43 = k817a1_43 := by decide +kernel

theorem cr_817a1_43_0 : cntRange 43 k817a1_43 0 43 = 42 := by decide +kernel

/-- #Ẽ(F_43) = 43 (a_43 = +1) — x 구간 1 덩어리 -/
theorem cardBad_817a1_43 : card 43 c817a1.c = 43 := by
  have h0 : cntRange 43 k817a1_43 0 43 = 42 := cr_817a1_43_0
  rw [card, k817a1_43_eq, h0]

/-- 817a1 : N = 817 준안정 · a_19 = -1, a_43 = +1 · w = −∏(−a_p) = +1 -/
theorem root_817a1 : rootOk c817a1 [(19, 2), (43, 1)] [card 19 c817a1.c, card 43 c817a1.c] = true := by
  rw [cardBad_817a1_19, cardBad_817a1_43]; decide +kernel

/-- 997b1 의 계수 mod 997 -/
def k997b1_997 : K := ⟨0, 996, 1, 992, 994⟩
theorem k997b1_997_eq : c997b1.c.modp 997 = k997b1_997 := by decide +kernel

theorem cr_997b1_997_0 : cntRange 997 k997b1_997 0 100 = 114 := by decide +kernel
theorem cr_997b1_997_1 : cntRange 997 k997b1_997 100 100 = 100 := by decide +kernel
theorem cr_997b1_997_2 : cntRange 997 k997b1_997 200 100 = 108 := by decide +kernel
theorem cr_997b1_997_3 : cntRange 997 k997b1_997 300 100 = 100 := by decide +kernel
theorem cr_997b1_997_4 : cntRange 997 k997b1_997 400 100 = 102 := by decide +kernel
theorem cr_997b1_997_5 : cntRange 997 k997b1_997 500 100 = 110 := by decide +kernel
theorem cr_997b1_997_6 : cntRange 997 k997b1_997 600 100 = 104 := by decide +kernel
theorem cr_997b1_997_7 : cntRange 997 k997b1_997 700 100 = 84 := by decide +kernel
theorem cr_997b1_997_8 : cntRange 997 k997b1_997 800 100 = 92 := by decide +kernel
theorem cr_997b1_997_9 : cntRange 997 k997b1_997 900 97 = 82 := by decide +kernel

/-- #Ẽ(F_997) = 997 (a_997 = +1) — x 구간 10 덩어리 -/
theorem cardBad_997b1_997 : card 997 c997b1.c = 997 := by
  have h9 : cntRange 997 k997b1_997 900 97 = 82 := cr_997b1_997_9
  have h8 : cntRange 997 k997b1_997 800 197 = 174 := chain cr_997b1_997_8 h9 rfl rfl rfl
  have h7 : cntRange 997 k997b1_997 700 297 = 258 := chain cr_997b1_997_7 h8 rfl rfl rfl
  have h6 : cntRange 997 k997b1_997 600 397 = 362 := chain cr_997b1_997_6 h7 rfl rfl rfl
  have h5 : cntRange 997 k997b1_997 500 497 = 472 := chain cr_997b1_997_5 h6 rfl rfl rfl
  have h4 : cntRange 997 k997b1_997 400 597 = 574 := chain cr_997b1_997_4 h5 rfl rfl rfl
  have h3 : cntRange 997 k997b1_997 300 697 = 674 := chain cr_997b1_997_3 h4 rfl rfl rfl
  have h2 : cntRange 997 k997b1_997 200 797 = 782 := chain cr_997b1_997_2 h3 rfl rfl rfl
  have h1 : cntRange 997 k997b1_997 100 897 = 882 := chain cr_997b1_997_1 h2 rfl rfl rfl
  have h0 : cntRange 997 k997b1_997 0 997 = 996 := chain cr_997b1_997_0 h1 rfl rfl rfl
  rw [card, k997b1_997_eq, h0]

/-- 997b1 : N = 997 준안정 · a_997 = +1 · w = −∏(−a_p) = +1 -/
theorem root_997b1 : rootOk c997b1 [(997, 1)] [card 997 c997b1.c] = true := by
  rw [cardBad_997b1_997]; decide +kernel

/-- 997c1 의 계수 mod 997 -/
def k997c1_997 : K := ⟨0, 996, 1, 973, 54⟩
theorem k997c1_997_eq : c997c1.c.modp 997 = k997c1_997 := by decide +kernel

theorem cr_997c1_997_0 : cntRange 997 k997c1_997 0 100 = 105 := by decide +kernel
theorem cr_997c1_997_1 : cntRange 997 k997c1_997 100 100 = 106 := by decide +kernel
theorem cr_997c1_997_2 : cntRange 997 k997c1_997 200 100 = 92 := by decide +kernel
theorem cr_997c1_997_3 : cntRange 997 k997c1_997 300 100 = 118 := by decide +kernel
theorem cr_997c1_997_4 : cntRange 997 k997c1_997 400 100 = 89 := by decide +kernel
theorem cr_997c1_997_5 : cntRange 997 k997c1_997 500 100 = 92 := by decide +kernel
theorem cr_997c1_997_6 : cntRange 997 k997c1_997 600 100 = 86 := by decide +kernel
theorem cr_997c1_997_7 : cntRange 997 k997c1_997 700 100 = 106 := by decide +kernel
theorem cr_997c1_997_8 : cntRange 997 k997c1_997 800 100 = 106 := by decide +kernel
theorem cr_997c1_997_9 : cntRange 997 k997c1_997 900 97 = 96 := by decide +kernel

/-- #Ẽ(F_997) = 997 (a_997 = +1) — x 구간 10 덩어리 -/
theorem cardBad_997c1_997 : card 997 c997c1.c = 997 := by
  have h9 : cntRange 997 k997c1_997 900 97 = 96 := cr_997c1_997_9
  have h8 : cntRange 997 k997c1_997 800 197 = 202 := chain cr_997c1_997_8 h9 rfl rfl rfl
  have h7 : cntRange 997 k997c1_997 700 297 = 308 := chain cr_997c1_997_7 h8 rfl rfl rfl
  have h6 : cntRange 997 k997c1_997 600 397 = 394 := chain cr_997c1_997_6 h7 rfl rfl rfl
  have h5 : cntRange 997 k997c1_997 500 497 = 486 := chain cr_997c1_997_5 h6 rfl rfl rfl
  have h4 : cntRange 997 k997c1_997 400 597 = 575 := chain cr_997c1_997_4 h5 rfl rfl rfl
  have h3 : cntRange 997 k997c1_997 300 697 = 693 := chain cr_997c1_997_3 h4 rfl rfl rfl
  have h2 : cntRange 997 k997c1_997 200 797 = 785 := chain cr_997c1_997_2 h3 rfl rfl rfl
  have h1 : cntRange 997 k997c1_997 100 897 = 891 := chain cr_997c1_997_1 h2 rfl rfl rfl
  have h0 : cntRange 997 k997c1_997 0 997 = 996 := chain cr_997c1_997_0 h1 rfl rfl rfl
  rw [card, k997c1_997_eq, h0]

/-- 997c1 : N = 997 준안정 · a_997 = +1 · w = −∏(−a_p) = +1 -/
theorem root_997c1 : rootOk c997c1 [(997, 1)] [card 997 c997c1.c] = true := by
  rw [cardBad_997c1_997]; decide +kernel

/-! ## 8. 모음 -/

/-- 18 곡선 모두 : 생성원 둘이 유리점 · 2 의 독립 증명서 (Ẽ(F_p) 전수 열거) · gcd #Ẽ(F_p) = 1 -/
theorem rankTwo_cert_all : all18.all gensOn = true ∧
    (Indep2 c389a1 ∧ gcdCard c389a1 = 1) ∧
    (Indep2 c433a1 ∧ gcdCard c433a1 = 1) ∧
    (Indep2 c446d1 ∧ gcdCard c446d1 = 1) ∧
    (Indep2 c563a1 ∧ gcdCard c563a1 = 1) ∧
    (Indep2 c571b1 ∧ gcdCard c571b1 = 1) ∧
    (Indep2 c643a1 ∧ gcdCard c643a1 = 1) ∧
    (Indep2 c655a1 ∧ gcdCard c655a1 = 1) ∧
    (Indep2 c664a1 ∧ gcdCard c664a1 = 1) ∧
    (Indep2 c681c1 ∧ gcdCard c681c1 = 1) ∧
    (Indep2 c707a1 ∧ gcdCard c707a1 = 1) ∧
    (Indep2 c709a1 ∧ gcdCard c709a1 = 1) ∧
    (Indep2 c718b1 ∧ gcdCard c718b1 = 1) ∧
    (Indep2 c794a1 ∧ gcdCard c794a1 = 1) ∧
    (Indep2 c817a1 ∧ gcdCard c817a1 = 1) ∧
    (Indep2 c916c1 ∧ gcdCard c916c1 = 1) ∧
    (Indep2 c944e1 ∧ gcdCard c944e1 = 1) ∧
    (Indep2 c997b1 ∧ gcdCard c997b1 = 1) ∧
    (Indep2 c997c1 ∧ gcdCard c997c1 = 1) :=
  ⟨gens_on_all, indep_389a1, indep_433a1, indep_446d1, indep_563a1, indep_571b1, indep_643a1, indep_655a1, indep_664a1, indep_681c1, indep_707a1, indep_709a1, indep_718b1, indep_794a1, indep_817a1, indep_916c1, indep_944e1, indep_997b1, indep_997c1⟩

/-- 준안정 15 곡선의 근호수 w = −∏(−a_p) = +1 (건너뜀 : 664a1, 916c1, 944e1) -/
theorem root_all : rootOk c389a1 [(389, 1)] [card 389 c389a1.c] = true ∧
    rootOk c433a1 [(433, 1)] [card 433 c433a1.c] = true ∧
    rootOk c446d1 [(2, 2), (223, 1)] [card 2 c446d1.c, card 223 c446d1.c] = true ∧
    rootOk c563a1 [(563, 1)] [card 563 c563a1.c] = true ∧
    rootOk c571b1 [(571, 1)] [card 571 c571b1.c] = true ∧
    rootOk c643a1 [(643, 1)] [card 643 c643a1.c] = true ∧
    rootOk c655a1 [(5, 2), (131, 1)] [card 5 c655a1.c, card 131 c655a1.c] = true ∧
    rootOk c681c1 [(3, 2), (227, 1)] [card 3 c681c1.c, card 227 c681c1.c] = true ∧
    rootOk c707a1 [(7, 2), (101, 1)] [card 7 c707a1.c, card 101 c707a1.c] = true ∧
    rootOk c709a1 [(709, 1)] [card 709 c709a1.c] = true ∧
    rootOk c718b1 [(2, 4), (359, 1)] [card 2 c718b1.c, card 359 c718b1.c] = true ∧
    rootOk c794a1 [(2, 2), (397, 1)] [card 2 c794a1.c, card 397 c794a1.c] = true ∧
    rootOk c817a1 [(19, 2), (43, 1)] [card 19 c817a1.c, card 43 c817a1.c] = true ∧
    rootOk c997b1 [(997, 1)] [card 997 c997b1.c] = true ∧
    rootOk c997c1 [(997, 1)] [card 997 c997c1.c] = true :=
  ⟨root_389a1, root_433a1, root_446d1, root_563a1, root_571b1, root_643a1, root_655a1, root_681c1, root_707a1, root_709a1, root_718b1, root_794a1, root_817a1, root_997b1, root_997c1⟩

end Trombo.RankTwo

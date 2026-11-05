/-
유체 정확해 — 삼각 다항식 셈으로 커널이 확인한 나비에–스토크스 · 오일러 고전 해 (린 4 코어)

무엇을 했나
* 2π 주기 장의 한 성분을 유한 개 항 c · e^{i(k·x)} 의 목록으로 적는다. 주파수 k 는 ℤ³ 의 정수 세 개,
  계수 c 는 가우스 유리수 (실수부 · 허수부가 모두 유리수). 2차원 장은 k_z = 0 인 항만 쓴다.
* 덧셈 (목록 잇기), 상수배, 곱 (주파수끼리 더하고 계수끼리 곱함), 편미분 ∂_j (계수에 i·k_j 를 곱함),
  라플라시안, 정규형 (같은 주파수 합치기 · 0 계수 버리기) 을 정의한다. 미분과 곱이 모두 유한 자료 위의
  정확한 대수가 되므로, 유체 방정식의 각 항을 커널이 끝까지 셈한다.
* 정규형 검사의 옳음은 정리로 따로 세운다 : 정규형이 비면 모든 푸리에 계수가 0 이다 (`isZero_sound`).
  그래서 Bool 검사 (`decide +kernel`) 가 곧 "모든 주파수에서 계수가 같다" 는 명제가 된다.

확인한 고전 정확해
1. 2차원 테일러–그린 소용돌이 (Taylor–Green 1937) : U = (sin x cos y, −cos x sin y).
   div U = 0, ΔU = −2U, (U·∇)U = −∇P (P = (cos 2x + cos 2y)/4).
   처음 받은 식 P = −(cos 2x + cos 2y)/4 는 부호가 틀렸음을 커널 셈이 잡아냈다 : (U·∇)U 의 첫 성분은 (1/2) sin 2x 이고
   −∂_x P 가 이것과 같으려면 P 의 cos 2x 계수가 +1/4 이어야 한다 (`tg_wrong_sign`).
   시간 인자 E 를 기호로 두고 (E' = −2νE 만 가정) u = E·U, p = E²·P 의 나비에–스토크스 잔차의
   모든 푸리에 계수가 0 임을 보인다.
2. 3차원 ABC 흐름 (Arnold 1965 · Childress 1970 의 Arnold–Beltrami–Childress 흐름) :
   U = (A sin z + C cos y, B sin x + A cos z, C sin y + B cos x), A · B · C 는 임의의 유리수 (기호).
   div U = 0, curl U = U (벨트라미), ΔU = −U, (U·∇)U = ∇(|U|²/2) — 그래서 압력 −|U|²/2 의 정상 오일러 해이고,
   점성이 있으면 U·E (E' = −νE) 가 나비에–스토크스 해다. 항등식 (U·∇)U = ∇(|U|²/2) − U × curl U 는
   구체 계수에서 따로 셈해 확인한다.
3. 음성 대조 : (sin x, 0, 0) 는 발산 검사에서 걸러지고, 테일러–그린 압력의 부호를 뒤집은
   −(cos 2x + cos 2y)/4 는 실패하며, ABC 바탕 장에서 curl U = −U 는 거짓으로 나온다.

정직하게 밝혀 둘 것
* 실수 · 극한 · 해석학은 없다. 장은 유한 푸리에 자료이고, "해" 는 푸리에 계수의 대수 등식이다.
  sin · cos 의 해석적 의미 (e^{iθ} 의 성질) 와 시간 인자 E(t) = e^{−2νt} 의 미분 E' = −2νE 는 바깥 사실로 받아들이고,
  여기서는 ν · E · E' 를 임의의 유리수 기호로 두고 E' = −2νE (또는 −νE) 만 가정한다.
  이 등식들은 ν · E · E' 에 대한 다항 등식이라 모든 유리수에서 성립하면 실수에서도 성립하지만, 그 넘김은 형식화하지 않았다.
  ABC 의 A · B · C 도 실수가 아니라 임의의 유리수 기호다 (같은 다항 논리로 실수에 넘어가지만 역시 형식화하지 않았다).
* 이것들은 1937 년 테일러–그린, 1965 년 아놀드 · 1970 년 차일드레스 의 고전 정확해를 커널이 정확히 다시 확인한 것이다.
* 밀레니엄 나비에–스토크스 문제 (모든 매끄러운 초기값에 대한 3차원 전역 정칙성) 는 다루지 않는다.
  어떤 미해결 문제에 대해서도 주장하지 않는다.

Core Lean 4 only : import 없음, sorry 없음, native_decide 없음, 새 공리 없음.
-/
namespace FluidExact

/-! ## 1. 가우스 유리수 -/

/-- 가우스 유리수 re + im·i -/
structure G where
  re : Rat
  im : Rat
deriving DecidableEq, Repr

namespace G
/-- 덧셈 -/
def add (x y : G) : G := ⟨x.re + y.re, x.im + y.im⟩
/-- 곱셈 (re + im·i)(re' + im'·i) -/
def mul (x y : G) : G := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
instance : Add G := ⟨add⟩
instance : Mul G := ⟨mul⟩
instance : OfNat G 0 := ⟨⟨0, 0⟩⟩
/-- 유리수 a 를 a + 0·i 로 -/
def ofRat (a : Rat) : G := ⟨a, 0⟩

@[simp] theorem add_re (x y : G) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : G) : (x + y).im = x.im + y.im := rfl
@[simp] theorem mul_re (x y : G) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : G) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] theorem zero_re : (0 : G).re = 0 := rfl
@[simp] theorem zero_im : (0 : G).im = 0 := rfl
@[simp] theorem ofRat_re (a : Rat) : (ofRat a).re = a := rfl
@[simp] theorem ofRat_im (a : Rat) : (ofRat a).im = 0 := rfl

/-- 두 가우스 유리수는 실수부와 허수부가 같으면 같다 -/
theorem ext_iff' {x y : G} : x = y ↔ x.re = y.re ∧ x.im = y.im := by
  cases x; cases y; simp
end G

/-- 가우스 유리수 등식을 실수부 · 허수부의 유리수 등식으로 쪼개 `grind` 로 끝낸다 -/
macro "gext" : tactic =>
  `(tactic| (simp only [G.ext_iff', G.add_re, G.add_im, G.mul_re, G.mul_im, G.zero_re, G.zero_im,
      G.ofRat_re, G.ofRat_im] at * <;> grind))

/-! ## 2. 주파수와 삼각 다항식 -/

/-- 주파수 k = (k_x, k_y, k_z) ∈ ℤ³ -/
structure K where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

/-- 주파수 덧셈 -/
def K.add (k l : K) : K := ⟨k.x + l.x, k.y + l.y, k.z + l.z⟩
/-- 주파수 부호 바꿈 -/
def K.neg (k : K) : K := ⟨-k.x, -k.y, -k.z⟩
/-- j 번째 성분 (0 → x, 1 → y, 그 밖 → z) -/
def K.get : K → Nat → Int
  | k, 0 => k.x
  | k, 1 => k.y
  | k, _ => k.z

/-- 한 항 c · e^{i(k·x)} -/
structure T where
  f : K
  c : G

/-- 삼각 다항식 = 항의 유한 목록 (합으로 읽는다) -/
abbrev P := List T

/-- 상수배 a · p -/
def smul (a : G) (p : P) : P := p.map fun t => ⟨t.f, a * t.c⟩
/-- 부호 바꿈 −p -/
def neg (p : P) : P := smul ⟨-1, 0⟩ p
/-- 뺄셈 p − q -/
def sub (p q : P) : P := p ++ neg q
/-- 곱 p · q : e^{ik·x} e^{il·x} = e^{i(k+l)·x} -/
def mul (p q : P) : P := p.flatMap fun s => q.map fun t => ⟨s.f.add t.f, s.c * t.c⟩
/-- 편미분 ∂_j : 계수에 i·k_j 를 곱한다 -/
def d (j : Nat) (p : P) : P := p.map fun t => ⟨t.f, ⟨0, (t.f.get j : Rat)⟩ * t.c⟩
/-- 라플라시안 Δ = ∂₀∂₀ + ∂₁∂₁ + ∂₂∂₂ -/
def lap (p : P) : P := d 0 (d 0 p) ++ d 1 (d 1 p) ++ d 2 (d 2 p)

/-- a · cos(v·x) = (a/2) e^{iv·x} + (a/2) e^{−iv·x} -/
def cosF (v : K) (a : Rat) : P := [⟨v, ⟨a / 2, 0⟩⟩, ⟨v.neg, ⟨a / 2, 0⟩⟩]
/-- a · sin(v·x) = (−ia/2) e^{iv·x} + (ia/2) e^{−iv·x} -/
def sinF (v : K) (a : Rat) : P := [⟨v, ⟨0, -a / 2⟩⟩, ⟨v.neg, ⟨0, a / 2⟩⟩]

def ex : K := ⟨1, 0, 0⟩
def ey : K := ⟨0, 1, 0⟩
def ez : K := ⟨0, 0, 1⟩

/-! ## 3. 정규형과 그 옳음 -/

/-- 항 하나를 넣는다 : 같은 주파수가 있으면 계수를 더하고, 없으면 끝에 붙인다 -/
def ins (t : T) : P → P
  | [] => [t]
  | s :: r => if s.f = t.f then ⟨s.f, s.c + t.c⟩ :: r else s :: ins t r

/-- 정규형 : 같은 주파수를 합치고 0 계수를 버린다 -/
def nf (p : P) : P := (p.foldr ins []).filter fun t => t.c != 0

/-- 정규형이 비었나 (= 0 인가) -/
def isZero (p : P) : Bool := (nf p).isEmpty
/-- 정규형 비교 : p − q 의 정규형이 비었나 -/
def eqv (p q : P) : Bool := isZero (sub p q)

/-- 주파수 k 의 푸리에 계수 (같은 주파수 항의 계수 합) — 삼각 다항식의 뜻 -/
def coef : P → K → G
  | [], _ => 0
  | t :: r, k => (if t.f = k then t.c else 0) + coef r k

@[simp] theorem coef_nil (k : K) : coef [] k = 0 := rfl
@[simp] theorem coef_cons (t : T) (r : P) (k : K) :
    coef (t :: r) k = (if t.f = k then t.c else 0) + coef r k := rfl

theorem coef_append (p q : P) (k : K) : coef (p ++ q) k = coef p k + coef q k := by
  induction p with
  | nil => simp only [List.nil_append, coef_nil]; gext
  | cons t r ih => simp only [List.cons_append, coef_cons, ih]; gext

theorem coef_smul (a : G) (p : P) (k : K) : coef (smul a p) k = a * coef p k := by
  induction p with
  | nil => simp only [smul, List.map_nil, coef_nil]; gext
  | cons t r ih =>
    simp only [smul, List.map_cons, coef_cons] at *
    rw [ih]
    by_cases h : t.f = k <;> simp only [h, ite_true, ite_false] <;> gext

theorem coef_neg (p : P) (k : K) : coef (neg p) k = ⟨-1, 0⟩ * coef p k := coef_smul _ _ _

theorem coef_sub (p q : P) (k : K) : coef (sub p q) k = coef p k + ⟨-1, 0⟩ * coef q k := by
  simp only [sub, coef_append, coef_neg]

/-- ∂_j 의 뜻 : 주파수 k 의 계수에 i·k_j 를 곱한다 -/
theorem coef_d (j : Nat) (p : P) (k : K) : coef (d j p) k = ⟨0, (k.get j : Rat)⟩ * coef p k := by
  induction p with
  | nil => simp only [d, List.map_nil, coef_nil]; gext
  | cons t r ih =>
    simp only [d, List.map_cons, coef_cons] at *
    rw [ih]
    by_cases h : t.f = k
    · subst h; simp only [ite_true]; gext
    · simp only [h, ite_false]; gext

theorem coef_ins (t : T) (acc : P) (k : K) :
    coef (ins t acc) k = (if t.f = k then t.c else 0) + coef acc k := by
  induction acc with
  | nil => rfl
  | cons s r ih =>
    simp only [ins]
    by_cases h : s.f = t.f
    · simp only [h, ite_true, coef_cons]
      by_cases hk : t.f = k <;> simp only [hk, ite_true, ite_false] <;> gext
    · simp only [h, ite_false, coef_cons, ih]; gext

theorem coef_foldr (p : P) (k : K) : coef (p.foldr ins []) k = coef p k := by
  induction p with
  | nil => rfl
  | cons t r ih => simp only [List.foldr_cons, coef_ins, ih, coef_cons]

theorem coef_filter (l : P) (k : K) : coef (l.filter fun t => t.c != 0) k = coef l k := by
  induction l with
  | nil => rfl
  | cons t r ih =>
    by_cases hc : t.c = 0
    · simp only [List.filter_cons, hc, bne_self_eq_false, Bool.false_eq_true, ite_false, ih, coef_cons]
      split <;> gext
    · have : (t.c != 0) = true := by simp [hc]
      simp only [List.filter_cons, this, ite_true, coef_cons, ih]

/-- 정규형의 계수는 원래 계수와 같다 -/
theorem coef_nf (p : P) (k : K) : coef (nf p) k = coef p k := by
  simp only [nf, coef_filter, coef_foldr]

/-- 검사의 옳음 : 정규형이 비면 모든 푸리에 계수가 0 이다 -/
theorem isZero_sound {p : P} (h : isZero p = true) (k : K) : coef p k = 0 := by
  simp only [isZero, List.isEmpty_iff] at h
  rw [← coef_nf, h]; rfl

/-- 비교의 옳음 : eqv p q 이면 모든 주파수에서 계수가 같다 -/
theorem eqv_sound {p q : P} (h : eqv p q = true) (k : K) : coef p k = coef q k := by
  have h0 := isZero_sound h k
  rw [coef_sub] at h0
  gext

/-! ## 4. 연산의 일반 법칙 (목록 수준 · 계수 수준) -/

theorem smul_append (a : G) (p q : P) : smul a (p ++ q) = smul a p ++ smul a q := by
  simp only [smul, List.map_append]

/-- ∂ 는 덧셈을 지킨다 -/
theorem d_append (j : Nat) (p q : P) : d j (p ++ q) = d j p ++ d j q := by
  simp only [d, List.map_append]

/-- ∂ 는 상수배와 바뀐다 -/
theorem d_smul (j : Nat) (a : G) (p : P) : d j (smul a p) = smul a (d j p) := by
  simp only [d, smul, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, T.mk.injEq, true_and]
  gext

theorem lap_smul (a : G) (p : P) : lap (smul a p) = smul a (lap p) := by
  simp only [lap, d_smul, smul_append]

theorem mul_append_left (p₁ p₂ q : P) : mul (p₁ ++ p₂) q = mul p₁ q ++ mul p₂ q := by
  simp only [mul, List.flatMap_append]

theorem mul_smul_left (a : G) (p q : P) : mul (smul a p) q = smul a (mul p q) := by
  induction p with
  | nil => rfl
  | cons s r ih =>
    simp only [smul, mul, List.map_cons, List.flatMap_cons, List.map_append, List.map_map] at *
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, T.mk.injEq, true_and]
    gext

theorem mul_smul_right (a : G) (p q : P) : mul p (smul a q) = smul a (mul p q) := by
  induction p with
  | nil => rfl
  | cons s r ih =>
    simp only [smul, mul, List.flatMap_cons, List.map_append, List.map_map] at *
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, T.mk.injEq, true_and]
    gext

theorem coef_mul_append_right (p q₁ q₂ : P) (k : K) :
    coef (mul p (q₁ ++ q₂)) k = coef (mul p q₁) k + coef (mul p q₂) k := by
  induction p with
  | nil => simp only [mul, List.flatMap_nil, coef_nil]; gext
  | cons s r ih =>
    simp only [mul, List.flatMap_cons, List.map_append, coef_append] at *
    rw [ih]; gext

/-! ## 5. 벡터장과 미분 연산 -/

/-- 3차원 벡터장 (성분 셋). 2차원 장은 셋째 성분을 [] 로 두고 k_z = 0 인 항만 쓴다 -/
structure V3 where
  c0 : P
  c1 : P
  c2 : P

/-- i 번째 성분 (0, 1, 그 밖 → 2) -/
def V3.get : V3 → Nat → P
  | V, 0 => V.c0
  | V, 1 => V.c1
  | V, _ => V.c2

def V3.add (V W : V3) : V3 := ⟨V.c0 ++ W.c0, V.c1 ++ W.c1, V.c2 ++ W.c2⟩
def V3.smul (a : G) (V : V3) : V3 :=
  ⟨FluidExact.smul a V.c0, FluidExact.smul a V.c1, FluidExact.smul a V.c2⟩
def V3.neg (V : V3) : V3 := V3.smul ⟨-1, 0⟩ V

/-- 발산 div V = ∂₀V₀ + ∂₁V₁ + ∂₂V₂ -/
def div (V : V3) : P := d 0 V.c0 ++ d 1 V.c1 ++ d 2 V.c2
/-- 기울기 ∇p -/
def grad (p : P) : V3 := ⟨d 0 p, d 1 p, d 2 p⟩
/-- 성분별 라플라시안 -/
def V3.lap (V : V3) : V3 := ⟨FluidExact.lap V.c0, FluidExact.lap V.c1, FluidExact.lap V.c2⟩
/-- 회전 curl V -/
def curl (V : V3) : V3 :=
  ⟨sub (d 1 V.c2) (d 2 V.c1), sub (d 2 V.c0) (d 0 V.c2), sub (d 0 V.c1) (d 1 V.c0)⟩
/-- (V·∇)w = V₀ ∂₀w + V₁ ∂₁w + V₂ ∂₂w -/
def advC (V : V3) (w : P) : P := mul V.c0 (d 0 w) ++ mul V.c1 (d 1 w) ++ mul V.c2 (d 2 w)
/-- 대류항 (V·∇)W -/
def adv (V W : V3) : V3 := ⟨advC V W.c0, advC V W.c1, advC V W.c2⟩
/-- 내적 V·W -/
def dot (V W : V3) : P := mul V.c0 W.c0 ++ mul V.c1 W.c1 ++ mul V.c2 W.c2
/-- 외적 V × W -/
def cross (V W : V3) : V3 :=
  ⟨sub (mul V.c1 W.c2) (mul V.c2 W.c1), sub (mul V.c2 W.c0) (mul V.c0 W.c2),
    sub (mul V.c0 W.c1) (mul V.c1 W.c0)⟩
/-- 성분마다 정규형 비교 -/
def eqv3 (V W : V3) : Bool := eqv V.c0 W.c0 && eqv V.c1 W.c1 && eqv V.c2 W.c2

/-- 벡터 비교의 옳음 : eqv3 V W 이면 모든 성분 · 모든 주파수에서 계수가 같다 -/
theorem eqv3_sound {V W : V3} (h : eqv3 V W = true) (i : Nat) (k : K) :
    coef (V.get i) k = coef (W.get i) k := by
  simp only [eqv3, Bool.and_eq_true] at h
  rcases i with _ | _ | i
  · exact eqv_sound h.1.1 k
  · exact eqv_sound h.1.2 k
  · exact eqv_sound h.2 k

theorem get_add (V W : V3) (i : Nat) : (V.add W).get i = V.get i ++ W.get i := by
  rcases i with _ | _ | i <;> rfl
theorem get_smul (a : G) (V : V3) (i : Nat) : (V.smul a).get i = smul a (V.get i) := by
  rcases i with _ | _ | i <;> rfl

/-! ## 6. 나비에–스토크스 잔차와 시간 인자 셈 -/

/-- 나비에–스토크스 잔차의 i 번째 성분 : ∂_t u + (u·∇)u + ∇p − νΔu,
여기서 u = E·U, ∂_t u = E'·U, p = E²·Pr (E, E' 는 시간 t 에서의 값을 나타내는 유리수 기호) -/
def nsRes (U : V3) (Pr : P) (ν E E' : Rat) (i : Nat) : P :=
  smul (G.ofRat E') (U.get i) ++ advC (U.smul (G.ofRat E)) ((U.smul (G.ofRat E)).get i)
    ++ d i (smul (G.ofRat (E * E)) Pr) ++ smul (G.ofRat (-ν)) (lap ((U.smul (G.ofRat E)).get i))

/-- 시간 인자 셈 : ΔU = λU, (U·∇)U = −∇Pr 이고 E' = λνE 이면, u = E·U, p = E²·Pr 의
나비에–스토크스 잔차는 모든 푸리에 계수가 0 이다 (잔차 = (E' − λνE)·U + E²·((U·∇)U + ∇Pr)) -/
theorem ns_of (U : V3) (Pr : P) (ν E E' lam : Rat) (i : Nat) (hi : i < 3) (k : K)
    (hl : coef ((V3.lap U).get i) k = coef ((V3.smul (G.ofRat lam) U).get i) k)
    (hp : coef ((adv U U).get i) k = coef ((V3.neg (grad Pr)).get i) k)
    (hE : E' = lam * ν * E) : coef (nsRes U Pr ν E E' i) k = 0 := by
  rcases i with _ | _ | _ | i
  all_goals first
    | omega
    | (simp only [nsRes, V3.get, V3.lap, V3.smul, V3.neg, adv, advC, grad, lap_smul, d_smul,
        mul_smul_left, mul_smul_right, coef_append, coef_smul] at *
       gext)

/-! ## 7. 테일러–그린 소용돌이 (2차원) -/

/-- U = (sin x cos y, −cos x sin y, 0) -/
def tgU : V3 := ⟨mul (sinF ex 1) (cosF ey 1), neg (mul (cosF ex 1) (sinF ey 1)), []⟩
/-- P = (cos 2x + cos 2y)/4 -/
def tgP : P := cosF ⟨2, 0, 0⟩ (1 / 4) ++ cosF ⟨0, 2, 0⟩ (1 / 4)

/-- 비압축 : div U = 0 -/
theorem tg_div : isZero (div tgU) = true := by decide +kernel
/-- 확산 : ΔU = −2U -/
theorem tg_lap : eqv3 (V3.lap tgU) (V3.smul (G.ofRat (-2)) tgU) = true := by decide +kernel
/-- 비선형항 = 압력 기울기 : (U·∇)U = −∇P, P = (cos 2x + cos 2y)/4 -/
theorem tg_pressure : eqv3 (adv tgU tgU) (V3.neg (grad tgP)) = true := by decide +kernel
/-- 램 꼴 항등식 확인 : (U·∇)U = ∇(|U|²/2) − U × curl U -/
theorem tg_lamb :
    eqv3 (adv tgU tgU)
      ((grad (smul (G.ofRat (1 / 2)) (dot tgU tgU))).add (V3.neg (cross tgU (curl tgU)))) = true := by
  decide +kernel

/-- 테일러–그린 나비에–스토크스 : 임의의 ν, E 와 E' = −2νE 에 대해 u = E·U, p = E²·P 의
잔차 ∂_t u + (u·∇)u + ∇p − νΔu 는 세 성분 모두 · 모든 주파수에서 계수 0 이다 -/
theorem tg_navier_stokes (ν E E' : Rat) (hE : E' = -2 * ν * E) (i : Nat) (hi : i < 3) (k : K) :
    coef (nsRes tgU tgP ν E E' i) k = 0 :=
  ns_of tgU tgP ν E E' (-2) i hi k (eqv3_sound tg_lap i k) (eqv3_sound tg_pressure i k) hE

/-- 비압축은 시간 인자에 상관없다 : div (E·U) = 0 -/
theorem tg_div_time (E : Rat) (k : K) : coef (div (tgU.smul (G.ofRat E))) k = 0 := by
  simp only [div, V3.smul, d_smul, coef_append, coef_smul]
  have h := isZero_sound tg_div k
  simp only [div, coef_append] at h
  gext

/-! ## 8. ABC 흐름 (3차원) — A, B, C 는 임의의 유리수 -/

/-- 바탕 장 셋 : U_A = (sin z, cos z, 0), U_B = (0, sin x, cos x), U_C = (cos y, 0, sin y) -/
def UA : V3 := ⟨sinF ez 1, cosF ez 1, []⟩
def UB : V3 := ⟨[], sinF ex 1, cosF ex 1⟩
def UC : V3 := ⟨cosF ey 1, [], sinF ey 1⟩

/-- ABC 흐름 U = (A sin z + C cos y, A cos z + B sin x, B cos x + C sin y) -/
def abc (A B C : Rat) : V3 :=
  ⟨sinF ez A ++ cosF ey C, cosF ez A ++ sinF ex B, cosF ex B ++ sinF ey C⟩

/-- U = A·U_A + B·U_B + C·U_C (목록 그대로 같다) -/
theorem abc_decomp (A B C : Rat) :
    abc A B C = ((UA.smul (G.ofRat A)).add (UB.smul (G.ofRat B))).add (UC.smul (G.ofRat C)) := by
  simp only [abc, UA, UB, UC, V3.smul, V3.add, smul, sinF, cosF, List.map_cons, List.map_nil,
    List.nil_append, List.append_nil, List.cons_append, V3.mk.injEq, List.cons.injEq, T.mk.injEq,
    true_and, and_true]
  gext

/-! ### 선형 법칙 (계수 수준) -/

theorem div_add (V W : V3) (k : K) : coef (div (V.add W)) k = coef (div V) k + coef (div W) k := by
  simp only [div, V3.add, d_append, coef_append]; gext
theorem div_smul (a : G) (V : V3) (k : K) : coef (div (V.smul a)) k = a * coef (div V) k := by
  simp only [div, V3.smul, d_smul, coef_append, coef_smul]; gext

theorem curl_add (V W : V3) (i : Nat) (k : K) :
    coef ((curl (V.add W)).get i) k = coef ((curl V).get i) k + coef ((curl W).get i) k := by
  rcases i with _ | _ | i <;>
  · simp only [curl, V3.get, V3.add, sub, neg, d_append, smul_append, coef_append]; gext
theorem curl_smul (a : G) (V : V3) (i : Nat) (k : K) :
    coef ((curl (V.smul a)).get i) k = a * coef ((curl V).get i) k := by
  rcases i with _ | _ | i <;>
  · simp only [curl, V3.get, V3.smul, sub, neg, d_smul, coef_append, coef_smul]; gext

theorem lapv_add (V W : V3) (i : Nat) (k : K) :
    coef ((V3.lap (V.add W)).get i) k = coef ((V3.lap V).get i) k + coef ((V3.lap W).get i) k := by
  rcases i with _ | _ | i <;>
  · simp only [V3.lap, V3.get, V3.add, lap, d_append, coef_append]; gext
theorem lapv_smul (a : G) (V : V3) (i : Nat) (k : K) :
    coef ((V3.lap (V.smul a)).get i) k = a * coef ((V3.lap V).get i) k := by
  rcases i with _ | _ | i <;>
  · simp only [V3.lap, V3.get, V3.smul, lap_smul, coef_smul]

theorem getc_add (V W : V3) (i : Nat) (k : K) :
    coef ((V.add W).get i) k = coef (V.get i) k + coef (W.get i) k := by
  rw [get_add, coef_append]
theorem getc_smul (a : G) (V : V3) (i : Nat) (k : K) :
    coef ((V.smul a).get i) k = a * coef (V.get i) k := by
  rw [get_smul, coef_smul]

/-! ### 바탕 장의 구체 확인 (커널 셈) -/

theorem UA_div : isZero (div UA) = true := by decide +kernel
theorem UB_div : isZero (div UB) = true := by decide +kernel
theorem UC_div : isZero (div UC) = true := by decide +kernel
theorem UA_curl : eqv3 (curl UA) UA = true := by decide +kernel
theorem UB_curl : eqv3 (curl UB) UB = true := by decide +kernel
theorem UC_curl : eqv3 (curl UC) UC = true := by decide +kernel
theorem UA_lap : eqv3 (V3.lap UA) (V3.smul (G.ofRat (-1)) UA) = true := by decide +kernel
theorem UB_lap : eqv3 (V3.lap UB) (V3.smul (G.ofRat (-1)) UB) = true := by decide +kernel
theorem UC_lap : eqv3 (V3.lap UC) (V3.smul (G.ofRat (-1)) UC) = true := by decide +kernel

/-! ### A, B, C 기호 그대로의 선형 성질 -/

/-- 비압축 : 모든 A, B, C 에서 div U = 0 -/
theorem abc_div (A B C : Rat) (k : K) : coef (div (abc A B C)) k = 0 := by
  rw [abc_decomp, div_add, div_add, div_smul, div_smul, div_smul,
    isZero_sound UA_div k, isZero_sound UB_div k, isZero_sound UC_div k]
  gext

/-- 벨트라미 : 모든 A, B, C 에서 curl U = U -/
theorem abc_beltrami (A B C : Rat) (i : Nat) (k : K) :
    coef ((curl (abc A B C)).get i) k = coef ((abc A B C).get i) k := by
  rw [abc_decomp, curl_add, curl_add, curl_smul, curl_smul, curl_smul,
    eqv3_sound UA_curl i k, eqv3_sound UB_curl i k, eqv3_sound UC_curl i k,
    getc_add, getc_add, getc_smul, getc_smul, getc_smul]

/-- 확산 : 모든 A, B, C 에서 ΔU = −U -/
theorem abc_lap (A B C : Rat) (i : Nat) (k : K) :
    coef ((V3.lap (abc A B C)).get i) k = coef ((V3.smul (G.ofRat (-1)) (abc A B C)).get i) k := by
  rw [abc_decomp, lapv_add, lapv_add, lapv_smul, lapv_smul, lapv_smul,
    eqv3_sound UA_lap i k, eqv3_sound UB_lap i k, eqv3_sound UC_lap i k]
  simp only [getc_add, getc_smul]
  gext

/-! ### 비선형항 : 쌍선형 꼴로 펼치기 -/

/-- 쌍선형 꼴 B(V, W)_i = (V·∇)W_i − ∂_i(V·W)/2. B(U, U) = 0 이 곧 (U·∇)U = ∇(|U|²/2) -/
def Bf (V W : V3) (i : Nat) : P :=
  sub (advC V (W.get i)) (d i (smul (G.ofRat (1 / 2)) (dot V W)))

theorem Bf_add_left (V V' W : V3) (i : Nat) (k : K) :
    coef (Bf (V.add V') W i) k = coef (Bf V W i) k + coef (Bf V' W i) k := by
  simp only [Bf, advC, dot, sub, neg, V3.add, mul_append_left, d_append, d_smul, smul_append,
    coef_append, coef_smul, coef_d]
  gext

theorem Bf_add_right (V W W' : V3) (i : Nat) (k : K) :
    coef (Bf V (W.add W') i) k = coef (Bf V W i) k + coef (Bf V W' i) k := by
  simp only [Bf, get_add]
  simp only [advC, dot, sub, neg, V3.add, d_append, d_smul, smul_append,
    coef_append, coef_smul, coef_d, coef_mul_append_right]
  gext

theorem Bf_smul_left (a : G) (V W : V3) (i : Nat) (k : K) :
    coef (Bf (V.smul a) W i) k = a * coef (Bf V W i) k := by
  simp only [Bf, advC, dot, sub, neg, V3.smul, mul_smul_left, smul_append,
    coef_append, coef_smul, coef_d]
  gext

theorem Bf_smul_right (a : G) (V W : V3) (i : Nat) (k : K) :
    coef (Bf V (W.smul a) i) k = a * coef (Bf V W i) k := by
  simp only [Bf, get_smul]
  simp only [advC, dot, sub, neg, V3.smul, mul_smul_right, d_smul, smul_append,
    coef_append, coef_smul, coef_d]
  gext

/-- 바탕 장 짝의 확인 : B(U_a, U_a) = 0, B(U_a, U_b) + B(U_b, U_a) = 0 -/
def quadCheck (i : Nat) : Bool :=
  isZero (Bf UA UA i) && isZero (Bf UB UB i) && isZero (Bf UC UC i) &&
  isZero (Bf UA UB i ++ Bf UB UA i) && isZero (Bf UA UC i ++ Bf UC UA i) &&
  isZero (Bf UB UC i ++ Bf UC UB i)

theorem quadCheck_ok : quadCheck 0 = true ∧ quadCheck 1 = true ∧ quadCheck 2 = true := by
  decide +kernel

/-- 정상 오일러 : 모든 A, B, C 에서 B(U, U) = 0, 곧 (U·∇)U − ∇(|U|²/2) 의 모든 계수가 0 -/
theorem abc_bf (A B C : Rat) (i : Nat) (hi : i < 3) (k : K) : coef (Bf (abc A B C) (abc A B C) i) k = 0 := by
  have hq : quadCheck i = true := by
    rcases i with _ | _ | _ | i
    · exact quadCheck_ok.1
    · exact quadCheck_ok.2.1
    · exact quadCheck_ok.2.2
    · omega
  simp only [quadCheck, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hq
  have e1 := isZero_sound h1 k
  have e2 := isZero_sound h2 k
  have e3 := isZero_sound h3 k
  have e4 := isZero_sound h4 k
  have e5 := isZero_sound h5 k
  have e6 := isZero_sound h6 k
  rw [coef_append] at e4 e5 e6
  rw [abc_decomp]
  simp only [Bf_add_left, Bf_add_right, Bf_smul_left, Bf_smul_right]
  gext

/-- 정상 오일러 (풀어 쓴 꼴) : (U·∇)U = ∇(|U|²/2) -/
theorem abc_euler (A B C : Rat) (i : Nat) (hi : i < 3) (k : K) :
    coef (advC (abc A B C) ((abc A B C).get i)) k
      = coef (d i (smul (G.ofRat (1 / 2)) (dot (abc A B C) (abc A B C)))) k := by
  have h := abc_bf A B C i hi k
  simp only [Bf, coef_sub] at h
  gext

/-- ABC 의 압력 Pr = −|U|²/2 -/
def abcP (A B C : Rat) : P := smul (G.ofRat (-1 / 2)) (dot (abc A B C) (abc A B C))

/-- 정상 오일러 (압력 꼴) : (U·∇)U = −∇Pr, Pr = −|U|²/2 -/
theorem abc_pressure (A B C : Rat) (i : Nat) (hi : i < 3) (k : K) :
    coef ((adv (abc A B C) (abc A B C)).get i) k
      = coef ((V3.neg (grad (abcP A B C))).get i) k := by
  have h := abc_euler A B C i hi k
  rcases i with _ | _ | _ | i
  all_goals first
    | omega
    | (simp only [adv, V3.get, V3.neg, V3.smul, grad, abcP, coef_smul, coef_d] at *
       gext)

/-- ABC 나비에–스토크스 : 임의의 A, B, C, ν, E 와 E' = −νE 에 대해 u = E·U, p = E²·(−|U|²/2) 의
잔차 ∂_t u + (u·∇)u + ∇p − νΔu 는 세 성분 모두 · 모든 주파수에서 계수 0 이다 (E 를 상수로 두면 정상 오일러 해) -/
theorem abc_navier_stokes (A B C ν E E' : Rat) (hE : E' = -1 * ν * E) (i : Nat) (hi : i < 3) (k : K) :
    coef (nsRes (abc A B C) (abcP A B C) ν E E' i) k = 0 :=
  ns_of (abc A B C) (abcP A B C) ν E E' (-1) i hi k (abc_lap A B C i k) (abc_pressure A B C i hi k) hE

/-- 구체 계수의 직접 확인 (기호 증명과 따로) : A = B = C = 1 과 (A, B, C) = (2, 3, 5) 에서
div U = 0, curl U = U, ΔU = −U, (U·∇)U = ∇(|U|²/2) 와 램 꼴 (U·∇)U = ∇(|U|²/2) − U × curl U -/
theorem abc_concrete :
    [(1, 1, 1), (2, 3, 5)].all (fun (t : Rat × Rat × Rat) =>
      let U := abc t.1 t.2.1 t.2.2
      isZero (div U) && eqv3 (curl U) U && eqv3 (V3.lap U) (V3.smul (G.ofRat (-1)) U) &&
      eqv3 (adv U U) (grad (smul (G.ofRat (1 / 2)) (dot U U))) &&
      eqv3 (adv U U) ((grad (smul (G.ofRat (1 / 2)) (dot U U))).add (V3.neg (cross U (curl U))))) = true := by
  decide +kernel

/-! ## 9. 음성 대조 -/

/-- 발산이 0 이 아닌 장 (sin x, 0, 0) -/
def bad : V3 := ⟨sinF ex 1, [], []⟩

/-- 검사가 걸러낸다 : 정규형이 비지 않고, 주파수 (1,0,0) 의 발산 계수가 1/2 -/
theorem bad_rejected : isZero (div bad) = false ∧ coef (div bad) ex = ⟨1 / 2, 0⟩ := by decide +kernel

/-- 그래서 (sin x, 0, 0) 은 비압축이 아니다 -/
theorem bad_not_div_free : ¬ ∀ k, coef (div bad) k = 0 := by
  intro h
  have h1 := h ex
  rw [bad_rejected.2] at h1
  exact absurd h1 (by decide +kernel)

/-- 테일러–그린 압력의 부호를 뒤집으면 (P 대신 −P = −(cos 2x + cos 2y)/4) 비교가 실패하고,
주파수 (2,0,0) 에서 첫 성분 계수가 다르다 -/
theorem tg_wrong_sign :
    eqv3 (adv tgU tgU) (V3.neg (grad (neg tgP))) = false ∧
    coef (adv tgU tgU).c0 ⟨2, 0, 0⟩ ≠ coef (V3.neg (grad (neg tgP))).c0 ⟨2, 0, 0⟩ := by
  decide +kernel

/-- 반대 회전 (curl U = −U) 은 ABC 바탕 장에서 거짓 -/
theorem UA_not_anti : eqv3 (curl UA) (V3.neg UA) = false := by decide +kernel

end FluidExact

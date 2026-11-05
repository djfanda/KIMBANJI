/-
다섯 열쇠를 깎아 오르기 — 열쇠마다 린 커널이 닫을 수 있는 데까지 (린 4 코어 · Mathlib 없음)
각 절은 «여기까지 닫음 ■» 과 «여기서 멈춤 □» 을 함께 적는다. 어느 절도 밀레니엄 문제를 풀지 않는다.
-/
namespace FiveKeys

/-! ## 1. 정사면체 · 양–밀스 — 자기 쌍대
4 차원의 2-형식은 좌표 넷에서 둘을 고르는 C(4,2) = 6 개 = 정사면체의 모서리 6 개.
호지 별 ⋆ : e01 ↔ e23 · e02 ↔ −e13 · e03 ↔ e12. ⋆⋆ = 1 이라 자기 쌍대 3 + 반자기 쌍대 3 으로 갈린다.
보고몰니 부등식(점마다의 꼴) : |F|² ≥ |F ∧ F|, 곧 a² + … + f² ≥ 2|af − be + cd| — 에너지는 위상 전하 아래로 내려가지 않는다.
□ 멈춤 : R⁴ 위 양자 양–밀스의 구성과 질량 간극 Δ > 0. -/

structure Two where (a b c d e f : Int)
def star (F : Two) : Two := ⟨F.f, -F.e, F.d, F.c, -F.b, F.a⟩
theorem star_star (F : Two) : star (star F) = F := by
  cases F; simp [star]
theorem edges_tetra : ((List.range 4).flatMap (fun i => (List.range 4).filterMap fun j => if i < j then some (i, j) else none)).length = 6 := by decide

theorem sq_nonneg' (x : Int) : 0 ≤ x * x := by have := Int.sq_nonneg x; grind
theorem bogomolny (a b c d e f : Int) :
    2 * (a * f - b * e + c * d) ≤ a*a + b*b + c*c + d*d + e*e + f*f ∧
    -2 * (a * f - b * e + c * d) ≤ a*a + b*b + c*c + d*d + e*e + f*f := by
  have h1 := sq_nonneg' (a - f); have h2 := sq_nonneg' (b + e); have h3 := sq_nonneg' (c - d)
  have h4 := sq_nonneg' (a + f); have h5 := sq_nonneg' (b - e); have h6 := sq_nonneg' (c + d)
  constructor <;> grind

/-! ## 2. 정육면체 · P 대 NP — 0 과 1 의 큐브
세 비트 함수는 2^(2^3) = 256 개. 두 입력 게이트(16 가지) 한 층으로 x · y · z · 0 · 1 에서 만들 수 있는 것은 38 개,
두 층으로는 232 개(③ 셈) — 나머지 24 개는 깊이 3 이 있어야 한다. 한 층의 38 은 커널이 센다. 크기를 세어 «만들기 어려운 함수가 있다» 를 보이는 길(섀넌)이다.
□ 멈춤 : NP 안의 한 함수가 초다항 회로를 요구함을 보이는 것. -/

def op (g a b : Nat) : Nat :=
  let na := 255 ^^^ a; let nb := 255 ^^^ b
  (if g % 2 = 1 then na &&& nb else 0) ||| (if g / 2 % 2 = 1 then na &&& b else 0) |||
  (if g / 4 % 2 = 1 then a &&& nb else 0) ||| (if g / 8 % 2 = 1 then a &&& b else 0)
def D0 : List Nat := [240, 204, 170, 0, 255]
def layer (D : List Nat) : List Nat :=
  D ++ (List.range 16).flatMap fun g => D.flatMap fun a => D.map fun b => op g a b
def distinct (D : List Nat) : List Nat := (List.range 256).filter fun t => D.contains t
/-- 한 층으로 얻는 진리표 38 개(셈으로 얻은 목록) -/
def D1 : List Nat := [0,3,5,10,12,15,17,34,48,51,60,63,68,80,85,90,95,102,119,136,153,160,165,170,175,187,192,195,204,207,221,238,240,243,245,250,252,255]
set_option maxRecDepth 100000 in
/-- 목록이 한 층의 결과와 꼭 같음(커널) -/
theorem depth_one : distinct (layer D0) = D1 ∧ D1.length = 38 := by decide +kernel

/-! ## 3. 정팔면체 · 호지 — 쌍대의 다이아몬드
복소 원환면(차원 n)의 호지 수 h^{p,q} = C(n,p) C(n,q) : 대칭 h^{p,q} = h^{q,p} = h^{n−p,n−q}, 그리고 p + q = k 의 합이 베티 수 C(2n,k).
n = 2 에서 h^{1,1} = 4 (아벨 곡면의 피카르 수 상한 · 여차원 1 은 레프셰츠가 닫음 · 전언).
□ 멈춤 : 여차원 2 이상에서 호지 류가 대수 순환의 결합임을 보이는 것. -/

def choose : Nat → Nat → Nat
  | _, 0 => 1 | 0, _ + 1 => 0 | n + 1, k + 1 => choose n k + choose n (k + 1)
def h (n p q : Nat) : Nat := choose n p * choose n q
def okTorus (n : Nat) : Bool :=
  (List.range (n + 1)).all fun p => (List.range (n + 1)).all fun q =>
    h n p q == h n q p && h n p q == h n (n - p) (n - q)
def betti (n k : Nat) : Nat := ((List.range (n + 1)).filter (fun p => p ≤ k && k - p ≤ n)).foldl (fun s p => s + h n p (k - p)) 0
def okBetti (n : Nat) : Bool := (List.range (2 * n + 1)).all fun k => betti n k == choose (2 * n) k
theorem hodge_diamonds : (List.range 7).all (fun n => okTorus n && okBetti n) = true := by decide +kernel
theorem picard_abelian_surface : h 2 1 1 = 4 := by decide

/-! ## 4. 정20면체 · 나비에–스토크스 — 2 차원이 영원한 까닭
2 차원 유체의 푸리에 세 파수 k + p + q = 0 (|k|² = A, |p|² = B, |q|² = C) 사이 주고받음의 계수는 공통 인수 × (1/C − 1/B) 등의 돌림꼴이고,
그 합이 0 (엔스트로피 보존), 1/A · 1/B · 1/C 를 곱한 합도 0 (에너지 보존). 분모를 걷어 정수 항등식으로 확인한다.
보존량이 둘이라 2 차원은 영원히 매끈하다(고전 · 전언). 3 차원에서는 엔스트로피가 보존되지 않는다(소용돌이 늘이기).
□ 멈춤 : 외력 없는 3 차원에서 영원히 매끈함 또는 유한 시간 깨짐. -/

theorem enstrophy_2d (A B C : Int) : (A*B - A*C) + (B*C - B*A) + (C*A - C*B) = 0 := by grind
theorem energy_2d (A B C : Int) : (B - C) + (C - A) + (A - B) = 0 := by grind

/-! ## 5. 정12면체 · BSD — 무게 12 의 판별식 Δ
Δ = q ∏ (1 − qⁿ)²⁴ 의 계수 τ(n) (라마누잔) : τ(1 … 6) = 1, −24, 252, −1472, 4830, −6048 · 곱셈성 τ(6) = τ(2)τ(3) · τ(10) = τ(2)τ(5) ·
헤케 τ(4) = τ(2)² − 2¹¹ · 작은 소수에서 τ(p)² ≤ 4p¹¹ (들리뉴의 한계 · 무게 12 의 «하세») — 커널이 셈.
□ 멈춤 : 해석 계수 2 이상에서 계수 등식과 BSD 공식 전체. -/

def mulTrunc (N : Nat) (P Q : List Int) : List Int :=
  (List.range N).map fun n => (List.range (n + 1)).foldl (fun s i => s + P.getD i 0 * Q.getD (n - i) 0) 0
def factor (N n : Nat) : List Int := (List.range N).map fun i => if i = 0 then 1 else if i = n then -1 else 0
def prodPow (N : Nat) : List Int :=
  (List.range (N - 1)).foldl (fun P n => (List.range 24).foldl (fun Q _ => mulTrunc N Q (factor N (n + 1))) P) ((List.range N).map fun i => if i = 0 then 1 else 0)
def tau (N : Nat) : List Int := 0 :: prodPow N         -- tau N 의 n 번째 = τ(n)
set_option maxRecDepth 100000 in
theorem tau_values :
    let t := tau 14
    t.getD 1 0 = 1 ∧ t.getD 2 0 = -24 ∧ t.getD 3 0 = 252 ∧ t.getD 4 0 = -1472 ∧ t.getD 5 0 = 4830 ∧ t.getD 6 0 = -6048 ∧
    t.getD 6 0 = t.getD 2 0 * t.getD 3 0 ∧ t.getD 10 0 = t.getD 2 0 * t.getD 5 0 ∧ t.getD 4 0 = t.getD 2 0 ^ 2 - 2 ^ 11 ∧
    (([2, 3, 5, 7, 11, 13] : List Nat).all fun p => decide ((t.getD p 0) ^ 2 ≤ 4 * (p : Int) ^ 11)) = true := by
  decide +kernel

end FiveKeys

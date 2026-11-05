/-
구 판정 증명서 — 삼각분할된 3 차원 구를 쌍별(파흐너) 이동으로 ∂Δ⁴ 까지 줄이는 수열을 커널이 확인 (린 4 코어 · 자연수 목록만)

· 복합체 K : 사면체(꼭짓점 넷의 정렬된 목록)들의 목록.
· 쌍별 이동 flip K A B : A ∪ B 가 다섯 점일 때, A 의 별 {A ∪ (B − b)} 이 K 에 정확히 있고 B 가 아직 면이 아니면
  그 별을 {B ∪ (A − a)} 로 바꾼다 (4→1 · 3→2 · 2→3 · 1→4 이동).
· 증명서 = 이동의 수열. run K 증명서 가 ∂Δ⁴ (꼭짓점 다섯 · 사면체 다섯) 에 닿으면 커널 ■.
· 다양체 검사 : 모든 삼각형이 사면체 둘에 끼고, 모든 꼭짓점의 링크가 연결된 닫힌 곡면이며 오일러 수 2 (= 2 차원 구).

전언 (고전 사실, 린 밖) : 쌍별 이동 하나는 조각적 선형(PL) 동형을 바꾸지 않는다 (공 하나를 같은 경계의 다른 공으로 바꿈).
그러므로 «증명서가 커널을 통과함» ⇒ «K 는 PL 3 차원 구» 이다. 거꾸로 모든 PL 3 차원 구에 이런 수열이 있다는 것은
파흐너 (1991) 의 정리이고, 길이의 다항 상한은 알려져 있지 않다 (미야토비치 2003 의 상한은 지수 꼴).
3 차원 구 판정이 NP 에 든다는 슐라이머 (2011) 의 증명서는 정규 곡면이라는 다른 종류다.

시범 : 두 세모의 이음 ∂Δ² * ∂Δ² (사면체 9 · 이동 2) · 16 세포의 겉 (사면체 16 · 이동 7) · 세모와 육각의 이음 (사면체 18 · 이동 5).
대조 : 토러스의 걸쳐 올림 (사면체 28) 은 삼각형 조건은 통과하지만 꼭대기 꼭짓점의 링크가 오일러 수 0 (토러스) 이라 다양체 검사에서 떨어짐 ·
       잘못된 이동은 none.

저자의 읽기 (수학 주장 아님) : 위아래 축 — 뚜껑 (푸앵카레, 구) 과 바닥 (P 대 NP, 증명서) 을 잇는 실험. 구에서 다시 정사면체 (∂Δ⁴) 로.
이 파일은 위의 유한한 사실만 판정하고, 어떤 열린 문제도 채우지 않는다.
-/
namespace SphereCert

abbrev Cx := List (List Nat)
abbrev Cert := List (List Nat × List Nat)

def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys
def srt (l : List Nat) : List Nat := l.foldr ins []
def nodup : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodup xs
def dedup {α} [BEq α] (l : List α) : List α := l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []
def sub (A f : List Nat) : Bool := A.all (f.contains ·)

/-- 쌍별 이동 -/
def flip (K : Cx) (A B : List Nat) : Option Cx :=
  let U := srt (A ++ B)
  let old := B.map (fun b => U.filter (· != b))
  let new := A.map (fun a => U.filter (· != a))
  if U.length == 5 && nodup U && old.all (K.contains ·) && (K.filter (sub A)).length == old.length
      && !(K.any (sub B)) && !(new.any (K.contains ·))
  then some (K.filter (fun f => !old.contains f) ++ new) else none

def run (K : Cx) : Cert → Option Cx
  | [] => some K
  | (A, B) :: r => match flip K A B with
    | some K' => run K' r
    | none => none

def verts (K : Cx) : List Nat := dedup K.flatten

/-- ∂Δ⁴ : 꼭짓점 다섯 · 서로 다른 사면체 다섯 (그러면 다섯 점의 네 점 부분집합 전부) -/
def isBd4 (K : Cx) : Bool :=
  K.length == 5 && (verts K).length == 5 && K.all (fun f => f.length == 4 && nodup f) && (dedup K).length == 5

def subsets3 (f : List Nat) : List (List Nat) := f.map (fun v => f.filter (· != v))

/-- 모든 삼각형이 정확히 사면체 둘에 낌 -/
def pseudo (K : Cx) : Bool := K.all (fun f => (subsets3 f).all (fun t => (K.filter (sub t)).length == 2))

def link (K : Cx) (v : Nat) : Cx := (K.filter (·.contains v)).map (fun f => f.filter (· != v))
def edges (T : Cx) : Cx := dedup (T.flatMap subsets3)

def grow (T : Cx) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S => grow T n (dedup (S ++ (T.filter (fun t => t.any (S.contains ·))).flatten))

/-- 링크가 2 차원 구 : 모서리마다 삼각형 둘 · 연결 · 오일러 수 V − E + F = 2 -/
def sphere2 (T : Cx) : Bool :=
  let V := dedup T.flatten
  let E := edges T
  (E.all (fun e => (T.filter (sub e)).length == 2)) &&
  ((grow T V.length (V.take 1)).length == V.length) &&
  (V.length + T.length == E.length + 2)

def manifold (K : Cx) : Bool := pseudo K && (verts K).all (fun v => sphere2 (link K v))

/-- 오일러 수 V − E + T − F (3 차원 닫힌 다양체는 0) -/
def euler (K : Cx) : Int :=
  let T := dedup (K.flatMap subsets3)
  let E := dedup (T.flatMap subsets3)
  (verts K).length - E.length + T.length - K.length

/-! ## 자료 (구판정.py 가 찾고, 여기서 커널이 다시 확인) -/

def join33 : Cx := [[0, 1, 3, 4], [0, 1, 3, 5], [0, 1, 4, 5], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5], [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 4, 5]]
def join33Cert : Cert := [([3, 4], [0, 1, 2]), ([3], [0, 1, 2, 5])]
def cell16 : Cx := [[0, 2, 4, 6], [0, 2, 4, 7], [0, 2, 5, 6], [0, 2, 5, 7], [0, 3, 4, 6], [0, 3, 4, 7], [0, 3, 5, 6], [0, 3, 5, 7], [1, 2, 4, 6], [1, 2, 4, 7], [1, 2, 5, 6], [1, 2, 5, 7], [1, 3, 4, 6], [1, 3, 4, 7], [1, 3, 5, 6], [1, 3, 5, 7]]
def cell16Cert : Cert := [([1, 4, 7], [2, 3]), ([1, 4], [2, 3, 6]), ([4, 6], [0, 2, 3]), ([1, 6], [2, 3, 5]), ([1], [2, 3, 5, 7]), ([6], [0, 2, 3, 5]), ([5], [0, 2, 3, 7])]
def join36 : Cx := [[0, 1, 3, 4], [0, 1, 3, 8], [0, 1, 4, 5], [0, 1, 5, 6], [0, 1, 6, 7], [0, 1, 7, 8], [0, 2, 3, 4], [0, 2, 3, 8], [0, 2, 4, 5], [0, 2, 5, 6], [0, 2, 6, 7], [0, 2, 7, 8], [1, 2, 3, 4], [1, 2, 3, 8], [1, 2, 4, 5], [1, 2, 5, 6], [1, 2, 6, 7], [1, 2, 7, 8]]
def join36Cert : Cert := [([3, 8], [0, 1, 2]), ([3], [0, 1, 2, 4]), ([8], [0, 1, 2, 7]), ([4], [0, 1, 2, 5]), ([7], [0, 1, 2, 6])]
def suspTorus : Cx := [[0, 1, 3, 7], [0, 1, 3, 8], [0, 1, 5, 7], [0, 1, 5, 8], [0, 2, 3, 7], [0, 2, 3, 8], [0, 2, 6, 7], [0, 2, 6, 8], [0, 4, 5, 7], [0, 4, 5, 8], [0, 4, 6, 7], [0, 4, 6, 8], [1, 2, 4, 7], [1, 2, 4, 8], [1, 2, 6, 7], [1, 2, 6, 8], [1, 3, 4, 7], [1, 3, 4, 8], [1, 5, 6, 7], [1, 5, 6, 8], [2, 3, 5, 7], [2, 3, 5, 8], [2, 4, 5, 7], [2, 4, 5, 8], [3, 4, 6, 7], [3, 4, 6, 8], [3, 5, 6, 7], [3, 5, 6, 8]]

/-! ## 1. 두 세모의 이음 ∂Δ² * ∂Δ² — 꼭짓점 6 · 사면체 9 -/

theorem join33_manifold : manifold join33 = true := by decide +kernel
theorem join33_euler : euler join33 = 0 := by decide +kernel
theorem join33_sphere : ((run join33 join33Cert).map isBd4) = some true := by decide +kernel
theorem join33_cert_len : join33Cert.length = 2 ∧ join33.length = 9 := by decide

/-! ## 2. 16 세포의 겉 S⁰ * S⁰ * S⁰ * S⁰ — 꼭짓점 8 · 사면체 16 -/

theorem cell16_manifold : manifold cell16 = true := by decide +kernel
theorem cell16_euler : euler cell16 = 0 := by decide +kernel
theorem cell16_sphere : ((run cell16 cell16Cert).map isBd4) = some true := by decide +kernel
theorem cell16_cert_len : cell16Cert.length = 7 ∧ cell16.length = 16 := by decide

/-! ## 3. 세모와 육각의 이음 ∂Δ² * C₆ — 꼭짓점 9 · 사면체 18 -/

theorem join36_manifold : manifold join36 = true := by decide +kernel
theorem join36_euler : euler join36 = 0 := by decide +kernel
theorem join36_sphere : ((run join36 join36Cert).map isBd4) = some true := by decide +kernel
theorem join36_cert_len : join36Cert.length = 5 ∧ join36.length = 18 := by decide

/-! ## 4. 대조 -/

/-- 토러스의 걸쳐 올림 : 삼각형 조건은 통과 -/
theorem suspTorus_pseudo : pseudo suspTorus = true := by decide +kernel
/-- 그러나 꼭대기 꼭짓점 7 의 링크 (꼭짓점 7 개 토러스) 는 오일러 수 7 − 21 + 14 = 0 이라 2 차원 구가 아님 -/
theorem suspTorus_apex_torus :
    (dedup (link suspTorus 7).flatten).length = 7 ∧ (edges (link suspTorus 7)).length = 21 ∧
    (link suspTorus 7).length = 14 ∧ sphere2 (link suspTorus 7) = false := by decide +kernel
theorem suspTorus_not_manifold : manifold suspTorus = false := by decide +kernel

/-- 잘못된 이동 : 두 세모의 이음에서 꼭짓점 0 은 사면체 여섯에 끼므로 4 → 1 로 지울 수 없음 -/
theorem illegal_move : flip join33 [0] [1, 2, 3, 4] = none := by decide +kernel
/-- 증명서의 순서를 바꾸면 통과하지 않음 -/
theorem wrong_order : run join33 join33Cert.reverse = none := by decide +kernel

/-- ∂Δ⁴ 자체 : 다양체 · 오일러 수 0 -/
def bd4 : Cx := [[1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]]
theorem bd4_ok : manifold bd4 = true ∧ euler bd4 = 0 ∧ isBd4 bd4 = true := by decide +kernel

end SphereCert

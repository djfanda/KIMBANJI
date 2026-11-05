import Trombo.SevenBalls
/-!
# 피터슨 별 — 바깥 오각형과 안쪽 오각별 (린 4 코어)

피터슨 그래프는 바깥 오각형 하나와 안쪽 오각별(«별») 하나를 다섯 살로 이은 그림이다.
아래의 고전 사실을 작은 계산 검사기로 옮기고, 검사기가 참을 돌려준다는 것을 커널이 확인한다.

1. 정의 두 가지 : 크네저 그래프 K(5,2) (꼭짓점 = {0,…,4} 의 두 원소 부분집합 10 개,
   서로소인 두 집합을 잇는다) 와 그림 꼴 (바깥 0…4 는 i ~ i+1, 안쪽 5…9 는 i ~ i+2 인 별,
   살 i ~ i+5). 두 꼴 사이의 명시적 동형을 준다. 꼭짓점 10 · 모서리 15 · 3-정칙 ·
   둘레(girth) 5 (삼각형도 사각형도 없고 오각형은 있다) · 지름 2.
2. 별을 돌려 맞추기 : {0,…,4} 의 순열 120 개가 저마다 K(5,2) 의 자기동형을 낳고 그 120 개는
   서로 다르다. 거꾸로, 인접과 비인접을 모두 지키는 어떤 꼭짓점 사상도 이 120 개 가운데 하나이다
   (가지치기 전수 탐색의 건전성 정리로 증명). 그래서 자기동형군의 크기는 정확히 120 (= S₅).
   바깥과 안쪽을 함께 k 만큼 돌리면 자기동형이고, 안쪽 별만 돌리면 (k ≢ 0) 자기동형이 아니다.
   두 고리 모두에서 i ↦ 2i 로 보내며 바깥과 안쪽을 맞바꾸는 사상은 자기동형이다 (오각형 ↔ 오각별).
   어느 두 꼭짓점 u, v 에도 u 를 v 로 보내는 자기동형이 있다 (꼭짓점 이행성).
3. 해밀턴 문제 : 피터슨 그래프에는 해밀턴 회로가 없다 (전수 탐색). 그러나 어느 한 점을 빼도
   남은 아홉 점에는 해밀턴 회로가 있다 (저해밀턴, hypohamiltonian). 해밀턴 경로는 있다.
4. 정십이면체 ↔ 피터슨 : 황금 정수 좌표의 정십이면체 스무 꼭짓점에서 맞은편 두 점 v, −v 를
   한 점으로 묶으면 (열 쌍) 그 몫 그래프가 피터슨 그래프이다. 모서리 30 은 둘씩 겹쳐 15 가 된다.
5. 스나크 : 모서리 15 개를 세 빛깔로 칠해 한 꼭짓점에 모인 세 모서리가 늘 다른 빛깔이 되게
   하는 방법은 없다 (가지치기 전수 탐색, 건전성 정리로 증명).

고전 출처 : 피터슨(J. Petersen, 1898), 크네저 그래프(Kneser, 1955), 저해밀턴 그래프,
정십이면체의 대척 몫. 위 내용은 오래전에 알려진 사실을 정수 계산으로 옮겨 커널이 확인한 것이다.
P 대 NP 를 비롯한 어떤 미해결 문제에 대해서도 주장하지 않는다. 해밀턴 회로 찾기가 일반 그래프에서
어렵다는 것은 이 파일이 다루는 범위 밖이며, 여기서는 꼭짓점 10 개짜리 한 그래프를 끝까지 센다.
-/
namespace PetersenStar

/-! ## 0. 공통 도구 : 꼭짓점 목록, 사상, 가지치기 탐색과 그 건전성 -/

/-- 꼭짓점 0 … 9 -/
def V : List Nat := List.range 10

/-- 목록으로 적은 사상의 i 번째 값 -/
def ap (f : List Nat) (i : Nat) : Nat := f.getD i 0

/-- 0 … 9 의 순열인가 : 길이 10 이고 0 … 9 를 모두 담는다 -/
def perm10 (f : List Nat) : Bool := f.length == 10 && V.all fun i => f.contains i

/-- 그래프 adj 의 자기동형인가 : 순열이고, 인접과 비인접을 모두 지킨다 -/
def isAut (adj : Nat → Nat → Bool) (f : List Nat) : Bool :=
  perm10 f && V.all fun i => V.all fun j => adj i j == adj (ap f i) (ap f j)

/-- adj₁ 에서 adj₂ 로 가는 동형인가 -/
def isIso (adj₁ adj₂ : Nat → Nat → Bool) (f : List Nat) : Bool :=
  perm10 f && V.all fun i => V.all fun j => adj₁ i j == adj₂ (ap f i) (ap f j)

/-- 모서리 목록 (i < j) -/
def edgeList (adj : Nat → Nat → Bool) : List (Nat × Nat) :=
  V.flatMap fun i => (V.filter fun j => decide (i < j) && adj i j).map fun j => (i, j)

/-- 대칭이고 고리(자기 자신과의 모서리)가 없다 -/
def simpleGraph (adj : Nat → Nat → Bool) : Bool :=
  V.all fun i => !adj i i && V.all fun j => adj i j == adj j i

/-- 모든 꼭짓점의 차수가 3 -/
def cubic (adj : Nat → Nat → Bool) : Bool := V.all fun i => (V.filter (adj i)).length == 3

/-- 삼각형이 없다 -/
def noTriangle (adj : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => V.all fun c => !(adj a b && adj b c && adj c a)

/-- 사각형이 없다 : a ~ b ~ c ~ d ~ a 이고 a ≠ c, b ≠ d 인 네 점이 없다 -/
def noSquare (adj : Nat → Nat → Bool) : Bool :=
  V.all fun a => V.all fun b => V.all fun c => V.all fun d =>
    !(adj a b && adj b c && adj c d && adj d a && a != c && b != d)

/-- 목록 l 이 회로인가 : 서로 다른 점들이고 차례로 (마지막과 처음도) 이웃한다 -/
def isCycle (adj : Nat → Nat → Bool) (l : List Nat) : Bool :=
  decide (3 ≤ l.length) && decide l.Nodup &&
    (List.range l.length).all fun t => adj (l.getD t 0) (l.getD ((t + 1) % l.length) 0)

/-- 목록 l 이 경로인가 : 서로 다른 점들이고 차례로 이웃한다 -/
def isPath (adj : Nat → Nat → Bool) (l : List Nat) : Bool :=
  decide l.Nodup && (List.range (l.length - 1)).all fun t => adj (l.getD t 0) (l.getD (t + 1) 0)

/-- 지름 ≤ 2 : 어느 두 점도 같거나, 이웃이거나, 공통 이웃이 있다 -/
def diamLe2 (adj : Nat → Nat → Bool) : Bool :=
  V.all fun i => V.all fun j => i == j || adj i j || V.any fun k => adj i k && adj k j

/-- 가지치기 탐색 : 앞마디 pre 뒤에 0 … bound−1 가운데 ok 를 통과하는 값만 붙여 가며
m 칸을 더 채운다. 끝까지 채운 모든 목록이 goal 을 만족하면 참. -/
def allExt (bound : Nat) (ok : List Nat → Nat → Bool) (goal : List Nat → Bool) :
    Nat → List Nat → Bool
  | 0, pre => goal pre
  | m + 1, pre => (List.range bound).all fun a => !ok pre a || allExt bound ok goal m (pre ++ [a])

/-- 같은 탐색으로 goal 을 만족하는 완성 목록의 수를 센다 -/
def countExt (bound : Nat) (ok : List Nat → Nat → Bool) (goal : List Nat → Bool) :
    Nat → List Nat → Nat
  | 0, pre => if goal pre then 1 else 0
  | m + 1, pre => ((List.range bound).filter (ok pre)).foldl
      (fun s a => s + countExt bound ok goal m (pre ++ [a])) 0

/-- 짝 조건 : 새 값 a (자리 pre.length) 가 앞의 모든 값 (자리 j) 과 조건 P 를 만족한다 -/
def pairOK (P : Nat → Nat → Nat → Nat → Bool) (pre : List Nat) (a : Nat) : Bool :=
  (List.range pre.length).all fun j => P j pre.length (pre.getD j 0) a

theorem getD_map_range (g : Nat → Nat) {k i : Nat} (h : i < k) :
    ((List.range k).map g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem pairOK_of (P : Nat → Nat → Nat → Nat → Bool) (g : Nat → Nat) (k : Nat)
    (h : ∀ j, j < k → P j k (g j) (g k) = true) :
    pairOK P ((List.range k).map g) (g k) = true := by
  simp only [pairOK, List.length_map, List.length_range, List.all_eq_true, List.mem_range]
  intro j hj
  rw [getD_map_range g hj]
  exact h j hj

theorem allExt_sound (bound : Nat) (ok : List Nat → Nat → Bool) (goal : List Nat → Bool)
    (g : Nat → Nat) : ∀ m k, allExt bound ok goal m ((List.range k).map g) = true →
    (∀ i, k ≤ i → i < k + m → g i < bound ∧ ok ((List.range i).map g) (g i) = true) →
    goal ((List.range (k + m)).map g) = true
  | 0, k, h, _ => by simpa [allExt] using h
  | m + 1, k, h, hg => by
    obtain ⟨hb, hok⟩ := hg k (Nat.le_refl _) (by omega)
    simp only [allExt, List.all_eq_true, List.mem_range] at h
    have h1 := h (g k) hb
    rw [hok] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    have e : (List.range k).map g ++ [g k] = (List.range (k + 1)).map g := by
      simp [List.range_succ]
    rw [e] at h1
    have := allExt_sound bound ok goal g m (k + 1) h1 (fun i h₁ h₂ => hg i (by omega) (by omega))
    rwa [show k + 1 + m = k + (m + 1) by omega] at this

/-- 건전성 : 탐색이 참을 돌려주면, 짝 조건을 모두 만족하는 어떤 함수 g 의 처음 n 값도 goal 을 만족한다.
(탐색 프로그램을 믿을 필요 없이, 탐색 결과가 함수에 대한 정리로 바뀐다.) -/
theorem search_sound (bound n : Nat) (P : Nat → Nat → Nat → Nat → Bool) (goal : List Nat → Bool)
    (g : Nat → Nat) (hs : allExt bound (pairOK P) goal n [] = true)
    (hb : ∀ i, i < n → g i < bound)
    (hP : ∀ j k, j < k → k < n → P j k (g j) (g k) = true) :
    goal ((List.range n).map g) = true := by
  have := allExt_sound bound (pairOK P) goal g n 0 (by simpa using hs)
    (fun i _ hi => ⟨hb i (by omega), pairOK_of P g i (fun j hj => hP j i hj (by omega))⟩)
  simpa using this

/-! ## 1. 두 가지 정의 : 크네저 그래프 K(5,2) 와 그림 꼴 -/

/-- 크네저 꼭짓점 : {0,…,4} 의 두 원소 부분집합 열 개 (사전 순) -/
def kv : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def kAt (v : Nat) : Nat × Nat := kv.getD v (0, 0)

/-- 크네저 그래프 K(5,2) : 두 부분집합이 서로소일 때 잇는다 -/
def adjK (i j : Nat) : Bool :=
  decide (i < 10) && decide (j < 10) &&
    let p := kAt i
    let q := kAt j
    !(p.1 == q.1 || p.1 == q.2 || p.2 == q.1 || p.2 == q.2)

/-- 그림 꼴 : 바깥 0…4 는 오각형 (i ~ i+1), 안쪽 5…9 는 오각별 (i ~ i+2), 살은 i ~ i+5 -/
def adjD (i j : Nat) : Bool :=
  if i < 5 && j < 5 then (j + 5 - i) % 5 == 1 || (i + 5 - j) % 5 == 1
  else if 5 ≤ i && i < 10 && 5 ≤ j && j < 10 then (j + 5 - i) % 5 == 2 || (i + 5 - j) % 5 == 2
  else (i < 5 && j == i + 5) || (j < 5 && i == j + 5)

/-- 그림 꼴 → 크네저 꼴 동형 : 바깥 i ↦ {2i, 2i+1} (mod 5) 이고
바깥 0,1,2,3,4 ↦ {0,1},{2,3},{0,4},{1,2},{3,4}, 안쪽 5,…,9 ↦ {2,4},{1,4},{1,3},{0,3},{0,2} -/
def isoDK : List Nat := [0, 7, 3, 4, 9, 8, 6, 5, 2, 1]
/-- 그 거꿀 사상 (크네저 → 그림) -/
def isoKD : List Nat := [0, 9, 8, 2, 3, 7, 6, 1, 5, 4]

/-- 두 꼴은 같은 그래프이다 : isoDK 는 모서리를 모서리로, 비모서리를 비모서리로 보내고,
isoKD 는 그 거꿀이다 -/
theorem drawing_iso_kneser :
    isIso adjD adjK isoDK = true ∧ isIso adjK adjD isoKD = true ∧
      V.all (fun i => ap isoKD (ap isoDK i) == i && ap isoDK (ap isoKD i) == i) = true := by
  decide +kernel

theorem basic_kneser :
    simpleGraph adjK = true ∧ (edgeList adjK).length = 15 ∧ cubic adjK = true := by decide +kernel

/-- 꼭짓점 10 · 모서리 15 · 3-정칙 -/
theorem basic_drawing :
    V.length = 10 ∧ simpleGraph adjD = true ∧ (edgeList adjD).length = 15 ∧ cubic adjD = true := by
  decide +kernel

/-- 둘레 5 : 삼각형 없음 · 사각형 없음 · 바깥 오각형 0-1-2-3-4 와 안쪽 별 5-7-9-6-8 은 오각 회로 -/
theorem girth_five :
    noTriangle adjD = true ∧ noSquare adjD = true ∧
      isCycle adjD [0, 1, 2, 3, 4] = true ∧ isCycle adjD [5, 7, 9, 6, 8] = true := by
  decide +kernel

/-- 지름 2 : 어느 두 점도 두 걸음 안이고, 0 과 2 는 이웃이 아니다 -/
theorem diameter_two : diamLe2 adjD = true ∧ adjD 0 2 = false := by decide +kernel

/-- 강정칙 매개변수 (10, 3, 0, 1) : 이웃한 두 점의 공통 이웃은 0 개, 이웃 아닌 서로 다른 두 점의
공통 이웃은 정확히 1 개 -/
theorem strongly_regular :
    V.all (fun i => V.all fun j =>
      let c := (V.filter fun k => adjD i k && adjD k j).length
      i == j || (if adjD i j then c == 0 else c == 1)) = true := by
  decide +kernel

/-! ## 2. 별을 돌려 맞추기 : 자기동형 -/

/-- x 를 목록의 모든 자리에 끼워 넣기 -/
def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- 목록의 모든 순열 -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

/-- {0,…,4} 의 순열 120 개 -/
def S5 : List (List Nat) := perms [0, 1, 2, 3, 4]

/-- 두 원소 집합 {a, b} 의 크네저 번호 -/
def kIdx (a b : Nat) : Nat :=
  let p := (min a b, max a b)
  (V.filter fun v => kAt v == p).headD 0

/-- 순열 σ 가 크네저 꼭짓점에 낳는 사상 : {a, b} ↦ {σa, σb} -/
def induced (σ : List Nat) : List Nat :=
  V.map fun v => kIdx (σ.getD (kAt v).1 0) (σ.getD (kAt v).2 0)

/-- 목록들이 서로 다른가 -/
def nodupL : List (List Nat) → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupL xs

/-- 120 개 순열이 낳는 크네저 자기동형들 -/
def autK : List (List Nat) := S5.map induced

/-- 순열 120 개는 모두 K(5,2) 의 자기동형을 낳고, 낳은 120 개의 꼭짓점 사상은 서로 다르다 -/
theorem s5_acts :
    S5.length = 120 ∧ S5.all (fun σ => isAut adjK (induced σ)) = true ∧ nodupL autK = true := by
  decide +kernel

/-- 자기동형 탐색의 짝 조건 : 자리 j, k 의 인접 여부와 값 x, y 의 인접 여부가 같다 -/
def autP (j k x y : Nat) : Bool := adjK j k == adjK x y

/-- 탐색 : 인접과 비인접을 지키는 꼭짓점 값 배치는 모두 autK 안에 있다 -/
theorem aut_search : allExt 10 (pairOK autP) (fun l => autK.contains l) 10 [] = true := by
  decide +kernel

/-- 그런 배치는 정확히 120 개 -/
theorem aut_count : countExt 10 (pairOK autP) (fun _ => true) 10 [] = 120 := by decide +kernel

/-- 자기동형군은 S₅ 이다 : 0 … 9 에서 0 … 9 로 가는 어떤 사상 g 든 인접과 비인접을 모두 지키면
(단사성은 가정하지 않는다) 순열 120 개가 낳는 사상 가운데 하나와 같다. 그 120 개가 서로 다르므로
자기동형은 정확히 120 개이다. -/
theorem aut_is_S5 (g : Nat → Nat) (hb : ∀ i, i < 10 → g i < 10)
    (h : ∀ i j, i < 10 → j < 10 → adjK (g i) (g j) = adjK i j) :
    autK.contains ((List.range 10).map g) = true :=
  search_sound 10 10 autP (fun l => autK.contains l) g aut_search hb
    (fun j k hj hk => by simp [autP, h j k (by omega) hk])

/-- 크네저 자기동형을 그림 꼴로 옮긴 것 : isoKD ∘ σ ∘ isoDK -/
def toDraw (f : List Nat) : List Nat := V.map fun i => ap isoKD (ap f (ap isoDK i))

/-- 그림 꼴의 자기동형 120 개 -/
def autD : List (List Nat) := autK.map toDraw

theorem autD_all : autD.all (isAut adjD) = true ∧ nodupL autD = true := by decide +kernel

/-- 함께 돌리기 : 바깥과 안쪽을 모두 k 칸 (i ↦ i + k) -/
def rot (k i : Nat) : Nat := if i < 5 then (i + k) % 5 else 5 + (i - 5 + k) % 5

theorem rot_aut_five : (List.range 5).all (fun k => isAut adjD (V.map (rot k))) = true := by
  decide +kernel

/-- 바깥 오각형과 안쪽 별을 함께 k 만큼 돌리면, 어떤 k 이든 자기동형이다 -/
theorem rot_aut (k : Nat) : isAut adjD (V.map (rot k)) = true := by
  have e : V.map (rot k) = V.map (rot (k % 5)) := by
    apply List.map_congr_left
    intro i _
    simp only [rot]
    split <;> omega
  rw [e]
  have h := rot_aut_five
  simp only [List.all_eq_true, List.mem_range] at h
  exact h (k % 5) (Nat.mod_lt _ (by decide))

/-- 안쪽 별만 k 칸 돌리고 바깥은 그대로 둔다 -/
def innerTurn (k i : Nat) : Nat := if i < 5 then i else 5 + (i - 5 + k) % 5

/-- 별만 돌리기는 k = 0 일 때만 자기동형이다 : k = 1, 2, 3, 4 이면 살 i ~ i+5 가 끊긴다 -/
theorem inner_turn_only :
    (List.range 5).all (fun k => isAut adjD (V.map (innerTurn k)) == (k == 0)) = true := by
  decide +kernel

/-- 맞바꾸기 : 바깥 i ↦ 안쪽 5 + 2i, 안쪽 5 + j ↦ 바깥 2j (모두 mod 5) -/
def swapStar : List Nat := [5, 7, 9, 6, 8, 0, 2, 4, 1, 3]

/-- 오각형 ↔ 오각별 : swapStar 는 자기동형이고, 바깥 오각형을 안쪽 별로, 안쪽 별을 바깥 오각형으로
보낸다. 두 번 하면 i ↦ −i (뒤집기), 네 번 하면 제자리 -/
theorem pentagon_pentagram_swap :
    isAut adjD swapStar = true ∧
      [0, 1, 2, 3, 4].all (fun i => decide (5 ≤ ap swapStar i)) = true ∧
      [5, 6, 7, 8, 9].all (fun i => decide (ap swapStar i < 5)) = true ∧
      V.map (fun i => ap swapStar (ap swapStar i)) = [0, 4, 3, 2, 1, 5, 9, 8, 7, 6] ∧
      V.map (fun i => ap swapStar (ap swapStar (ap swapStar (ap swapStar i)))) = V := by
  decide +kernel

/-- 사상 f 가 바깥 다섯을 집합 S 위로 보내는가 -/
def outerTo (f : List Nat) (S : List Nat) : Bool := [0, 1, 2, 3, 4].all fun i => S.contains (ap f i)

/-- 120 개 자기동형 가운데 바깥 오각형을 제자리로 보내는 것은 10 개 (돌리기 5 · 뒤집기 5),
바깥 오각형을 바깥 오각형 또는 안쪽 별로 보내는 것은 20 개 -/
theorem draw_symmetries :
    (autD.filter fun f => outerTo f [0, 1, 2, 3, 4]).length = 10 ∧
      (autD.filter fun f => outerTo f [0, 1, 2, 3, 4] || outerTo f [5, 6, 7, 8, 9]).length = 20 := by
  decide +kernel

/-- 꼭짓점 이행성 : 어느 두 꼭짓점 u, v 에도 u 를 v 로 보내는 자기동형이
순열 120 개가 낳는 것 가운데 있다 (크네저 꼴과 그림 꼴 모두) -/
theorem vertex_transitive :
    V.all (fun u => V.all fun v => autK.any fun f => ap f u == v) = true ∧
      V.all (fun u => V.all fun v => autD.any fun f => ap f u == v) = true := by
  decide +kernel

/-! ## 3. 해밀턴 회로는 없고, 한 점을 빼면 생긴다 -/

/-- 회로 탐색의 짝 조건 : 값이 서로 다르고, 이웃한 자리의 값은 이웃한 꼭짓점이다 -/
def hamP (j k x y : Nat) : Bool := x != y && (j + 1 != k || adjD x y)

/-- 열 자리가 다 찼을 때 마지막 점이 첫 점에 이웃하지 않는다 (회로가 닫히지 않는다) -/
def notClosed (l : List Nat) : Bool := !adjD (l.getD 9 0) (l.getD 0 0)

/-- 점 0 에서 출발하는 깊이 우선 탐색이 세는 해밀턴 회로 (방향 구별) 의 수는 0 -/
theorem ham_count_from_zero : countExt 10 (pairOK hamP) (fun l => !notClosed l) 9 [0] = 0 := by
  decide +kernel

/-- 출발점을 가리지 않는 전수 탐색 : 열 점을 모두 지나는 모든 단순 경로는 닫히지 않는다 -/
theorem ham_search : allExt 10 (pairOK hamP) notClosed 10 [] = true := by decide +kernel

/-- 피터슨 그래프에는 해밀턴 회로가 없다 : 서로 다른 열 꼭짓점 g 0, …, g 9 를 차례로 이웃하게
늘어놓는 어떤 g 도 g 9 와 g 0 을 잇지 못한다 -/
theorem no_hamiltonian_cycle :
    ¬ ∃ g : Nat → Nat, (∀ i, i < 10 → g i < 10) ∧
      (∀ i j, i < 10 → j < 10 → g i = g j → i = j) ∧
      (∀ i, i < 10 → adjD (g i) (g ((i + 1) % 10)) = true) := by
  rintro ⟨g, hb, hinj, hadj⟩
  have h := search_sound 10 10 hamP notClosed g ham_search hb (fun j k hj hk => by
    have hne : g j ≠ g k := fun e => by have := hinj j k (by omega) hk e; omega
    simp only [hamP, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
    refine ⟨hne, ?_⟩
    by_cases hjk : j + 1 = k
    · right; subst hjk; have := hadj j (by omega); rwa [Nat.mod_eq_of_lt (by omega)] at this
    · left; simpa using hjk)
  have h9 := hadj 9 (by decide)
  simp only [notClosed, getD_map_range g (show 9 < 10 by decide),
    getD_map_range g (show 0 < 10 by decide)] at h
  simp [h9] at h

/-- 해밀턴 경로는 있다 -/
theorem hamiltonian_path : isPath adjD [0, 1, 2, 3, 4, 9, 6, 8, 5, 7] = true ∧
    perm10 [0, 1, 2, 3, 4, 9, 6, 8, 5, 7] = true := by decide +kernel

/-- 점 d 를 뺀 아홉 점의 해밀턴 회로인가 : 길이 9 인 회로이고 d 를 지나지 않으며 0 … 9 안에 있다
(길이 9 · 서로 다름 · d 없음 이므로 d 아닌 아홉 점을 모두 지난다) -/
def hamAvoid (d : Nat) (c : List Nat) : Bool :=
  c.length == 9 && isCycle adjD c && !c.contains d && c.all fun x => decide (x < 10)

/-- 빼는 점마다 하나씩 : 아홉 점 회로 열 개 -/
def nineCycles : List (List Nat) :=
  [[1, 2, 3, 4, 9, 7, 5, 8, 6], [0, 4, 3, 2, 7, 9, 6, 8, 5], [0, 1, 6, 8, 3, 4, 9, 7, 5],
   [0, 1, 2, 7, 5, 8, 6, 9, 4], [0, 1, 2, 3, 8, 6, 9, 7, 5], [0, 1, 2, 7, 9, 6, 8, 3, 4],
   [0, 1, 2, 3, 8, 5, 7, 9, 4], [0, 1, 2, 3, 4, 9, 6, 8, 5], [0, 1, 6, 9, 4, 3, 2, 7, 5],
   [0, 1, 6, 8, 5, 7, 2, 3, 4]]

/-- 저해밀턴 : 어느 한 점 d 를 빼도 남은 아홉 점에 해밀턴 회로가 있다 -/
theorem hypohamiltonian : V.all (fun d => hamAvoid d (nineCycles.getD d [])) = true := by
  decide +kernel

/-- 빠진 점을 «구» 라 부르자. 점 0 을 뺀 아홉 점 회로 C₀ = 1-2-3-4-9-7-5-8-6 하나면 충분하다.
«구» 가 열 자리 가운데 어디에 있든, 그림 꼴 자기동형 120 개 가운데 0 을 «구» 로 보내는 τ 가 있고,
τ 는 C₀ 를 «구» 를 뺀 아홉 점의 해밀턴 회로로 옮긴다. 곧 «구» 의 자리는 이름만 다를 뿐,
한 점을 뺀 열 가지 그래프는 모두 같은 모양 (동형) 이고 어느 것에나 아홉 점 회로가 있다. -/
theorem remove_gu_anywhere :
    V.all (fun gu => autD.any fun τ =>
      ap τ 0 == gu && hamAvoid gu ([1, 2, 3, 4, 9, 7, 5, 8, 6].map (ap τ))) = true := by
  decide +kernel

/-- 점 u 를 뺀 그래프에서 점 v 를 뺀 그래프로 : u 를 v 로 보내는 자기동형은 남은 아홉 점을
남은 아홉 점으로 일대일로 보내며 인접과 비인접을 지킨다 (= 두 그래프의 동형) -/
theorem deleted_graphs_isomorphic :
    V.all (fun u => V.all fun v => autD.any fun τ =>
      ap τ u == v && isAut adjD τ &&
        (V.filter (· != u)).all (fun i => ap τ i != v)) = true := by
  decide +kernel

/-! ## 4. 정십이면체의 맞은편 쌍을 묶으면 피터슨 -/

open SevenBalls in
/-- 정십이면체 꼭짓점 i 와 j 가 모서리로 이웃하는가 : 거리² = 4/φ² = 8 − 4φ -/
def dEdge (i j : Nat) : Bool :=
  d2 (dodeca.getD i (g 0, g 0, g 0)) (dodeca.getD j (g 0, g 0, g 0)) == ⟨8, -4⟩

open SevenBalls in
/-- 정십이면체 꼭짓점 j 가 i 의 맞은편 (−v) 인가 -/
def antipode (i j : Nat) : Bool :=
  let v := dodeca.getD i (g 0, g 0, g 0)
  dodeca.getD j (g 0, g 0, g 0) == (neg v.1, neg v.2.1, neg v.2.2)

/-- 몫 사상 : 정십이면체 꼭짓점 번호 (SevenBalls.dodeca 의 차례) ↦ 피터슨 꼭짓점 (그림 꼴) -/
def qmap : List Nat := [0, 2, 8, 9, 9, 8, 2, 0, 4, 1, 5, 3, 6, 7, 3, 6, 7, 4, 1, 5]

def W : List Nat := List.range 20

/-- 피터슨 꼭짓점 p 위에 놓이는 정십이면체 꼭짓점들 (올올) -/
def fiber (p : Nat) : List Nat := W.filter fun i => ap qmap i == p

/-- 몫 그래프 : 두 올 사이에 정십이면체 모서리가 하나라도 있으면 잇는다 -/
def adjQ (p q : Nat) : Bool := (fiber p).any fun i => (fiber q).any fun j => dEdge i j

/-- 두 올 사이의 정십이면체 모서리 수 -/
def between (p q : Nat) : Nat :=
  ((fiber p).flatMap fun i => (fiber q).filter fun j => dEdge i j).length

/-- ± 짝 : 몫 사상은 피터슨 꼭짓점마다 정확히 두 정십이면체 꼭짓점 v 와 −v 를 보낸다.
곧 qmap i = qmap j 는 j = i 이거나 j 가 i 의 맞은편일 때, 그리고 그때만이다.
그러므로 피터슨 꼭짓점 하나를 빼는 것은 정십이면체의 ± 짝 하나 (두 꼭짓점) 를 빼는 것이다. -/
theorem fibers_are_pm_pairs :
    V.all (fun p => (fiber p).length == 2) = true ∧
      W.all (fun i => W.all fun j => (ap qmap i == ap qmap j) == (i == j || antipode i j)) = true ∧
      W.all (fun i => decide (ap qmap i < 10)) = true := by
  decide +kernel

/-- 정십이면체 ↔ 피터슨 : 맞은편 쌍을 묶은 몫 그래프는 (qmap 으로 이름 붙이면) 그림 꼴 피터슨
그래프와 모서리 하나하나까지 같다. 이웃한 두 올 사이에는 정확히 두 정십이면체 모서리 (u ~ w 와
−u ~ −w) 가 있어, 모서리 30 이 둘씩 겹쳐 15 가 된다 -/
theorem dodeca_quotient_is_petersen :
    V.all (fun p => V.all fun q => adjQ p q == adjD p q) = true ∧
      V.all (fun p => V.all fun q => if adjD p q then between p q == 2 else between p q == 0) = true ∧
      (edgeList adjQ).length = 15 ∧
      ((W.flatMap fun i => W.filter fun j => decide (i < j) && dEdge i j)).length = 30 := by
  decide +kernel

/-! ## 5. 스나크 : 모서리 세 빛깔 칠하기는 없다 -/

/-- 그림 꼴의 모서리 15 개 -/
def ED : List (Nat × Nat) := edgeList adjD

/-- 모서리 s 와 t 가 끝점을 나누는가 (서로 다른 모서리일 때) -/
def meet (s t : Nat) : Bool :=
  let e := ED.getD s (0, 0)
  let f := ED.getD t (0, 0)
  s != t && (e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2)

/-- 칠하기 짝 조건 : 만나는 두 모서리는 다른 빛깔 -/
def colP (s t x y : Nat) : Bool := !meet s t || x != y

theorem edges_fifteen : ED.length = 15 := by decide +kernel

/-- 깊이 우선 탐색이 세는 올바른 세 빛깔 칠하기의 수는 0 -/
theorem colouring_count : countExt 3 (pairOK colP) (fun _ => true) 15 [] = 0 := by decide +kernel

theorem colouring_search : allExt 3 (pairOK colP) (fun _ => false) 15 [] = true := by decide +kernel

/-- 피터슨 그래프는 모서리 세 빛깔 칠하기가 없다 (스나크) : 모서리 15 개에 빛깔 0, 1, 2 를 주는
어떤 c 도, 끝점을 나누는 두 모서리에 같은 빛깔을 준다 -/
theorem no_three_edge_colouring :
    ¬ ∃ c : Nat → Nat, (∀ s, s < 15 → c s < 3) ∧
      (∀ s t, s < 15 → t < 15 → meet s t = true → c s ≠ c t) := by
  rintro ⟨c, hb, hc⟩
  have h := search_sound 3 15 colP (fun _ => false) c colouring_search hb (fun j k hj hk => by
    simp only [colP, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
    cases hm : meet j k
    · left; rfl
    · right; exact hc j k (by omega) hk hm)
  simp at h

end PetersenStar

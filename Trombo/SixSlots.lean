/-
세 축 여섯 자리 — 일곱 밀레니엄 문제의 상태 지도 (린 4 코어, Mathlib 없이)

정육면체의 여섯 면 = ±x · ±y · ±z = 마주 보는 짝 셋 (세 축). 가운데 하나를 더해 일곱 자리.
자리 배정은 저자의 읽기이다 (수학 정리가 아니라 위치를 정한 것):
  · +z 뚜껑 = 푸앵카레 (구)          · −z 바닥 = 양–밀스 (정사면체, 자기 쌍대)
  · +x = P 대 NP (정육면체)          · −x = 호지 (정팔면체)            — 정육면체–정팔면체 쌍대
  · +y = 나비에–스토크스 (정이십면체) · −y = BSD (정십이면체)           — 정이십–정십이 쌍대
  · 가운데 = 리만 (안의 구)
층 넷 : 1 유한 · 2 다리 · 3 거시 · 4 미시(무한체). 칸 표시 :
  ■ 커널 정리 · ② 유한 계산/수치 · 전언 = 남의 정리를 옮겨 적음 · 해결 = 남이 푼 것 · □ 빈칸.

이 파일은 지도를 커널이 확인하게 한 것일 뿐, 어떤 칸도 채우지 않는다.
빈칸이 곧 열린 문제이다 (푸앵카레는 페렐만이 풀었으나, 그 미시 층을 트롬보가 형식화한 것은 아직 없다는 뜻의 빈칸).
돌려 보아도 문제의 자리만 바뀔 뿐 빈칸은 그대로라는 것까지 커널이 확인한다.

주요 정리
· dual_involutive · dual_swaps_VF · euler_five · self_dual_only_tetra : 정다면체 쌍대의 자료
· dual_axes_exact · z_axis_not_dual : 쌍대 짝은 x 축과 y 축뿐, z 축은 구 대 정사면체
· empty_cells_exact · kernel_count · census_counts · every_problem_layer4_empty : 빈칸과 ■ 의 셈
· rots_length · rots_nodup · rots_closed · rots_perm : 정육면체 회전 24 개
· rots_keep_axes · rots_transitive · stabilizer_four : 축 보존 · 추이성 · 안정자 4
· rotation_keeps_empty : 돌려도 빈자리는 채워지지 않는다
· rotation_keeps_dual_axes : 어떻게 돌려도 쌍대 짝 두 축과 구–정사면체 한 축의 짜임은 그대로
· no_axis_opens · no_pair_opens_anywhere : 양쪽에서 쌍대로 눌러야 열린다 — 어느 축도 열리지 않는다
· layoutB_dual_axes · no_three_dual_axes : 둘째 배치(뚜껑 푸앵카레 · 바닥 P 대 NP) · 720 배치 어느 것도 세 축이 모두 쌍대일 수 없다
-/

namespace Trombo.SixSlots

/-! ## 1. 정다면체 다섯과 쌍대 -/

/-- 정다면체 다섯 -/
inductive Platonic where
  | tetra   -- 정사면체
  | cube    -- 정육면체
  | octa    -- 정팔면체
  | icosa   -- 정이십면체
  | dodeca  -- 정십이면체
deriving DecidableEq, Repr

def allPlatonic : List Platonic := [.tetra, .cube, .octa, .icosa, .dodeca]

/-- 쌍대 : 꼭짓점과 면을 맞바꾼다 -/
def dual : Platonic → Platonic
  | .tetra => .tetra
  | .cube => .octa
  | .octa => .cube
  | .icosa => .dodeca
  | .dodeca => .icosa

/-- (꼭짓점 V, 모서리 E, 면 F) -/
def vef : Platonic → Nat × Nat × Nat
  | .tetra => (4, 6, 4)
  | .cube => (8, 12, 6)
  | .octa => (6, 12, 8)
  | .icosa => (12, 30, 20)
  | .dodeca => (20, 30, 12)

/-- 쌍대를 두 번 하면 제자리 -/
theorem dual_involutive : allPlatonic.all (fun p => dual (dual p) == p) = true := by decide

/-- 쌍대는 V 와 F 를 맞바꾸고 E 는 그대로 둔다 -/
theorem dual_swaps_VF :
    allPlatonic.all (fun p =>
      (vef (dual p)).1 == (vef p).2.2 && (vef (dual p)).2.1 == (vef p).2.1 &&
      (vef (dual p)).2.2 == (vef p).1) = true := by decide

/-- 오일러 V − E + F = 2 (다섯 모두) -/
theorem euler_five :
    allPlatonic.all (fun p => (vef p).1 + (vef p).2.2 == (vef p).2.1 + 2) = true := by decide

/-- 자기 쌍대는 정사면체 하나뿐 -/
theorem self_dual_only_tetra : allPlatonic.filter (fun p => dual p == p) = [.tetra] := by decide

/-- 모양 : 구 또는 정다면체 -/
inductive Shape where
  | sphere
  | solid (p : Platonic)
deriving DecidableEq, Repr

/-! ## 2. 일곱 문제와 여섯 자리 -/

/-- 일곱 밀레니엄 문제 -/
inductive Problem where
  | riemann       -- 리만
  | yangMills     -- 양–밀스
  | pnp           -- P 대 NP
  | hodge         -- 호지
  | navierStokes  -- 나비에–스토크스
  | bsd           -- BSD (버치–스위너턴다이어)
  | poincare      -- 푸앵카레
deriving DecidableEq, Repr

def allProblems : List Problem := [.riemann, .yangMills, .pnp, .hodge, .navierStokes, .bsd, .poincare]

/-- 정육면체의 여섯 면 : +x −x +y −y +z −z -/
inductive Face where
  | xp | xn | yp | yn | zp | zn
deriving DecidableEq, Repr

def allFaces : List Face := [.xp, .xn, .yp, .yn, .zp, .zn]

/-- 마주 보는 면 -/
def opp : Face → Face
  | .xp => .xn | .xn => .xp
  | .yp => .yn | .yn => .yp
  | .zp => .zn | .zn => .zp

/-- 저자의 읽기 : 면 자리에 놓인 문제 -/
def slot : Face → Problem
  | .zp => .poincare      -- 뚜껑
  | .zn => .yangMills     -- 바닥
  | .xp => .pnp
  | .xn => .hodge
  | .yp => .navierStokes
  | .yn => .bsd

/-- 가운데 자리 = 리만 -/
def center : Problem := .riemann

/-- 문제의 모양 (저자의 읽기) : 리만은 안의 구, 푸앵카레는 뚜껑의 구 -/
def shape : Problem → Shape
  | .riemann => .sphere
  | .poincare => .sphere
  | .yangMills => .solid .tetra
  | .pnp => .solid .cube
  | .hodge => .solid .octa
  | .navierStokes => .solid .icosa
  | .bsd => .solid .dodeca

theorem opp_involutive : allFaces.all (fun f => opp (opp f) == f && opp f != f) = true := by decide

/-- 일곱 문제가 여섯 면과 가운데에 하나씩 : 면마다 다른 문제, 가운데의 리만은 어느 면에도 없다 -/
theorem seven_places :
    allProblems.all (fun p =>
      (allFaces.filter (fun f => slot f == p)).length + (if p == center then 1 else 0) == 1) = true := by
  decide

/-- 면 f 와 그 맞은편이 서로 쌍대인 두 정다면체를 지는가 (배치 m 에서) -/
def dualPair (m : Face → Problem) (f : Face) : Bool :=
  match shape (m f), shape (m (opp f)) with
  | .solid p, .solid q => dual p == q
  | _, _ => false

/-- 쌍대 짝은 정확히 x 축과 y 축 : 정육면체–정팔면체, 정이십–정십이 -/
theorem dual_axes_exact : allFaces.filter (dualPair slot) = [.xp, .xn, .yp, .yn] := by decide

/-- z 축은 쌍대 짝이 아니다 : 뚜껑은 구, 바닥은 자기 쌍대인 정사면체 (짝이 맞은편이 아니라 자기 자신) -/
theorem z_axis_not_dual :
    shape (slot .zp) = .sphere ∧ shape (slot .zn) = .solid .tetra ∧ dual .tetra = .tetra ∧
    dualPair slot .zp = false ∧ dualPair slot .zn = false := by decide

/-! ## 3. 층 넷과 칸의 상태 -/

/-- 층 : 1 유한 · 2 다리 · 3 거시 · 4 미시(무한체) -/
inductive Layer where
  | finite | bridge | macro | micro
deriving DecidableEq, Repr

def allLayers : List Layer := [.finite, .bridge, .macro, .micro]

/-- 칸 : ■ 커널 정리 · ② 유한 계산/수치 · 전언 · 해결 · □ 빈칸 -/
inductive Cell where
  | kernel | numeric | cited | solved | empty
deriving DecidableEq, Repr

/-- 현재 조사표 (2026-10-28 기준의 값; 다른 모듈이 칸을 채우면 따로 고친다) -/
def status : Problem → Layer → Cell
  | .riemann, .finite => .kernel
  | .riemann, .bridge => .kernel
  | .riemann, .macro => .cited
  | .riemann, .micro => .empty
  | .yangMills, .finite => .kernel
  | .yangMills, .bridge => .cited
  | .yangMills, .macro => .empty
  | .yangMills, .micro => .empty
  | .pnp, .finite => .kernel
  | .pnp, .bridge => .kernel
  | .pnp, .macro => .cited
  | .pnp, .micro => .empty
  | .hodge, .finite => .kernel
  | .hodge, .bridge => .cited
  | .hodge, .macro => .kernel    -- 클라인 4 차 곡선의 점 세기 (KleinCount · 2 ≤ p < 400 의 소수 77 개)
  | .hodge, .micro => .empty
  | .navierStokes, .finite => .kernel
  | .navierStokes, .bridge => .kernel    -- 테일러–그린 · ABC 정확해 (FluidExact · 커널)
  | .navierStokes, .macro => .cited
  | .navierStokes, .micro => .empty
  | .bsd, .finite => .kernel
  | .bsd, .bridge => .numeric   -- 해석 계수 2 는 공 산술 (린 밖) · 대수 쪽 증명서는 RankTwo (커널 · 18 곡선)
  | .bsd, .macro => .cited
  | .bsd, .micro => .empty
  | .poincare, .finite => .kernel
  | .poincare, .bridge => .cited
  | .poincare, .macro => .solved
  | .poincare, .micro => .empty

/-- 상태가 c 인 칸의 목록 -/
def cellsOf (c : Cell) : List (Problem × Layer) :=
  allProblems.flatMap fun p => (allLayers.filter fun l => status p l == c).map fun l => (p, l)

/-- 빈칸(X) 은 정확히 일곱 문제의 미시 층 일곱 칸과 양–밀스의 거시 층 한 칸 -/
theorem empty_cells_exact :
    cellsOf .empty =
      [(.riemann, .micro), (.yangMills, .macro), (.yangMills, .micro), (.pnp, .micro),
       (.hodge, .micro), (.navierStokes, .micro), (.bsd, .micro), (.poincare, .micro)] := by decide

/-- ■ 칸은 열하나 (나비에–스토크스 다리 칸은 FluidExact · 호지 거시 칸은 KleinCount 로 ■) -/
theorem kernel_count : (cellsOf .kernel).length = 11 := by decide

/-- 스물여덟 칸의 셈 : ■ 11 · ② 1 · 전언 7 · 해결 1 · □ 8 -/
theorem census_counts :
    (cellsOf .kernel).length = 11 ∧ (cellsOf .numeric).length = 1 ∧ (cellsOf .cited).length = 7 ∧
    (cellsOf .solved).length = 1 ∧ (cellsOf .empty).length = 8 ∧
    allProblems.length * allLayers.length = 28 := by decide

/-- 모든 문제의 유한 층은 ■ -/
theorem every_problem_layer1_kernel : allProblems.all (fun p => status p .finite == .kernel) = true := by
  decide

/-- 모든 문제의 미시 층은 □ -/
theorem every_problem_layer4_empty : allProblems.all (fun p => status p .micro == .empty) = true := by
  decide

/-! ## 4. 정육면체 회전 스물넷 -/

/-- 면의 번호 -/
def Face.idx : Face → Nat
  | .xp => 0 | .xn => 1 | .yp => 2 | .yn => 3 | .zp => 4 | .zn => 5

/-- 면의 치환 : allFaces 차례대로 놓은 상(像)의 목록 -/
abbrev Perm := List Face

def apply (r : Perm) (f : Face) : Face := r.getD f.idx f

/-- 합성 : 먼저 s, 다음 r -/
def comp (r s : Perm) : Perm := allFaces.map fun f => apply r (apply s f)

def idP : Perm := allFaces

/-- z 축 둘레 사분의 일 회전 : +x → +y → −x → −y → +x -/
def qz : Perm := [.yp, .yn, .xn, .xp, .zp, .zn]

/-- x 축 둘레 사분의 일 회전 : +y → +z → −y → −z → +y -/
def qx : Perm := [.xp, .xn, .zp, .zn, .yn, .yp]

def gens : List Perm := [qz, qx]

/-- 한 걸음 : 지금 모인 회전마다 생성원을 하나 더 곱해 새것을 붙인다 -/
def step (S : List Perm) : List Perm :=
  S.foldl (fun acc g => gens.foldl (fun acc' s =>
    let h := comp s g
    if acc'.contains h then acc' else acc' ++ [h]) acc) S

def close : Nat → List Perm → List Perm
  | 0, S => S
  | n + 1, S => close n (step S)

/-- 두 생성원으로 만든 회전 모음 -/
def rots : List Perm := close 8 [idP]

/-- 역회전 : r 이 s 를 t 로 보낼 때 t 의 원래 자리 s -/
def inv (r : Perm) (t : Face) : Face := ((allFaces.find? fun s => apply r s == t)).getD t

theorem qz_order_four : comp qz (comp qz (comp qz qz)) = idP ∧ comp qz qz ≠ idP := by decide
theorem qx_order_four : comp qx (comp qx (comp qx qx)) = idP ∧ comp qx qx ≠ idP := by decide

/-- 회전은 스물넷 -/
theorem rots_length : rots.length = 24 := by decide +kernel

/-- 스물넷이 모두 다르다 -/
theorem rots_nodup :
    (List.range 24).all (fun i => (List.range 24).all (fun j =>
      i == j || rots.getD i idP != rots.getD j idP)) = true := by decide +kernel

/-- 항등과 두 생성원을 담는다 -/
theorem rots_has_gens : rots.contains idP = true ∧ rots.contains qz = true ∧ rots.contains qx = true := by
  decide +kernel

/-- 합성에 닫혀 있다 (24 × 24) — 군을 이룬다 -/
theorem rots_closed : rots.all (fun r => rots.all (fun s => rots.contains (comp r s))) = true := by
  decide +kernel

/-- 모두 여섯 면의 치환이다 (여섯 면이 하나씩 나온다) -/
theorem rots_perm :
    rots.all (fun r => r.length == 6 && allFaces.all (fun f => r.contains f)) = true := by decide +kernel

/-- 역회전이 맞다 -/
theorem rots_inv : rots.all (fun r => allFaces.all (fun t => apply r (inv r t) == t)) = true := by
  decide +kernel

/-- 마주 보는 짝은 마주 보는 짝으로 간다 : 회전은 세 축을 서로 바꿀 뿐 -/
theorem rots_keep_axes :
    rots.all (fun r => allFaces.all (fun f => apply r (opp f) == opp (apply r f))) = true := by
  decide +kernel

/-- 추이성 : 어느 자리든 어느 자리로 보낼 수 있다 -/
theorem rots_transitive :
    allFaces.all (fun f => allFaces.all (fun g => rots.any (fun r => apply r f == g))) = true := by
  decide +kernel

/-- 한 면을 고정하는 회전은 넷 (그 축 둘레 사분의 일 회전들) : 6 × 4 = 24 -/
theorem stabilizer_four :
    allFaces.all (fun f => (rots.filter (fun r => apply r f == f)).length == 4) = true := by
  decide +kernel

/-! ## 5. 돌려도 빈자리는 채워지지 않는다 -/

/-- 회전 r 뒤의 배치 : 자리 t 에는 r 이 t 로 옮겨 온 문제가 앉는다 -/
def moved (r : Perm) (t : Face) : Problem := slot (inv r t)

/-- 돌린 뒤에도 여섯 문제가 여섯 자리에 하나씩 (문제의 모임은 그대로) -/
theorem moved_is_permutation :
    rots.all (fun r => allFaces.all (fun s =>
      (allFaces.filter (fun t => moved r t == slot s)).length == 1)) = true := by decide +kernel

/-- 돌려도 빈자리는 채워지지 않는다 :
어떤 회전 r 의 뒤에도 모든 자리 t 의 미시 층은 □, 가운데(리만, 회전에 움직이지 않음)도 □.
회전은 문제를 옮길 뿐, 빈칸 X 는 그대로이다. -/
theorem rotation_keeps_empty :
    rots.all (fun r => allFaces.all (fun t => status (moved r t) .micro == .empty)) = true ∧
    status center .micro = .empty := by decide +kernel

/-- 어떻게 돌려도 쌍대 짝은 두 축 (네 면) 이고, 나머지 한 축은 구와 정사면체 -/
theorem rotation_keeps_dual_axes :
    rots.all (fun r =>
      (allFaces.filter (dualPair (moved r))).length == 4 &&
      allFaces.all (fun t => dualPair (moved r) t ||
        (shape (moved r t) == .sphere && shape (moved r (opp t)) == .solid .tetra) ||
        (shape (moved r t) == .solid .tetra && shape (moved r (opp t)) == .sphere))) = true := by
  decide +kernel

/-! ## 6. 양쪽에서 쌍대로 눌러야 열린다 -/

/-- 축이 열린다 : 배치 m 에서 면 f 와 맞은편 면, 두 미시 층 칸이 모두 채워졌을 때 -/
def opens (m : Face → Problem) (f : Face) : Bool :=
  status (m f) .micro != .empty && status (m (opp f)) .micro != .empty

/-- 어느 회전 뒤에도 어느 축도 열리지 않는다 -/
theorem no_axis_opens : rots.all (fun r => allFaces.all (fun f => !opens (moved r) f)) = true := by
  decide +kernel

/-- 회전에 그치지 않고 어떤 두 문제를 마주 세워도 열리지 않는다 (미시 층이 모두 □ 이므로) -/
theorem no_pair_opens_anywhere :
    allProblems.all (fun p => allProblems.all (fun q =>
      !(status p .micro != .empty && status q .micro != .empty))) = true := by decide


/-! ## 7. 저자의 둘째 배치 — 뚜껑 푸앵카레 · 바닥 P 대 NP

저자의 읽기 (2026-10-28) : 뚜껑 = 푸앵카레 (구) · 바닥 = P 대 NP (정육면체) · 옆 두 축 = 양–밀스 (정사면체) ↔ 호지 (정팔면체) ·
나비에–스토크스 (정이십면체) ↔ BSD (정십이면체) · 가운데 = 리만.
이 배치에서 쌍대 짝은 y 축 하나뿐이고, x 축은 정사면체–정팔면체로 쌍대가 아니라 공간을 함께 채우는 짝이다
(정팔면체는 정사면체의 모서리 중점을 이은 것 — 정사면체 · 정팔면체 벌집 · 고전 사실, 여기서는 이름만 적음).
아래는 «여섯 문제를 여섯 면에 어떻게 놓아도 세 축이 모두 쌍대 짝이 될 수는 없다» 를 720 가지 배치 전부에서 확인한다.
-/

/-- 둘째 배치 -/
def slotB : Face → Problem
  | .zp => .poincare      -- 뚜껑
  | .zn => .pnp           -- 바닥
  | .xp => .yangMills
  | .xn => .hodge
  | .yp => .navierStokes
  | .yn => .bsd

/-- 둘째 배치에서 쌍대 짝은 y 축 (정이십–정십이) 하나뿐 -/
theorem layoutB_dual_axes : allFaces.filter (dualPair slotB) = [.yp, .yn] := by decide

/-- 둘째 배치의 x 축은 정사면체–정팔면체, z 축은 구–정육면체 -/
theorem layoutB_shapes :
    shape (slotB .xp) = .solid .tetra ∧ shape (slotB .xn) = .solid .octa ∧
    shape (slotB .zp) = .sphere ∧ shape (slotB .zn) = .solid .cube := by decide

/-- 여섯 원소 목록의 치환 (직접 셈 · 연료 n 으로 구조 재귀) -/
def permsN : Nat → List Problem → List (List Problem)
  | 0, _ => [[]]
  | n + 1, l => if l = [] then [[]] else l.flatMap (fun x => (permsN n (l.erase x)).map (x :: ·))

def perms (l : List Problem) : List (List Problem) := permsN l.length l

def sixProblems : List Problem := [.yangMills, .pnp, .hodge, .navierStokes, .bsd, .poincare]

/-- 면 차례 [+x, −x, +y, −y, +z, −z] 에 문제 목록을 놓은 배치 -/
def place (l : List Problem) : Face → Problem
  | .xp => l.getD 0 .riemann | .xn => l.getD 1 .riemann
  | .yp => l.getD 2 .riemann | .yn => l.getD 3 .riemann
  | .zp => l.getD 4 .riemann | .zn => l.getD 5 .riemann

/-- 쌍대 짝인 축의 수 (0 ~ 3) -/
def dualAxisCount (m : Face → Problem) : Nat :=
  [Face.xp, .yp, .zp].countP (fun f => dualPair m f)

theorem perms_count : (perms sixProblems).length = 720 := by decide +kernel

/-- 720 가지 배치 어느 것도 세 축이 모두 쌍대 짝이 되지 않는다 (가장 많아야 둘) -/
theorem no_three_dual_axes : (perms sixProblems).all (fun l => decide (dualAxisCount (place l) ≤ 2)) = true := by
  decide +kernel

/-- 두 축이 쌍대인 배치는 있다 (첫째 배치) · 둘째 배치는 하나 -/
theorem layout_counts : dualAxisCount slot = 2 ∧ dualAxisCount slotB = 1 := by decide

/-- 둘째 배치에서도 미시 층은 모두 비어 있고, 어떤 축도 열리지 않는다 (상태는 문제에 붙어 있으므로 배치와 무관) -/
theorem layoutB_still_empty :
    allFaces.all (fun f => status (slotB f) .micro == .empty) = true := by decide

end Trombo.SixSlots

/-
  Kimbanji_CubeNets.lean  (2026-11-04)
  정육면체 전개도 11개의 유한 검증. 핵심 Lean 만 사용(Mathlib 불필요).
  1) 정육면체 꼭짓점 그래프의 신장나무 384개, 대칭군 48 아래 궤도 11개(크기 24 가 6개, 48 이 5개).
  2) 11개 전개도 모양: 6칸, 굴려 접으면 여섯 면이 모두 다름, 평면 대칭 아래 서로 다른 모양, 고정 모양 64개.
  3) 호지 미덮 궤도 11개: 호지형 (2,2), 궤도 크기 검산, 전개도 쪽 궤도 크기 다중집합과 다름.
  호지 추측과 연결되었다는 주장은 없다. 두 개의 11 사이의 구조 대응은 이 파일에서 부정되는 쪽(크기)만 증명한다.
-/
namespace CubeNets

/-! ## 1. 꼭짓점 그래프의 신장나무 -/
def edges : List (Nat × Nat) :=
  [(0,1),(2,3),(4,5),(6,7),(0,2),(1,3),(4,6),(5,7),(0,4),(1,5),(2,6),(3,7)]

def merge (lab : List Nat) (a b : Nat) : Option (List Nat) :=
  let la := lab.getD a 0
  let lb := lab.getD b 0
  if la = lb then none else some (lab.map fun x => if x = lb then la else x)

def step (s : Nat) (acc : Option (List Nat)) (ie : Nat × (Nat × Nat)) : Option (List Nat) :=
  match acc with
  | none => none
  | some lab => if s.testBit ie.1 then merge lab ie.2.1 ie.2.2 else some lab

def isTree (s : Nat) : Bool :=
  ((List.range 12).countP (fun i => s.testBit i) == 7) &&
  (((List.range 12).zip edges).foldl (step s) (some (List.range 8))).isSome

def treeMasks : List Nat := (List.range 4096).filter isTree

def bitPerms : List (List Nat) := [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]

def vmap (p : List Nat) (c v : Nat) : Nat :=
  (List.range 3).foldl (fun r k => if (v ^^^ c).testBit k then r + 2 ^ (p.getD k 0) else r) 0

def edgeIdx (u v : Nat) : Nat :=
  let a := min u v
  let b := max u v
  ((List.range 12).find? (fun i => edges.getD i (0,0) == (a,b))).getD 99

/-- 48 개 대칭을 모서리 번호의 치환으로 -/
def edgePerms : List (List Nat) :=
  bitPerms.flatMap fun p => (List.range 8).map fun c =>
    edges.map fun e => edgeIdx (vmap p c e.1) (vmap p c e.2)

def img (g : List Nat) (s : Nat) : Nat :=
  (List.range 12).foldl (fun r i => if s.testBit i then r + 2 ^ (g.getD i 99) else r) 0

def isCanon (s : Nat) : Bool := edgePerms.all fun g => s ≤ img g s

def stabSize (s : Nat) : Nat := (edgePerms.filter fun g => img g s == s).length

def canonTrees : List Nat := treeMasks.filter isCanon

def orbitSizes : List Nat := canonTrees.map fun s => 48 / stabSize s

theorem group_48 : edgePerms.length = 48 := by decide +kernel

theorem perms_are_permutations :
    edgePerms.all (fun g => (List.range 12).all fun i => g.contains i) = true := by decide +kernel

theorem trees_384 : treeMasks.length = 384 := by decide +kernel

theorem orbits_11 : canonTrees.length = 11 := by decide +kernel

theorem orbit_sizes_sum : orbitSizes.foldl (· + ·) 0 = 384 := by decide +kernel

theorem orbit_sizes_count :
    (orbitSizes.filter (· == 24)).length = 6 ∧ (orbitSizes.filter (· == 48)).length = 5 := by
  decide +kernel

/-! ## 2. 평면 전개도 11개 -/
abbrev Cell := Int × Int

def netCells : List (List Cell) := [
  [(0, 0), (0, 1), (0, 2), (1, 1), (2, 1), (3, 1)],
  [(0, 0), (0, 1), (1, 1), (1, 2), (2, 1), (3, 1)],
  [(0, 0), (0, 1), (1, 1), (2, 1), (2, 2), (3, 1)],
  [(0, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2)],
  [(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1)],
  [(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2)],
  [(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 1)],
  [(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 2)],
  [(0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 3)],
  [(0, 0), (0, 1), (0, 2), (1, 2), (1, 3), (1, 4)],
  [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 3)]]

def dirs : List Cell := [(1,0),(-1,0),(0,1),(0,-1)]

abbrev St := Nat × Nat × Nat × Nat × Nat × Nat

def roll (s : St) (d : Cell) : St :=
  match s with
  | (b,t,n,so,e,w) =>
    if d == (1,0) then (e,w,n,so,t,b)
    else if d == (-1,0) then (w,e,n,so,b,t)
    else if d == (0,1) then (n,so,t,b,e,w)
    else (so,n,b,t,e,w)

def expand (cells : List Cell) (st : List (Cell × St)) : List (Cell × St) :=
  st.foldl (fun acc cs =>
    dirs.foldl (fun acc2 d =>
      let c2 : Cell := (cs.1.1 + d.1, cs.1.2 + d.2)
      if cells.contains c2 && !(acc2.any fun x => x.1 == c2) then acc2 ++ [(c2, roll cs.2 d)] else acc2)
      acc) st

def foldAll (cells : List Cell) : List (Cell × St) :=
  (List.range 6).foldl (fun st _ => expand cells st) [(cells.headD (0,0), (0,1,2,3,4,5))]

def foldOK (cells : List Cell) : Bool :=
  cells.length == 6 && (foldAll cells).length == 6 &&
  (List.range 6).all fun f => (foldAll cells).any fun x => x.2.1 == f

def adjCount (cells : List Cell) : Nat :=
  (cells.map fun c => (dirs.filter fun d => cells.contains (c.1 + d.1, c.2 + d.2)).length).foldl (· + ·) 0 / 2

theorem nets_count : netCells.length = 11 := by decide +kernel
theorem nets_fold : netCells.all foldOK = true := by decide +kernel
theorem nets_tree_shaped : netCells.all (fun c => adjCount c == 5) = true := by decide +kernel

def d4 : List (Int × Int × Int × Int) := [(1,0,0,1),(0,-1,1,0),(-1,0,0,-1),(0,1,-1,0),(-1,0,0,1),(1,0,0,-1),(0,1,1,0),(0,-1,-1,0)]

def ins (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def isort (l : List Int) : List Int := l.foldl (fun acc x => ins x acc) []

/-- 변환 후 평행이동해 모서리를 0 으로 맞추고 코드 x*16+y 로 정렬 -/
def normCode (g : Int × Int × Int × Int) (cells : List Cell) : List Int :=
  let pts := cells.map fun c => (g.1 * c.1 + g.2.1 * c.2, g.2.2.1 * c.1 + g.2.2.2 * c.2)
  let mx := (pts.map (·.1)).foldl min 1000
  let my := (pts.map (·.2)).foldl min 1000
  isort (pts.map fun p => (p.1 - mx) * 16 + (p.2 - my))

def images (cells : List Cell) : List (List Int) := d4.map fun g => normCode g cells

def equiv (a b : List Cell) : Bool := (images a).any fun x => x == normCode (1,0,0,1) b

def planarStab (a : List Cell) : Nat := (images a).filter (· == normCode (1,0,0,1) a) |>.length

def distinctImages (a : List Cell) : Nat := (images a).eraseDups.length

theorem nets_pairwise_inequivalent :
    ((List.range 11).all fun i => (List.range 11).all fun j =>
      i == j || !(equiv (netCells.getD i []) (netCells.getD j []))) = true := by decide +kernel

theorem fixed_nets_64 : (netCells.map distinctImages).foldl (· + ·) 0 = 64 := by decide +kernel

theorem planar_stab_counts :
    ((netCells.map planarStab).filter (· == 1)).length = 5 ∧
    ((netCells.map planarStab).filter (· == 2)).length = 6 := by decide +kernel

/-! ## 3. 호지 미덮 궤도 11개 (m, 대표, 궤도 크기) -/
def hodgeOrbits : List (Nat × List Nat × Nat) := [
  (70, [1, 20, 24, 42, 61, 62], 24),
  (110, [1, 24, 62, 71, 81, 91], 40),
  (110, [1, 31, 55, 71, 81, 91], 8),
  (114, [1, 7, 78, 79, 86, 91], 36),
  (114, [1, 13, 43, 72, 103, 110], 36),
  (114, [1, 13, 43, 80, 102, 103], 36),
  (210, [2, 9, 129, 142, 168, 180], 24),
  (210, [3, 60, 72, 126, 183, 186], 24),
  (220, [1, 62, 111, 142, 162, 182], 40),
  (220, [2, 48, 124, 142, 162, 182], 40),
  (220, [2, 62, 110, 142, 162, 182], 8)]

def units (m : Nat) : List Nat := (List.range m).filter fun t => 0 < t && Nat.gcd t m == 1

def isort' (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: isort' x ys

def sortN (l : List Nat) : List Nat := l.foldl (fun acc x => isort' x acc) []

def orbitSize (m : Nat) (a : List Nat) : Nat :=
  ((units m).map fun t => sortN (a.map fun x => t * x % m)).eraseDups.length

def hodge22 (m : Nat) (a : List Nat) : Bool :=
  a.length == 6 && (a.all fun x => x % m != 0) && (a.foldl (· + ·) 0) % m == 0 &&
  (units m).all fun t => (a.map fun x => t * x % m).foldl (· + ·) 0 == 3 * m

def noZeroPair (m : Nat) (a : List Nat) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun j =>
    i ≥ j || (a.getD i 0 + a.getD j 0) % m != 0

theorem hodge_all_22 : hodgeOrbits.all (fun o => hodge22 o.1 o.2.1 && noZeroPair o.1 o.2.1) = true := by
  decide +kernel

theorem hodge_orbit_sizes : hodgeOrbits.all (fun o => orbitSize o.1 o.2.1 == o.2.2) = true := by
  decide +kernel

def hodgeSizes : List Nat := sortN (hodgeOrbits.map fun o => o.2.2)
def netSizes : List Nat := sortN orbitSizes

theorem sizes_differ : hodgeSizes ≠ netSizes := by decide +kernel

theorem some_hodge_size_not_divisor_of_48 : hodgeSizes.any (fun s => 48 % s != 0) = true := by
  decide +kernel

theorem sum_sizes : hodgeSizes.foldl (· + ·) 0 = 316 ∧ netSizes.foldl (· + ·) 0 = 384 := by
  decide +kernel

end CubeNets

#print axioms CubeNets.trees_384
#print axioms CubeNets.orbits_11
#print axioms CubeNets.orbit_sizes_count
#print axioms CubeNets.nets_fold
#print axioms CubeNets.nets_pairwise_inequivalent
#print axioms CubeNets.fixed_nets_64
#print axioms CubeNets.hodge_all_22
#print axioms CubeNets.hodge_orbit_sizes
#print axioms CubeNets.sizes_differ

import Mathlib

/-!
# 상수 큐브 배치의 계수 산술 (2026-11-04)
순수 조합 산술이다. 상수 6개를 면 6개에 놓는 방법의 수와, 마주 보는 쌍 3개를 정했을 때의
모서리 12개, 꼭짓점 8개를 센다. 어떤 식이 참인지, 어떤 배치가 좋은지는 다루지 않는다.
-/

namespace KimbanjiCubeLayout

/-- 상수 6개의 번호. 육각형 mod-6 순서: π=0, e=1, i=2, γ=3, φ=4, 1=5. -/
abbrev K := Fin 6

/-- 새 배치 π–1 | e–i | γ–φ 에서 마주 보는 상수 = 번호 (0,5), (1,2), (3,4). -/
def opp : K → K := ![5, 2, 1, 4, 3, 0]

theorem opp_opp : ∀ a : K, opp (opp a) = a := by decide
theorem opp_ne : ∀ a : K, opp a ≠ a := by decide

/-- 상수 6개. -/
theorem card_K : Fintype.card K = 6 := by decide

/-- 상수 쌍은 15개. -/
theorem pairs_15 : Nat.choose 6 2 = 15 := by decide

/-- 서로 다른 두 상수의 쌍(작은 번호 먼저) 전체. -/
def pairs : Finset (K × K) := (Finset.univ : Finset (K × K)).filter (fun p => p.1 < p.2)

theorem card_pairs : pairs.card = 15 := by decide +kernel

/-- 마주 보는 쌍. -/
def oppPairs : Finset (K × K) := pairs.filter (fun p => p.2 = opp p.1)

theorem card_oppPairs : oppPairs.card = 3 := by decide +kernel

/-- 모서리 = 마주 보지 않는 쌍: 15 - 3 = 12. -/
def edges : Finset (K × K) := pairs.filter (fun p => p.2 ≠ opp p.1)

theorem card_edges : edges.card = 12 := by decide +kernel
theorem edges_add_opp : edges.card + oppPairs.card = pairs.card := by decide +kernel
theorem edges_arith : 15 - 3 = 12 := by norm_num

/-- 면 하나에 이웃한 면은 4개(자기 자신과 마주 보는 면을 뺀 나머지). -/
theorem neighbors_four : ∀ a : K,
    ((Finset.univ : Finset K).filter (fun b => b ≠ a ∧ b ≠ opp a)).card = 4 := by decide

/-- 면 6개 x 이웃 4개 = 모서리 12개 x 2. -/
theorem handshake : 6 * 4 = 12 * 2 := by norm_num

/-- 세 상수의 부분집합(번호 증가 순서의 삼중)은 20개. -/
def triples : Finset (K × K × K) :=
  (Finset.univ : Finset (K × K × K)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

theorem card_triples : triples.card = 20 := by decide +kernel
theorem triples_choose : Nat.choose 6 3 = 20 := by decide

/-- 꼭짓점 = 마주 보는 두 면을 함께 갖지 않는 삼중 (세 면이 한 점에서 만남). -/
def verts : Finset (K × K × K) :=
  triples.filter (fun t => t.2.1 ≠ opp t.1 ∧ t.2.2 ≠ opp t.1 ∧ t.2.2 ≠ opp t.2.1)

theorem card_verts : verts.card = 8 := by decide +kernel

/-- 꼭짓점이 아닌 삼중은 12개 (마주 보는 쌍 3개 x 나머지 면 4개 중 하나). -/
def nonverts : Finset (K × K × K) :=
  triples.filter (fun t => ¬ (t.2.1 ≠ opp t.1 ∧ t.2.2 ≠ opp t.1 ∧ t.2.2 ≠ opp t.2.1))

theorem card_nonverts : nonverts.card = 12 := by decide +kernel
theorem verts_arith : 20 - 8 = 3 * 4 := by norm_num
theorem verts_two_pow : 2 ^ 3 = 8 := by norm_num

/-- 꼭짓점마다 세 면이 쌍마다 이웃한다: 각 꼭짓점 삼중의 세 쌍은 모두 모서리. -/
theorem verts_pairs_are_edges : ∀ t ∈ verts,
    (t.1, t.2.1) ∈ edges ∧ (t.1, t.2.2) ∈ edges ∧ (t.2.1, t.2.2) ∈ edges := by decide +kernel

/-- 꼭짓점 한 개는 모서리 3개의 끝이다 (삼중 속 쌍 3개). -/
theorem vert_three_pairs : Nat.choose 3 2 = 3 := by decide

/-- 꼭짓점 8개 x 3 = 모서리 12개 x 2 (모서리 하나에 꼭짓점 두 개). -/
theorem vertex_edge_incidence : 8 * 3 = 12 * 2 := by norm_num

/-- 모서리마다 그 두 면을 함께 갖는 꼭짓점이 정확히 2개. -/
theorem edge_two_verts : ∀ p ∈ edges,
    (verts.filter (fun t => (t.1 = p.1 ∨ t.2.1 = p.1 ∨ t.2.2 = p.1) ∧
      (t.1 = p.2 ∨ t.2.1 = p.2 ∨ t.2.2 = p.2))).card = 2 := by decide +kernel

/-! ## 배치 수 15 -/

/-- 짝짓기 열거. -/
def matchings : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => [[]]
  | _+1, [] => [[]]
  | _+1, [_] => []
  | n+1, a :: rest =>
      (List.range rest.length).flatMap (fun k =>
        let b := rest.getD k 0
        let rest' := rest.eraseIdx k
        (matchings n rest').map (fun m => (a, b) :: m))

/-- 6개를 마주 보는 3쌍으로 나누는 방법은 15가지 (열거). -/
theorem matchings_15 : (matchings 3 [0, 1, 2, 3, 4, 5]).length = 15 := by decide

/-- 6!/(2^3 * 3!) = 15 -/
theorem layouts_formula : Nat.factorial 6 / (2 ^ 3 * Nat.factorial 3) = 15 := by decide
theorem layouts_exact : Nat.factorial 6 = 15 * (2 ^ 3 * Nat.factorial 3) := by decide

/-- 이중 계승 꼴 5 x 3 x 1 = 15. -/
theorem layouts_double_factorial : 5 * 3 * 1 = 15 := by norm_num

/-- 한 배치를 고정하는 면 이름 바꿈(상수 순서 바꿈)은 2^3 x 3! = 48. -/
theorem stabilizer_48 : 2 ^ 3 * Nat.factorial 3 = 48 := by decide

/-! ## 육각형 mod-6 번호로 본 두 배치 -/

/-- 앞 배치 π–γ | e–φ | i–1 = (0,3),(1,4),(2,5): 번호 차 3 (육각형의 맞은편). -/
theorem old_layout_opposite_hexagon : ∀ p ∈ [(0, 3), (1, 4), (2, 5)], (p.2 + 6 - p.1) % 6 = 3 := by decide

/-- 새 배치 π–1 | e–i | γ–φ = (5,0),(1,2),(3,4): 번호 차 1 (육각형의 이웃). -/
theorem new_layout_opposite_hexagon : ∀ p ∈ [(5, 0), (1, 2), (3, 4)], (p.2 + 6 - p.1) % 6 = 1 := by decide

/-- 새 배치의 세 쌍은 6개 번호를 빠짐없이 한 번씩 쓴다. -/
theorem new_layout_covers : ([5, 0, 1, 2, 3, 4] : List Nat).Perm [0, 1, 2, 3, 4, 5] := by decide

end KimbanjiCubeLayout

#print axioms KimbanjiCubeLayout.card_pairs
#print axioms KimbanjiCubeLayout.card_oppPairs
#print axioms KimbanjiCubeLayout.card_edges
#print axioms KimbanjiCubeLayout.neighbors_four
#print axioms KimbanjiCubeLayout.card_triples
#print axioms KimbanjiCubeLayout.card_verts
#print axioms KimbanjiCubeLayout.card_nonverts
#print axioms KimbanjiCubeLayout.verts_pairs_are_edges
#print axioms KimbanjiCubeLayout.edge_two_verts
#print axioms KimbanjiCubeLayout.matchings_15
#print axioms KimbanjiCubeLayout.layouts_formula
#print axioms KimbanjiCubeLayout.layouts_exact
#print axioms KimbanjiCubeLayout.old_layout_opposite_hexagon
#print axioms KimbanjiCubeLayout.new_layout_opposite_hexagon
#print axioms KimbanjiCubeLayout.new_layout_covers

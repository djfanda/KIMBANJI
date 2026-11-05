import Mathlib
/-!
# 상수 큐브 24 회전 — 다리(띠) · 전선 · 대칭의 유한 셈 (decide)
상수 번호: π=0, e=1, i=2, γ=3, φ=4, 1=5. 면 번호: x+=0, x−=1, y+=2, y−=3, z+=4, z−=5.
S2 = 엄격 S 쌍 10 개(11-04 판정 권고 적용 뒤).
-/
namespace CubeBridge

def rots : List (Fin 6 → Fin 6) := [![1, 0, 3, 2, 4, 5],
  ![1, 0, 5, 4, 3, 2],
  ![1, 0, 4, 5, 2, 3],
  ![1, 0, 2, 3, 5, 4],
  ![3, 2, 1, 0, 5, 4],
  ![4, 5, 1, 0, 3, 2],
  ![5, 4, 1, 0, 2, 3],
  ![2, 3, 1, 0, 4, 5],
  ![3, 2, 4, 5, 1, 0],
  ![5, 4, 3, 2, 1, 0],
  ![4, 5, 2, 3, 1, 0],
  ![2, 3, 5, 4, 1, 0],
  ![3, 2, 5, 4, 0, 1],
  ![4, 5, 3, 2, 0, 1],
  ![5, 4, 2, 3, 0, 1],
  ![2, 3, 4, 5, 0, 1],
  ![3, 2, 0, 1, 4, 5],
  ![5, 4, 0, 1, 3, 2],
  ![4, 5, 0, 1, 2, 3],
  ![2, 3, 0, 1, 5, 4],
  ![0, 1, 3, 2, 5, 4],
  ![0, 1, 4, 5, 3, 2],
  ![0, 1, 5, 4, 2, 3],
  ![0, 1, 2, 3, 4, 5]]
def S2 : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (2, 3), (3, 4), (3, 5)]
def isS2 (a b : Fin 6) : Bool := S2.any (fun q => (q.1 = a ∧ q.2 = b) || (q.1 = b ∧ q.2 = a))
def allPairs : List (Fin 6 × Fin 6) := (List.finRange 6).flatMap (fun a => (List.finRange 6).filterMap (fun b => if a < b then some (a, b) else none))
/-- 배치 L: 면 → 상수. 마주 보는 면: (0,1),(2,3),(4,5). -/
def opp (L : Fin 6 → Fin 6) (a b : Fin 6) : Bool :=
  (List.finRange 3).any (fun k => (L ⟨2*k.1, by omega⟩ = a ∧ L ⟨2*k.1+1, by omega⟩ = b) || (L ⟨2*k.1, by omega⟩ = b ∧ L ⟨2*k.1+1, by omega⟩ = a))
def inv (L : Fin 6 → Fin 6) (c : Fin 6) : Fin 6 := ((List.finRange 6).find? (fun f => L f = c)).getD 0
def induced (L : Fin 6 → Fin 6) (r : Fin 6 → Fin 6) (c : Fin 6) : Fin 6 := L (r (inv L c))
def preservesS2 (σ : Fin 6 → Fin 6) : Bool := S2.all (fun q => isS2 (σ q.1) (σ q.2))
def fixedCount (r : Fin 6 → Fin 6) : Nat := ((List.finRange 6).filter (fun f => r f = f)).length
def isId (r : Fin 6 → Fin 6) : Bool := (List.finRange 6).all (fun f => r f = f)
def inK (c : Fin 6) : Bool := c = 0 || c = 1 || c = 3      -- π e γ (밖, 초월)
def inW (c : Fin 6) : Bool := c = 2 || c = 4 || c = 5      -- i φ 1 (안, 단위)

def L0 : Fin 6 → Fin 6 := ![0, 5, 3, 4, 1, 2]   -- 권고 배치 π–1 | γ–φ | e–i
def Lsym : Fin 6 → Fin 6 := ![0, 3, 1, 4, 2, 5] -- 대칭 배치 π–γ | e–φ | i–1

def edges (L : Fin 6 → Fin 6) := allPairs.filter (fun q => !(opp L q.1 q.2))
def centre (L : Fin 6 → Fin 6) := allPairs.filter (fun q => opp L q.1 q.2)
def Ktri (L : Fin 6 → Fin 6) := (edges L).filter (fun q => inK q.1 && inK q.2)
def Wtri (L : Fin 6 → Fin 6) := (edges L).filter (fun q => inW q.1 && inW q.2)
def belt (L : Fin 6 → Fin 6) := (edges L).filter (fun q => (inK q.1 && inW q.2) || (inW q.1 && inK q.2))
def sCount (l : List (Fin 6 × Fin 6)) : Nat := (l.filter (fun q => isS2 q.1 q.2)).length

theorem rots_card : rots.length = 24 := by decide
theorem edges_card : (edges L0).length = 12 := by decide
/-- 밖 삼각형(π,e,γ)은 3/3 S, 안 삼각형(1,i,φ)은 0/3, 띠는 5/6, 중심 3 전선은 2/3. -/
theorem wires_K : sCount (Ktri L0) = 3 := by decide
theorem wires_W : sCount (Wtri L0) = 0 := by decide
theorem wires_belt : (belt L0).length = 6 ∧ sCount (belt L0) = 5 := by decide
theorem wires_centre : (centre L0).length = 3 ∧ sCount (centre L0) = 2 := by decide
/-- 권고 배치에서 S 쌍을 보존하는 회전은 항등뿐, 대칭 배치에서는 넷(클라인 4 군). -/
theorem sym_L0 : (rots.filter (fun r => preservesS2 (induced L0 r))).length = 1 := by decide
theorem sym_Lsym : (rots.filter (fun r => preservesS2 (induced Lsym r))).length = 4 := by decide
/-- 항등이 아닌 회전은 면을 많아야 둘 고정한다 — 세 면 이상을 고정하는 사상은 회전이 아니다. -/
theorem fix_le_two : rots.all (fun r => isId r || decide (fixedCount r ≤ 2)) = true := by decide
#print axioms wires_belt
#print axioms sym_L0
#print axioms sym_Lsym
#print axioms fix_le_two
end CubeBridge

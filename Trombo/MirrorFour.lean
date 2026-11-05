/-
거울 넷 — 제타 영점의 네 방향과 리만 가설의 꼴 (린 4 코어 · 정수만)

영점 후보 ρ = σ + it 를 두 배 좌표 (a, b) = (2σ, 2t) 의 정수 쌍으로 적는다.
· 켤레 (남북) : ρ ↦ ρ̄          — (a, b) ↦ (a, −b)
· 거울 (동서) : ρ ↦ 1 − ρ       — (a, b) ↦ (2 − a, −b)
· 둘 다       : ρ ↦ 1 − ρ̄       — (a, b) ↦ (2 − a, b)
제타의 영점은 켤레와 함수 방정식 ξ(s) = ξ(1 − s) 때문에 이 네 자리에 함께 놓인다(고전 사실 · 여기서는 가정으로 둔다).

이 파일이 커널로 확인하는 것 :
1. 실수가 아닌 ρ (b ≠ 0) 의 네 자리는 σ = 1/2 (a = 1) 이면 꼭 둘로 겹치고, 아니면 넷이 모두 다르다.
2. 그래서 «모든 영점의 네 자리가 둘로 겹침» 과 «모든 영점의 실수부가 1/2» 은 같은 말이다 (리만 가설의 다른 꼴).
3. 네 자리는 짝 넷(클라인 네 무리)으로 닫혀 있다 : 두 번 하면 제자리 · 켤레와 거울은 바꿔 해도 같다.

정직한 경계 : 이것은 리만 가설을 «다른 말로 옮긴 것» 이지 증명이 아니다. 영점이 실제로 어디 있는지는 이 파일이 말하지 않는다.
-/
namespace MirrorFour

/-- 두 배 좌표의 점 (2σ, 2t) -/
abbrev P := Int × Int

def conj (z : P) : P := (z.1, -z.2)
def mirror (z : P) : P := (2 - z.1, -z.2)
def both (z : P) : P := (2 - z.1, z.2)

/-- 네 자리 -/
def orbit (z : P) : List P := [z, conj z, mirror z, both z]

theorem conj_conj (z : P) : conj (conj z) = z := by
  simp [conj]
theorem mirror_mirror (z : P) : mirror (mirror z) = z := by
  obtain ⟨a, b⟩ := z; simp only [mirror, Prod.mk.injEq]; omega
theorem both_eq (z : P) : both z = mirror (conj z) := by
  simp [both, mirror, conj]
theorem conj_mirror_comm (z : P) : conj (mirror z) = mirror (conj z) := by
  simp [conj, mirror]
theorem both_both (z : P) : both (both z) = z := by
  obtain ⟨a, b⟩ := z; show (2 - (2 - a), b) = (a, b); congr 1; omega

/-- «둘 다» 가 제자리 ⇔ σ = 1/2 -/
theorem both_fixed_iff (z : P) : both z = z ↔ z.1 = 1 := by
  obtain ⟨a, b⟩ := z
  simp only [both, Prod.mk.injEq, and_true]
  constructor <;> intro h <;> omega

/-- 켤레가 제자리 ⇔ 실수 (t = 0) -/
theorem conj_fixed_iff (z : P) : conj z = z ↔ z.2 = 0 := by
  obtain ⟨a, b⟩ := z
  simp only [conj, Prod.mk.injEq, true_and]
  constructor <;> intro h <;> omega

/-- 실수가 아니고 σ ≠ 1/2 이면 네 자리가 모두 다름 -/
theorem four_distinct (a b : Int) (hb : b ≠ 0) (ha : a ≠ 1) : (orbit (a, b)).Nodup := by
  have h1 : a ≠ 2 - a := by omega
  have h2 : b ≠ -b := by omega
  simp [orbit, conj, mirror, both, h1, h2, Ne.symm h2]

/-- 실수가 아니고 σ = 1/2 이면 네 자리가 꼭 두 점 (ρ 와 ρ̄) 으로 겹침 -/
theorem two_points (a b : Int) (hb : b ≠ 0) (ha : a = 1) :
    (a, b) ≠ (a, -b) ∧ ∀ w ∈ orbit (a, b), w = (a, b) ∨ w = (a, -b) := by
  subst ha
  refine ⟨?_, ?_⟩
  · simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  · intro w hw
    simp only [orbit, conj, mirror, both, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h <;> subst h <;> simp

/-- σ = 1/2 이면 네 자리에 겹침이 있음 (Nodup 아님) -/
theorem not_distinct (a b : Int) (ha : a = 1) : ¬ (orbit (a, b)).Nodup := by
  subst ha
  simp [orbit, conj, mirror, both]

/-- 실수가 아닌 점 : 네 자리가 모두 다름 ⇔ σ ≠ 1/2 -/
theorem distinct_iff (a b : Int) (hb : b ≠ 0) : (orbit (a, b)).Nodup ↔ a ≠ 1 := by
  constructor
  · intro h ha; exact not_distinct a b ha h
  · exact four_distinct a b hb

/-- 리만 가설의 꼴 : 영점 모임 Z 의 실수 아닌 점마다 «네 자리가 겹침(둘)» ⇔ «실수부 1/2» -/
theorem rh_form (Z : P → Prop) (hZ : ∀ z, Z z → z.2 ≠ 0) :
    (∀ z, Z z → ¬ (orbit z).Nodup) ↔ (∀ z, Z z → z.1 = 1) := by
  constructor
  · intro h z hz
    obtain ⟨a, b⟩ := z
    have := h _ hz
    rw [distinct_iff a b (hZ _ hz)] at this
    simpa using this
  · intro h z hz
    obtain ⟨a, b⟩ := z
    exact not_distinct a b (h _ hz)

/-- 시범 : 첫 영점의 꼴 (σ = 1/2 · 두 배 좌표 (1, 28)) 은 겹치고, 줄 밖의 가상 점 (σ = 3/2 · (3, 28)) 은 넷이 모두 다름 -/
theorem demo_on_line : ¬ (orbit (1, 28)).Nodup := by decide
theorem demo_off_line : (orbit (3, 28)).Nodup := by decide

end MirrorFour

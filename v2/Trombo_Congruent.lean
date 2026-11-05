import Mathlib.Data.Set.Card
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Trombo hypothesis ladder: congruent-number anchors (Tunnell 1983)

* `IsCongruent n` : `n` is the area of a right triangle with rational sides.
* Unconditional: `5`, `6`, `7` are congruent (explicit rational triangles).
* Unconditional: Tunnell's representation counts for `n = 1, 2, 3, 5, 6, 7`, computed from the
  exact definitions (counts of all integer triples, not of a truncated box; the box reduction is
  proved).
* `TunnellForward` (a theorem of Tunnell 1983, not formalized here) and `TunnellConverse`
  (the direction that depends on the Birch–Swinnerton-Dyer conjecture) are `def … : Prop`.
  Nothing is assumed as an axiom.

Reference: J. B. Tunnell, *A classical Diophantine problem and modular forms of weight 3/2*,
Invent. Math. 72 (1983), 323–334.
-/

namespace TromboCongruent

/-- `n` is a congruent number: there is a right triangle with positive rational legs `a, b`,
hypotenuse `c`, and area `n`. -/
def IsCongruent (n : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- `6` is congruent: the triangle `(3, 4, 5)`. -/
theorem congruent_six : IsCongruent 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `5` is congruent: the triangle `(3/2, 20/3, 41/6)`. -/
theorem congruent_five : IsCongruent 5 :=
  ⟨3 / 2, 20 / 3, 41 / 6, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `7` is congruent: the triangle `(24/5, 35/12, 337/60)`. -/
theorem congruent_seven : IsCongruent 7 :=
  ⟨24 / 5, 35 / 12, 337 / 60, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Number of integer triples `(x, y, z) ∈ ℤ³` with `a x² + b y² + c z² = m`
(`Set.ncard`; it is `0` if the set were infinite, which `card_eq_box` rules out for `a,b,c ≥ 1`). -/
noncomputable def repCount (a b c m : ℤ) : ℕ :=
  Set.ncard {p : ℤ × ℤ × ℤ | a * p.1 ^ 2 + b * p.2.1 ^ 2 + c * p.2.2 ^ 2 = m}

/-- The same count restricted to the box `[-m, m]³` (computable). -/
def boxCount (a b c m : ℤ) : ℕ :=
  ((Finset.Icc (-m) m ×ˢ (Finset.Icc (-m) m ×ˢ Finset.Icc (-m) m)).filter
    (fun p : ℤ × ℤ × ℤ => a * p.1 ^ 2 + b * p.2.1 ^ 2 + c * p.2.2 ^ 2 = m)).card

private lemma bound_of_sq_le {x m : ℤ} (h : x ^ 2 ≤ m) : -m ≤ x ∧ x ≤ m := by
  constructor <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

/-- Unconditional: for `a, b, c ≥ 1` every solution lies in the box `[-m, m]³`,
so `repCount = boxCount`. -/
theorem card_eq_box {a b c : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (m : ℤ) :
    repCount a b c m = boxCount a b c m := by
  unfold repCount boxCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext ⟨x, y, z⟩
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h
    have hx : x ^ 2 ≤ m := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y ^ 2 ≤ m := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z ^ 2 ≤ m := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    exact ⟨⟨bound_of_sq_le hx, bound_of_sq_le hy, bound_of_sq_le hz⟩, h⟩
  · exact fun h => h.2

/-- Tunnell's `A_n = #{(x,y,z) ∈ ℤ³ : x² + 2y² + 8z² = n}` (used for odd `n`; letters follow Koblitz, GTM 97 — Wikipedia labels them differently). -/
noncomputable def tA (n : ℕ) : ℕ := repCount 1 2 8 n
/-- Tunnell's `B_n = #{(x,y,z) ∈ ℤ³ : x² + 2y² + 32z² = n}` (used for odd `n`). -/
noncomputable def tB (n : ℕ) : ℕ := repCount 1 2 32 n
/-- Tunnell's `C_n = #{(x,y,z) ∈ ℤ³ : x² + 4y² + 8z² = n/2}` (used for even `n`). -/
noncomputable def tC (n : ℕ) : ℕ := repCount 1 4 8 ((n / 2 : ℕ) : ℤ)
/-- Tunnell's `D_n = #{(x,y,z) ∈ ℤ³ : x² + 4y² + 32z² = n/2}` (used for even `n`). -/
noncomputable def tD (n : ℕ) : ℕ := repCount 1 4 32 ((n / 2 : ℕ) : ℤ)

/-- Unconditional counts for odd `n ∈ {1, 3, 5, 7}`:
`(A,B) = (2,2), (4,4), (0,0), (0,0)`. (Box sums checked by kernel reduction, `decide +kernel`.) -/
theorem tunnell_odd_counts :
    tA 1 = 2 ∧ tB 1 = 2 ∧ tA 3 = 4 ∧ tB 3 = 4 ∧
    tA 5 = 0 ∧ tB 5 = 0 ∧ tA 7 = 0 ∧ tB 7 = 0 := by
  simp only [tA, tB, card_eq_box (le_refl 1) (by norm_num : (1 : ℤ) ≤ 2) (by norm_num : (1 : ℤ) ≤ 8),
    card_eq_box (le_refl 1) (by norm_num : (1 : ℤ) ≤ 2) (by norm_num : (1 : ℤ) ≤ 32)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Unconditional counts for even `n ∈ {2, 6}` (so `n/2 ∈ {1, 3}`):
`(C,D) = (2,2), (0,0)`. -/
theorem tunnell_even_counts :
    tC 2 = 2 ∧ tD 2 = 2 ∧ tC 6 = 0 ∧ tD 6 = 0 := by
  simp only [tC, tD, card_eq_box (le_refl 1) (by norm_num : (1 : ℤ) ≤ 4) (by norm_num : (1 : ℤ) ≤ 8),
    card_eq_box (le_refl 1) (by norm_num : (1 : ℤ) ≤ 4) (by norm_num : (1 : ℤ) ≤ 32)]
  decide

/-- Tunnell's criterion holds (`A = 2B`, resp. `C = 2D`) at `n = 5, 6, 7` and fails at
`n = 1, 2, 3`. Unconditional arithmetic. -/
theorem tunnell_criterion_values :
    tA 5 = 2 * tB 5 ∧ tA 7 = 2 * tB 7 ∧ tC 6 = 2 * tD 6 ∧
    tA 1 ≠ 2 * tB 1 ∧ tA 3 ≠ 2 * tB 3 ∧ tC 2 ≠ 2 * tD 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := tunnell_odd_counts
  obtain ⟨e1, e2, e3, e4⟩ := tunnell_even_counts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [*]

/-- Tunnell's theorem, proven direction (Tunnell 1983, via Coates–Wiles). It is a theorem in the
literature but NOT formalized here, so it is stated as a hypothesis `Prop`: if a squarefree `n` is congruent then `A_n = 2B_n` for odd `n`
and `C_n = 2D_n` for even `n`. -/
def TunnellForward : Prop :=
  ∀ n : ℕ, Squarefree n → IsCongruent n →
    (Odd n → tA n = 2 * tB n) ∧ (Even n → tC n = 2 * tD n)

/-- Tunnell's converse (open; follows from the Birch–Swinnerton-Dyer conjecture for the curves
`y² = x³ − n²x`): a squarefree `n` with `A_n = 2B_n` (odd `n`) or `C_n = 2D_n` (even `n`)
is congruent. -/
def TunnellConverse : Prop :=
  ∀ n : ℕ, Squarefree n →
    ((Odd n ∧ tA n = 2 * tB n) ∨ (Even n ∧ tC n = 2 * tD n)) → IsCongruent n

/-- `TunnellForward → 1, 2, 3 are not congruent` (using the unconditional counts above). -/
theorem tunnellForward_imp_not_congruent_123 :
    TunnellForward → ¬ IsCongruent 1 ∧ ¬ IsCongruent 2 ∧ ¬ IsCongruent 3 := by
  intro hT
  obtain ⟨-, -, -, h1, h3, h2⟩ := tunnell_criterion_values
  refine ⟨fun hc => h1 ((hT 1 squarefree_one hc).1 (by decide)),
    fun hc => h2 ((hT 2 Nat.prime_two.prime.squarefree hc).2 (by decide)),
    fun hc => h3 ((hT 3 Nat.prime_three.prime.squarefree hc).1 (by decide))⟩

end TromboCongruent

#print axioms TromboCongruent.congruent_five
#print axioms TromboCongruent.congruent_six
#print axioms TromboCongruent.congruent_seven
#print axioms TromboCongruent.card_eq_box
#print axioms TromboCongruent.tunnell_odd_counts
#print axioms TromboCongruent.tunnell_even_counts
#print axioms TromboCongruent.tunnell_criterion_values
#print axioms TromboCongruent.tunnellForward_imp_not_congruent_123
#print axioms TromboCongruent.bound_of_sq_le

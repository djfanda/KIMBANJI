import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Trombo: the zero quartet of the Riemann zeta function

Elementary, folklore facts about the symmetry of the zeros of `ζ`, proved against Mathlib's
`riemannZeta` and Mathlib's own `RiemannHypothesis`. Nothing here is new mathematics and nothing
here proves RH; the file only restates RH as a symmetry statement.

Contents.
* `zeta_conj` : `ζ (conj s) = conj (ζ s)` for all `s` (this is Mathlib's `riemannZeta_conj`).
* `zeta_eq_zero_iff_conj` : `ζ s = 0 ↔ ζ (conj s) = 0`.
* `zeta_zero_in_strip` : a zero that is not trivial lies in `0 < re s < 1` (copied from
  `Trombo_RHEquiv.lean`, mlib4).
* `zeta_eq_zero_iff_one_sub` : on the open strip `0 < re s < 1`, `ζ s = 0 ↔ ζ (1 - s) = 0`.
* `zeta_one_sub_trivial_ne_zero`, `zeta_zero_ne_zero'` : the reflection does NOT pair trivial
  zeros with zeros, and the points `0`, `1` are not zeros.
* `quartet`, `quartet_nontrivial` : all four points of the quartet of a nontrivial zero are
  nontrivial zeros.
* `one_sub_conj_eq_self_iff`, `quartet_eq_pair_iff` : the quartet collapses to `{ρ, conj ρ}`
  iff `re ρ = 1/2` (pure complex arithmetic).
* `RH_iff_quartets_collapse` : `RiemannHypothesis ↔ ∀ ρ nontrivial zero, 1 - conj ρ = ρ`.
* Orientation: `det_conj = -1`, `det_neg = 1`, `det_negConj = -1` for the ℝ-linear parts of
  `s ↦ conj s`, `s ↦ 1 - s`, `s ↦ 1 - conj s`, plus the explicit 2×2 matrices.
-/

open Complex ComplexConjugate

namespace TromboZeroQuartet

/-! ## 1. Conjugation (reflection across the real axis) -/

/-- `ζ (conj s) = conj (ζ s)` for every `s : ℂ` (including Mathlib's junk value at `s = 1`).
This is exactly Mathlib's `riemannZeta_conj`. -/
theorem zeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) :=
  riemannZeta_conj s

/-- `ζ s = 0 ↔ ζ (conj s) = 0` for every `s : ℂ`. -/
theorem zeta_eq_zero_iff_conj (s : ℂ) : riemannZeta s = 0 ↔ riemannZeta (conj s) = 0 := by
  rw [zeta_conj, map_eq_zero]

/-! ## 2. Functional-equation reflection `s ↦ 1 - s` -/

/-- A point with positive real part is not a trivial zero `-2(n+1)`. -/
lemma not_trivial_of_re_pos {s : ℂ} (hs : 0 < s.re) : ¬∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at hs
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Unconditional: a zero of `ζ` that is not of the form `-2(n+1)` lies in the open critical
strip `0 < re s < 1`. (Copied from `Trombo_RHEquiv.lean`.) -/
lemma zeta_zero_in_strip {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    push Not at hle
    have hs0 : s ≠ 0 := by
      rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
    set w : ℂ := 1 - s with hw
    have hwre : 1 ≤ w.re := by simp [hw]; linarith
    have hwn : ∀ n : ℕ, w ≠ -n := by
      intro n h
      have : w.re = -(n : ℝ) := by rw [h]; simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hw1 : w ≠ 1 := by
      intro h; apply hs0; rw [hw] at h; linear_combination -h
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : 1 - w = s := by rw [hw]; ring
    rw [h1w, hz] at hfe
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hA : (2 : ℂ) * (2 * Real.pi) ^ (-w) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      rw [cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hpi)]
      exact exp_ne_zero _
    have hG : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hZ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : cos (Real.pi * w / 2) = 0 := by
      by_contra hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hG) hc) hZ) hfe.symm
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
    have hwk : w = 2 * k + 1 := by
      have : Real.pi * w = Real.pi * (2 * k + 1) := by linear_combination 2 * hk
      exact mul_left_cancel₀ hpi this
    have hsk : s = -2 * (k : ℂ) := by linear_combination -hwk - hw
    have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
    have hk0 : 0 ≤ k := by
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rcases Nat.eq_zero_or_pos m with hm | hm
    · apply hs0; rw [hsk, hm]; simp
    · apply htriv
      refine ⟨m - 1, ?_⟩
      rw [hsk]
      have : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
        rw [Nat.cast_sub hm]; push_cast; ring
      rw [this]; push_cast; ring
  · by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- If `ζ s = 0`, `0 < re s` and `s ≠ 1`, then `ζ (1 - s) = 0` (functional equation). -/
lemma zeta_one_sub_eq_zero {s : ℂ} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have : s.re = -(n : ℝ) := by rw [h]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hn hs1
  rw [hz, mul_zero] at hfe
  exact hfe

/-- On the open critical strip `0 < re s < 1`: `ζ s = 0 ↔ ζ (1 - s) = 0`. -/
theorem zeta_eq_zero_iff_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = 0 ↔ riemannZeta (1 - s) = 0 := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  constructor
  · intro hz; exact zeta_one_sub_eq_zero hz h0 hs1
  · intro hz
    have h0' : 0 < (1 - s).re := by simp; linarith
    have h1' : 1 - s ≠ 1 := by
      intro h; have : (1 - s).re = (1 : ℂ).re := by rw [h]
      simp at this; linarith
    have := zeta_one_sub_eq_zero hz h0' h1'
    simpa using this

/-- The reflection fails at the trivial zeros: `ζ (-2(n+1)) = 0` but
`ζ (1 - (-2(n+1))) = ζ (2n+3) ≠ 0`. -/
theorem zeta_one_sub_trivial_ne_zero (n : ℕ) :
    riemannZeta (-2 * (n + 1)) = 0 ∧ riemannZeta (1 - (-2 * ((n : ℂ) + 1))) ≠ 0 := by
  refine ⟨riemannZeta_neg_two_mul_nat_add_one n, ?_⟩
  apply riemannZeta_ne_zero_of_one_le_re
  have : (1 - (-2 * ((n : ℂ) + 1))).re = 1 + 2 * ((n : ℝ) + 1) := by simp
  rw [this]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The pair `{0, 1}` exchanged by `s ↦ 1 - s` contains no zero: `ζ 0 = -1/2 ≠ 0`, and Mathlib's
junk value `ζ 1` is nonzero. -/
theorem zeta_zero_ne_zero' : riemannZeta 0 ≠ 0 ∧ riemannZeta 1 ≠ 0 := by
  refine ⟨?_, riemannZeta_one_ne_zero⟩
  rw [riemannZeta_zero]; norm_num

/-! ## 3. Nontrivial zeros and the quartet -/

/-- `s` is a nontrivial zero in Mathlib's sense: `ζ s = 0`, `s` is not `-2(n+1)`, `s ≠ 1`
(the same hypotheses as in Mathlib's `RiemannHypothesis`). -/
def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- A nontrivial zero lies in the open strip `0 < re s < 1`. -/
lemma NontrivialZero.strip {s : ℂ} (h : NontrivialZero s) : 0 < s.re ∧ s.re < 1 :=
  zeta_zero_in_strip h.1 h.2.1

/-- A point of the open strip with `ζ s = 0` is a nontrivial zero. -/
lemma nontrivialZero_of_strip {s : ℂ} (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    NontrivialZero s := by
  refine ⟨hz, not_trivial_of_re_pos h0, ?_⟩
  rintro rfl; simp at h1

/-- `NontrivialZero s ↔ NontrivialZero (conj s)`. -/
theorem nontrivialZero_conj_iff (s : ℂ) : NontrivialZero s ↔ NontrivialZero (conj s) := by
  have key : ∀ z : ℂ, NontrivialZero z → NontrivialZero (conj z) := by
    intro z hz
    obtain ⟨h0, h1⟩ := hz.strip
    exact nontrivialZero_of_strip ((zeta_eq_zero_iff_conj z).1 hz.1) (by simpa using h0)
      (by simpa using h1)
  exact ⟨key s, fun h => by simpa using key _ h⟩

/-- `NontrivialZero s ↔ NontrivialZero (1 - s)`. -/
theorem nontrivialZero_one_sub_iff (s : ℂ) : NontrivialZero s ↔ NontrivialZero (1 - s) := by
  have key : ∀ z : ℂ, NontrivialZero z → NontrivialZero (1 - z) := by
    intro z hz
    obtain ⟨h0, h1⟩ := hz.strip
    exact nontrivialZero_of_strip ((zeta_eq_zero_iff_one_sub h0 h1).1 hz.1)
      (by simp; linarith) (by simp; linarith)
  exact ⟨key s, fun h => by simpa using key _ h⟩

/-- The quartet of `ρ`: `{ρ, conj ρ, 1 - ρ, 1 - conj ρ}`. -/
def quartet (ρ : ℂ) : Set ℂ := {ρ, conj ρ, 1 - ρ, 1 - conj ρ}

/-- If `ρ` is a nontrivial zero, every member of its quartet is a nontrivial zero. -/
theorem quartet_nontrivial {ρ : ℂ} (h : NontrivialZero ρ) :
    ∀ z ∈ quartet ρ, NontrivialZero z := by
  have hc := (nontrivialZero_conj_iff ρ).1 h
  intro z hz
  simp only [quartet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact h
  · exact hc
  · exact (nontrivialZero_one_sub_iff _).1 h
  · exact (nontrivialZero_one_sub_iff _).1 hc

/-! ## 4. Collapse of the quartet (pure complex arithmetic) -/

/-- `1 - conj ρ = ρ ↔ re ρ = 1/2`, for every `ρ : ℂ`. -/
theorem one_sub_conj_eq_self_iff (ρ : ℂ) : 1 - conj ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith
  · intro h
    apply Complex.ext
    · simp [h]; norm_num
    · simp

/-- `1 - ρ = conj ρ ↔ re ρ = 1/2`, for every `ρ : ℂ`. -/
theorem one_sub_eq_conj_iff (ρ : ℂ) : 1 - ρ = conj ρ ↔ ρ.re = 1 / 2 := by
  rw [← one_sub_conj_eq_self_iff]
  constructor <;> intro h <;> linear_combination h

/-- The quartet collapses to the pair `{ρ, conj ρ}` iff `re ρ = 1/2`, for every `ρ : ℂ`. -/
theorem quartet_eq_pair_iff (ρ : ℂ) : quartet ρ = {ρ, conj ρ} ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have hm : (1 - conj ρ) ∈ ({ρ, conj ρ} : Set ℂ) := by
      rw [← h]; simp [quartet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h1 | h1
    · exact (one_sub_conj_eq_self_iff ρ).1 h1
    · have := congrArg Complex.re h1
      simp at this; linarith
  · intro h
    have e1 := (one_sub_eq_conj_iff ρ).2 h
    have e2 := (one_sub_conj_eq_self_iff ρ).2 h
    simp only [quartet, e1, e2]
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ## 5. Main theorem -/

/-- **RH as quartet collapse.** Mathlib's `RiemannHypothesis` holds iff every nontrivial zero `ρ`
is fixed by the mirror `s ↦ 1 - conj s`. This is an elementary reformulation, not a proof of RH. -/
theorem RH_iff_quartets_collapse :
    RiemannHypothesis ↔ ∀ ρ : ℂ, NontrivialZero ρ → 1 - conj ρ = ρ := by
  constructor
  · intro hRH ρ h
    exact (one_sub_conj_eq_self_iff ρ).2 (hRH ρ h.1 h.2.1 h.2.2)
  · intro h s hz htriv hs1
    exact (one_sub_conj_eq_self_iff s).1 (h s ⟨hz, htriv, hs1⟩)

/-- Same statement with the set form: RH iff every nontrivial zero's quartet is `{ρ, conj ρ}`. -/
theorem RH_iff_quartets_eq_pair :
    RiemannHypothesis ↔ ∀ ρ : ℂ, NontrivialZero ρ → quartet ρ = {ρ, conj ρ} := by
  rw [RH_iff_quartets_collapse]
  refine forall_congr' fun ρ => imp_congr_right fun _ => ?_
  rw [one_sub_conj_eq_self_iff, quartet_eq_pair_iff]

/-! ## 6. Orientation (determinants of the ℝ-linear parts) -/

/-- The ℝ-linear map `s ↦ conj s`. -/
noncomputable def conjLin : ℂ →ₗ[ℝ] ℂ := conjAe.toLinearEquiv.toLinearMap

/-- The ℝ-linear map `s ↦ -s`, the linear part of `s ↦ 1 - s`. -/
noncomputable def negLin : ℂ →ₗ[ℝ] ℂ := -LinearMap.id

/-- The ℝ-linear map `s ↦ -conj s`, the linear part of `s ↦ 1 - conj s`. -/
noncomputable def negConjLin : ℂ →ₗ[ℝ] ℂ := negLin ∘ₗ conjLin

/-- `s ↦ 1 - s` is `1 + negLin s`, and `s ↦ 1 - conj s` is `1 + negConjLin s`. -/
theorem affine_parts (s : ℂ) : 1 - s = 1 + negLin s ∧ 1 - conj s = 1 + negConjLin s := by
  simp [negLin, negConjLin, conjLin, sub_eq_add_neg]

/-- `s ↦ conj s` reverses orientation: its real determinant is `-1`. -/
theorem det_conj : LinearMap.det conjLin = -1 := det_conjAe

/-- `s ↦ -s` (rotation by `π`) preserves orientation: its real determinant is `+1`. -/
theorem det_neg : LinearMap.det negLin = 1 := by
  have : negLin = (-1 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
    ext z; simp [negLin]
  rw [this, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex]
  norm_num

/-- `s ↦ -conj s` (linear part of the mirror across `re s = 1/2`) reverses orientation:
its real determinant is `-1`. -/
theorem det_negConj : LinearMap.det negConjLin = -1 := by
  rw [negConjLin, LinearMap.det_comp, det_neg, det_conj]; norm_num

/-- Determinants of three explicit real 2×2 matrices: `det diag(1,-1) = -1`,
`det diag(-1,-1) = 1`, `det diag(-1,1) = -1`, and `diag(-1,-1) * diag(1,-1) = diag(-1,1)`.
(These are the matrices of `conj`, `s ↦ -s`, `s ↦ -conj s` in the basis `(1, i)`; that
identification is stated here for exposition and is not itself proved in this lemma.) -/
theorem explicit_matrices :
    Matrix.det !![(1 : ℝ), 0; 0, -1] = -1 ∧ Matrix.det !![(-1 : ℝ), 0; 0, -1] = 1 ∧
    Matrix.det !![(-1 : ℝ), 0; 0, 1] = -1 ∧
    !![(-1 : ℝ), 0; 0, -1] * !![(1 : ℝ), 0; 0, -1] = !![(-1 : ℝ), 0; 0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The point reflection `s ↦ 1 - s` has exactly one fixed point, `1/2`. -/
theorem one_sub_fixed_iff (s : ℂ) : 1 - s = s ↔ s = 1 / 2 := by
  constructor
  · intro h; linear_combination -h / 2
  · intro h; rw [h]; norm_num

end TromboZeroQuartet

#print axioms TromboZeroQuartet.zeta_conj
#print axioms TromboZeroQuartet.zeta_eq_zero_iff_conj
#print axioms TromboZeroQuartet.not_trivial_of_re_pos
#print axioms TromboZeroQuartet.zeta_zero_in_strip
#print axioms TromboZeroQuartet.zeta_one_sub_eq_zero
#print axioms TromboZeroQuartet.zeta_eq_zero_iff_one_sub
#print axioms TromboZeroQuartet.zeta_one_sub_trivial_ne_zero
#print axioms TromboZeroQuartet.zeta_zero_ne_zero'
#print axioms TromboZeroQuartet.NontrivialZero.strip
#print axioms TromboZeroQuartet.nontrivialZero_of_strip
#print axioms TromboZeroQuartet.nontrivialZero_conj_iff
#print axioms TromboZeroQuartet.nontrivialZero_one_sub_iff
#print axioms TromboZeroQuartet.quartet_nontrivial
#print axioms TromboZeroQuartet.one_sub_conj_eq_self_iff
#print axioms TromboZeroQuartet.one_sub_eq_conj_iff
#print axioms TromboZeroQuartet.quartet_eq_pair_iff
#print axioms TromboZeroQuartet.RH_iff_quartets_collapse
#print axioms TromboZeroQuartet.RH_iff_quartets_eq_pair
#print axioms TromboZeroQuartet.affine_parts
#print axioms TromboZeroQuartet.det_conj
#print axioms TromboZeroQuartet.det_neg
#print axioms TromboZeroQuartet.det_negConj
#print axioms TromboZeroQuartet.explicit_matrices
#print axioms TromboZeroQuartet.one_sub_fixed_iff

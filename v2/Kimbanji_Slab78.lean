/-
  Kimbanji_Slab78.lean  (Trombo project, author DJ FANDA, 2026-11-04)

  What this file contains (all proved here, Mathlib only, no extra hypotheses):
  (1) A logic fact from the functional equation of Mathlib's `riemannZeta`:
      if `ζ(s) ≠ 0` for every `Re s > θ` (0 ≤ θ), then `ζ(w) ≠ 0` for every `w` with
      `Re w < 1 - θ` except `w = -2(n+1)` (the trivial zeros, which really are zeros).
      Hence, under `ZeroFreeRight 7/8`, every zero with `0 < Re w < 1` has `1/8 ≤ Re w ≤ 7/8`.
  (2) Arithmetic of the eight strips of width 1/8 in the critical strip (0,1):
      widths, count of the remaining six strips, the central line 4/8 = 1/2,
      and the reflection `s ↦ 1 - s` sending strip k to strip 7 - k.
  (3) `RiemannHypothesis → ZeroFreeRight (1/2)` and `→ ZeroFreeRight (7/8)`.

  NOT proved here, and not assumed: `ZeroFreeRight (7/8)` itself.  It is the statement of a claim
  (OpenAI, preprint of 2026-09-30, unrefereed).  Every result below is an implication or an arithmetic
  fact; nothing here says the claim or RH is true.
-/
import Mathlib

open Complex

namespace Slab78

/-- `ζ` has no zero in the open half-plane `Re s > θ`. -/
def ZeroFreeRight (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- The statement `ZeroFreeRight (7/8)` (a claim; not proved here). -/
def ZeroFreeRight78 : Prop := ZeroFreeRight (7 / 8)

theorem zeroFreeRight78_iff :
    ZeroFreeRight78 ↔ ∀ {s : ℂ}, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0 :=
  ⟨fun h _ hs => h _ hs, fun h _ hs => h hs⟩

/-! ## (1) Reflection of the zero-free region -/

/-- Reflection through the functional equation. -/
theorem reflect_nonzero {θ : ℝ} (hθ : 0 ≤ θ) (h : ZeroFreeRight θ) {w : ℂ}
    (hw : w.re < 1 - θ) (hexc : ∀ n : ℕ, w ≠ -2 * ((n : ℂ) + 1)) :
    riemannZeta w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst hw0
    rw [riemannZeta_zero]; norm_num
  set s : ℂ := 1 - w with hs
  have hsre : θ < s.re := by
    have : s.re = 1 - w.re := by simp [hs]
    linarith
  have hspos : 0 < s.re := lt_of_le_of_lt hθ hsre
  have hs_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h1
    apply hw0
    have : w = 1 - s := by simp [hs]
    rw [this, h1]; ring
  have hfe := riemannZeta_one_sub hs_nat hs1
  have hw' : 1 - s = w := by simp [hs]
  rw [hw'] at hfe
  rw [hfe]
  have hz : riemannZeta s ≠ 0 := h s hsre
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs_nat
  have hP : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    apply (Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_).mpr
    · have : (0 : ℝ) < Real.pi := Real.pi_pos
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    · intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
  have hC : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsk : s = 2 * (k : ℂ) + 1 := by
      have : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
        linear_combination 2 * hk
      exact mul_left_cancel₀ hpi this
    have hre : s.re = 2 * (k : ℝ) + 1 := by
      have := congrArg Complex.re hsk
      simpa using this
    have hk0' : 0 ≤ k := by
      by_contra hneg
      have hk1 : k ≤ -1 := by omega
      have hk2 : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
      linarith
    have hwk : w = -2 * (k : ℂ) := by
      have : w = 1 - s := by simp [hs]
      rw [this, hsk]; ring
    rcases lt_or_eq_of_le hk0' with hpos | hzero
    · have hkn : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      apply hexc (k - 1).toNat
      rw [hwk]
      have : ((((k - 1).toNat : ℕ) : ℂ)) = ((k - 1 : ℤ) : ℂ) := by exact_mod_cast hkn
      rw [this]; push_cast; ring
    · apply hw0
      rw [hwk, ← hzero]; simp
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hP) hG) hC) hz

/-- Trivial zeros are real zeros: the exclusion in `reflect_nonzero` cannot be dropped. -/
theorem trivial_zero_exists : riemannZeta (-2 * ((0 : ℕ) + 1)) = 0 ∧ (-2 * (((0 : ℕ) : ℂ) + 1)).re < 1 / 8 := by
  refine ⟨riemannZeta_neg_two_mul_nat_add_one 0, ?_⟩
  simp; norm_num

/-- Zeros under `ZeroFreeRight θ`: trivial, or in the closed band `1 - θ ≤ Re ≤ θ`. -/
theorem zero_trivial_or_band {θ : ℝ} (hθ : 0 ≤ θ) (h : ZeroFreeRight θ) {w : ℂ}
    (hz : riemannZeta w = 0) :
    (∃ n : ℕ, w = -2 * ((n : ℂ) + 1)) ∨ (1 - θ ≤ w.re ∧ w.re ≤ θ) := by
  by_cases ht : ∃ n : ℕ, w = -2 * ((n : ℂ) + 1)
  · exact Or.inl ht
  · right
    push Not at ht
    constructor
    · by_contra hlt
      push Not at hlt
      exact reflect_nonzero hθ h hlt ht hz
    · by_contra hlt
      push Not at hlt
      exact h w hlt hz

/-- Under `ZeroFreeRight 7/8`: no zero in the outer strip `0 < Re < 1/8` (and `7/8 < Re`);
every zero with `0 < Re < 1` has `1/8 ≤ Re ≤ 7/8`. -/
theorem zero_in_critical_strip_78 (h : ZeroFreeRight78) {w : ℂ} (hz : riemannZeta w = 0)
    (h0 : 0 < w.re) (h1 : w.re < 1) : (1 / 8 : ℝ) ≤ w.re ∧ w.re ≤ 7 / 8 := by
  rcases zero_trivial_or_band (θ := 7 / 8) (by norm_num) h hz with ⟨n, hn⟩ | hb
  · exfalso
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · constructor <;> norm_num at hb ⊢ <;> linarith [hb.1, hb.2]

/-- Outer strip on the left has no zero (no exclusion needed there). -/
theorem left_outer_strip_nonzero (h : ZeroFreeRight78) {w : ℂ} (h0 : 0 < w.re)
    (h1 : w.re < 1 / 8) : riemannZeta w ≠ 0 := by
  intro hz
  have := zero_in_critical_strip_78 h hz h0 (by linarith)
  linarith [this.1]

/-! ## (3) RH gives the zero-free half-planes -/

theorem rh_imp_zeroFreeRight_half : RiemannHypothesis → ZeroFreeRight (1 / 2) := by
  intro hRH s hs hz
  have h1 : s ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hz)
  have hn : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have := hRH s hz hn h1
  linarith

theorem zeroFreeRight_mono {a b : ℝ} (hab : a ≤ b) (h : ZeroFreeRight a) : ZeroFreeRight b :=
  fun s hs => h s (lt_of_le_of_lt hab hs)

theorem rh_imp_zeroFreeRight78 : RiemannHypothesis → ZeroFreeRight78 :=
  fun h => zeroFreeRight_mono (by norm_num) (rh_imp_zeroFreeRight_half h)

/-! ## (2) Eight strips of width 1/8 -/

/-- Open strip `k/8 < σ < (k+1)/8`, for `k = 0, …, 7`. -/
def band (k : Fin 8) (σ : ℝ) : Prop := (k.val : ℝ) / 8 < σ ∧ σ < ((k.val : ℝ) + 1) / 8

theorem band_width (k : Fin 8) : ((k.val : ℝ) + 1) / 8 - (k.val : ℝ) / 8 = 1 / 8 := by ring

theorem widths_sum : ∑ _k : Fin 8, (1 / 8 : ℝ) = 1 := by simp

theorem band_last (σ : ℝ) : band 7 σ ↔ 7 / 8 < σ ∧ σ < 1 := by
  unfold band; norm_num

theorem band_first (σ : ℝ) : band 0 σ ↔ 0 < σ ∧ σ < 1 / 8 := by
  unfold band; norm_num

/-- Six strips remain after removing the two outer ones. -/
theorem remaining_six :
    (Finset.univ.filter (fun k : Fin 8 => k ≠ 0 ∧ k ≠ 7)).card = 6 := by decide

/-- The six inner strips are three reflection pairs (1,6), (2,5), (3,4). -/
theorem inner_pairs :
    (Finset.univ.filter (fun k : Fin 8 => k ≠ 0 ∧ k ≠ 7 ∧ k.val < 4)).card = 3 := by decide

/-- The central line `4/8` is the upper edge of strip 3 and the lower edge of strip 4, and is `1/2`. -/
theorem central_line :
    ((3 : ℝ) + 1) / 8 = 1 / 2 ∧ (4 : ℝ) / 8 = 1 / 2 ∧ (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num

/-- `1/2` is the only fixed point of `σ ↦ 1 - σ`. -/
theorem fixed_point_unique (σ : ℝ) : 1 - σ = σ ↔ σ = 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem val_rev (k : Fin 8) : (Fin.rev k).val + k.val = 7 := by
  have := Fin.val_rev k
  omega

/-- `s ↦ 1 - s` sends strip `k` to strip `7 - k`. -/
theorem reflect_band (k : Fin 8) (σ : ℝ) (h : band k σ) : band (Fin.rev k) (1 - σ) := by
  have hv : ((Fin.rev k).val : ℝ) + (k.val : ℝ) = 7 := by exact_mod_cast val_rev k
  unfold band at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem rev_involutive (k : Fin 8) : Fin.rev (Fin.rev k) = k := Fin.rev_rev k

/-- No strip is its own mirror image (8 is even). -/
theorem rev_no_fixed : ∀ k : Fin 8, Fin.rev k ≠ k := by decide

/-- Every `σ` in `(0,1)` lies in the half-open strip of exactly one index `⌊8σ⌋`. -/
theorem cover (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ k : Fin 8, (k.val : ℝ) / 8 ≤ σ ∧ σ < ((k.val : ℝ) + 1) / 8 := by
  have hn : ⌊8 * σ⌋₊ < 8 := by
    rw [Nat.floor_lt (by linarith)]; push_cast; linarith
  refine ⟨⟨⌊8 * σ⌋₊, hn⟩, ?_, ?_⟩
  · have := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * σ)
    simp only; linarith
  · have := Nat.lt_floor_add_one (8 * σ)
    simp only; linarith

/-! ## (4) Arithmetic of kappa in the plain-moment lemma (OpenAI preprint, paper.tex lines 12532, 12581, 12833, 12932, 12957).
  Pure arithmetic on the numbers the preprint writes down; it says nothing about whether the lemma is true. -/

/-- `kappa = 2 beta - 1 >= 3/4  iff  beta >= 7/8`. -/
theorem kappa_ge_iff (β : ℝ) : (3 / 4 : ℝ) ≤ 2 * β - 1 ↔ (7 / 8 : ℝ) ≤ β := by
  constructor <;> intro h <;> linarith

/-- `s_kappa = (1+kappa)/2` equals `beta` when `kappa = 2 beta - 1`. -/
theorem sKappa_of_kappa (β : ℝ) : (1 + (2 * β - 1)) / 2 = β := by ring

/-- At the edge `kappa = 3/4` one has `s_kappa = 7/8`. -/
theorem sKappa_edge : (1 + (3 / 4 : ℝ)) / 2 = 7 / 8 := by norm_num

/-- `6 kappa - 1 >= 7/2` for `kappa >= 3/4` (line 12957). -/
theorem six_kappa_sub_one (κ : ℝ) (h : (3 / 4 : ℝ) ≤ κ) : (7 / 2 : ℝ) ≤ 6 * κ - 1 := by linarith

/-- `z <= M/(6 kappa) <= 2M/9` for `kappa >= 3/4`, `M >= 0` (line 12932). -/
theorem z_le_two_ninths (κ M : ℝ) (h : (3 / 4 : ℝ) ≤ κ) (hM : 0 ≤ M) :
    M / (6 * κ) ≤ 2 * M / 9 := by
  have hk : (0 : ℝ) < 6 * κ := by linarith
  rw [div_le_div_iff₀ hk (by norm_num)]
  nlinarith

/-- Margin of the displayed comparison chain (lines 12950-12977), as a fraction of `M`:
    `1 - 5/6 - 2/(6(6 kappa - 1))`.  It is positive exactly when `kappa > 1/2`; value 1/14 at 3/4,
    1/22 at 5/8, 0 at 1/2.  This is a check of that one chain only, not of the whole proof. -/
noncomputable def margin (κ : ℝ) : ℝ := 1 / 6 - 1 / (3 * (6 * κ - 1))

theorem margin_pos (κ : ℝ) (h : (1 / 2 : ℝ) < κ) : 0 < margin κ := by
  unfold margin
  have h1 : (0 : ℝ) < 3 * (6 * κ - 1) := by linarith
  rw [sub_pos, div_lt_div_iff₀ h1 (by norm_num)]
  linarith

theorem margin_values :
    margin (3 / 4) = 1 / 14 ∧ margin (5 / 8) = 1 / 22 ∧ margin (1 / 2) = 0 := by
  unfold margin; norm_num


end Slab78

#print axioms Slab78.reflect_nonzero
#print axioms Slab78.zero_trivial_or_band
#print axioms Slab78.zero_in_critical_strip_78
#print axioms Slab78.left_outer_strip_nonzero
#print axioms Slab78.rh_imp_zeroFreeRight78
#print axioms Slab78.trivial_zero_exists
#print axioms Slab78.remaining_six
#print axioms Slab78.inner_pairs
#print axioms Slab78.reflect_band
#print axioms Slab78.rev_no_fixed
#print axioms Slab78.cover
#print axioms Slab78.kappa_ge_iff
#print axioms Slab78.z_le_two_ninths
#print axioms Slab78.margin_pos
#print axioms Slab78.margin_values

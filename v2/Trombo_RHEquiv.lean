import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Trombo hypothesis ladder, next rung: equivalent forms of RH

Every open statement is a `def … : Prop`; nothing is assumed as an axiom.
The target is Mathlib's own `RiemannHypothesis`:
`∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`.

Contents.
* `RH_iff_noZerosRightHalf` : `RiemannHypothesis ↔ ∀ s, 1/2 < re s → ζ s ≠ 0`.
  Pole convention: Mathlib assigns `ζ 1` the junk value `(γ - log (4π))/2`; Mathlib's
  `riemannZeta_one_ne_zero` shows it is nonzero, so `s = 1` may stay inside the right-hand side.
* `QuasiRH θ` (zeros have `re ≤ θ`), with `RH → QuasiRH θ` for `θ ≥ 1/2`, `QuasiRH (1/2) → RH`,
  monotonicity in `θ`, the unconditional `QuasiRH 1`, and the half-plane form of `QuasiRH θ`.
* `mertensBound_noZerosRightHalf` : `MertensBound → ∀ s, 1/2 < re s → ζ s ≠ 0`
  (the Mertens part is copied from `Trombo_Mertens.lean`, mlib3, so this file stands alone).

Only the direction `MertensBound → RH` is proved; the converse `RH → MertensBound` is NOT
proved here (see `Trombo_RHtoMertens.lean`).
-/

open Complex Filter Asymptotics MeasureTheory Set Topology ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace TromboRHEquiv

/-- The Mertens function `M(x) = ∑_{1 ≤ n ≤ x} μ(n)` for real `x` (it is `0` for `x < 1`). -/
noncomputable def mertensM (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n

/-- Mertens-type bound (open; equivalent to RH, only `→ RH` is proved here):
for every `ε > 0` there is `C` with `|M(x)| ≤ C · x^(1/2+ε)` for all real `x ≥ 1`. -/
def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |(mertensM x : ℝ)| ≤ C * x ^ ((1 : ℝ) / 2 + ε)

/-- The Mertens conjecture `|M(x)| < √x` for all real `x ≥ 1`.
This statement is FALSE (Odlyzko–te Riele 1985); it is stated only for illustration. -/
def MertensConjecture : Prop := ∀ x : ℝ, 1 ≤ x → |(mertensM x : ℝ)| < Real.sqrt x

/-- `M` as a complex-valued function of a real variable. -/
noncomputable def F (t : ℝ) : ℂ := (mertensM t : ℂ)

/-- `g s = s · mellin F (-s) = s ∫_{t>0} t^(-s-1) M(t) dt`. -/
noncomputable def g (s : ℂ) : ℂ := s * mellin F (-s)

/-- `M(t) = 0` for `t < 1`. -/
lemma F_eq_zero {t : ℝ} (ht : t < 1) : F t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [F, mertensM, this]

/-- `F t = ∑_{k ∈ [1, ⌊t⌋]} μ(k)` in `ℂ`. -/
lemma F_eq_sum (t : ℝ) : F t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((μ k : ℤ) : ℂ) := by
  simp [F, mertensM]

/-- `F` is locally integrable on `(0, ∞)`. -/
lemma F_locInt : LocallyIntegrableOn F (Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc (fun k : ℕ => ((μ k : ℤ) : ℂ)) (m := 1)
    (le_refl (0 : ℝ)) (g := fun _ => (1 : ℂ)) (locallyIntegrableOn_const _)
  have hF : F = fun t => (fun _ => (1 : ℂ)) t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((μ k : ℤ) : ℂ) := by
    funext t; simp [F_eq_sum]
  rw [hF]
  exact h.mono_set Ioi_subset_Ici_self

/-- Trivial bound: partial sums of `μ` are `O(n)`. -/
lemma partial_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (↗μ) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  calc ‖∑ k ∈ Finset.Icc 1 n, (↗μ) k‖ ≤ ∑ k ∈ Finset.Icc 1 n, ‖(↗μ) k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have : ‖((μ k : ℤ) : ℂ)‖ = |((μ k : ℤ) : ℝ)| := by
          rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        simp only [this]
        exact_mod_cast abs_moebius_le_one
    _ = 1 * ‖(n : ℝ) ^ (1 : ℝ)‖ := by simp

/-- On `re s > 1`, the Dirichlet series of `μ` equals `g s`. -/
lemma LSeries_moebius_eq_g {s : ℂ} (hs : 1 < s.re) : L ↗μ s = g s := by
  rw [LSeries_eq_mul_integral _ zero_le_one hs (LSeriesSummable_moebius_iff.mpr hs) partial_bigO]
  unfold g mellin
  congr 1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ici_subset_Ioi.mpr one_pos) ?_, integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, F_eq_sum]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    simp only [Set.mem_sdiff, mem_Ioi, mem_Ici, not_le] at ht
    rw [F_eq_zero ht.2, smul_zero]

/-- Under `MertensBound`, `g` is complex-differentiable at every `s` with `re s > 1/2`. -/
lemma g_differentiableAt (hM : MertensBound) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ g s := by
  set ε := (s.re - 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, hC⟩ := hM ε hε0
  have hmel : DifferentiableAt ℂ (mellin F) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 2 + ε)) (b := -s.re - 1)
      F_locInt ?_ ?_ ?_ ?_
    · refine IsBigO.of_bound C ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have h1 : ‖F t‖ = |(mertensM t : ℝ)| := by
        rw [F, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖t ^ (-(-(1 / 2 + ε)))‖ = t ^ ((1 : ℝ) / 2 + ε) := by
        rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      rw [h1, h2]
      exact hC t ht
    · simp only [neg_re]; linarith
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [F_eq_zero ht.2]; simp
    · simp only [neg_re]; linarith
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact differentiableAt_id.mul (hmel.comp s hneg)

/-- Unconditional: `{z | 1/2 < re z} \ {1}` is preconnected. -/
lemma isPreconnected_U : IsPreconnected ({z : ℂ | 1 / 2 < z.re} ∩ {1}ᶜ) := by
  set A : Set ℂ := {z | (1 : ℝ) / 2 < z.re} ∩ {z | 0 < z.im}
  set B : Set ℂ := {z | (1 : ℝ) < z.re}
  set C : Set ℂ := {z | (1 : ℝ) / 2 < z.re} ∩ {z | z.im < 0}
  set D : Set ℂ := {z | (1 : ℝ) / 2 < z.re} ∩ {z | z.re < 1}
  have hA : IsPreconnected A :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)).isPreconnected
  have hB : IsPreconnected B := (convex_halfSpace_re_gt _).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected
  have hD : IsPreconnected D :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hAB : IsPreconnected (A ∪ B) :=
    IsPreconnected.union (2 + I) (by norm_num [A]) (by norm_num [B]) hA hB
  have hABC : IsPreconnected (A ∪ B ∪ C) :=
    IsPreconnected.union (2 - I) (Or.inr (by norm_num [B])) (by norm_num [C]) hAB hC
  have hABCD : IsPreconnected (A ∪ B ∪ C ∪ D) :=
    IsPreconnected.union ((3 / 4 : ℂ) + I) (Or.inl (Or.inl (by norm_num [A])))
      (by norm_num [D]) hABC hD
  have hEq : ({z : ℂ | 1 / 2 < z.re} ∩ {1}ᶜ) = A ∪ B ∪ C ∪ D := by
    ext z
    simp only [A, B, C, D, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff,
      mem_union]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hre, him⟩)
      · rcases lt_trichotomy z.re 1 with h1 | h1 | h1
        · exact Or.inr ⟨hre, h1⟩
        · exact absurd (Complex.ext (by simpa using h1) (by simpa using him)) hne
        · exact Or.inl (Or.inl (Or.inr h1))
      · exact Or.inl (Or.inl (Or.inl ⟨hre, him⟩))
    · rintro (((⟨hre, him⟩ | hre) | ⟨hre, him⟩) | ⟨hre, hlt⟩)
      · exact ⟨hre, fun h => by rw [h] at him; simp at him⟩
      · exact ⟨by linarith, fun h => by rw [h] at hre; simp at hre⟩
      · exact ⟨hre, fun h => by rw [h] at him; simp at him⟩
      · exact ⟨hre, fun h => by rw [h] at hlt; simp at hlt⟩
  rw [hEq]; exact hABCD

/-- Under `MertensBound`, `ζ(s) ≠ 0` whenever `re s > 1/2` and `s ≠ 1`. -/
theorem mertensBound_zeta_ne_zero (hM : MertensBound) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} ∩ {1}ᶜ with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ (fun z => riemannZeta z * g z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact ((differentiableAt_riemannZeta hz.2).mul
      (g_differentiableAt hM hz.1)).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : (fun z => riemannZeta z * g z) =ᶠ[𝓝 (2 : ℂ)] fun _ => (1 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz, LSeries_moebius_eq_g hz] at h
    exact h
  have hEq := hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_U
    h2U hev
  have hsU : s ∈ U := ⟨hs, hs1⟩
  have h1 : riemannZeta s * g s = 1 := hEq hsU
  exact left_ne_zero_of_mul_eq_one h1

/-- Unconditional: a zero `s ≠ 1` of `ζ` that is not of the form `-2(n+1)` lies in the open
critical strip `0 < re s < 1`. (Same proof as in `Trombo_GRH.lean`.) -/
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

/-- Main theorem: `MertensBound` implies Mathlib's `RiemannHypothesis`. -/
theorem mertensBound_imp_RH : MertensBound → RiemannHypothesis := by
  intro hM s hz htriv hs1
  obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hn : ∀ n : ℕ, s ≠ -n := by
      intro n h
      have : s.re = -(n : ℝ) := by rw [h]; simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hn hs1
    rw [hz, mul_zero] at hfe
    refine mertensBound_zeta_ne_zero hM (s := 1 - s) ?_ ?_ hfe
    · simp; linarith
    · intro h
      have : (1 - s).re = (1 : ℂ).re := by rw [h]
      simp at this; linarith
  · exact heq
  · exact absurd hz (mertensBound_zeta_ne_zero hM hgt hs1)


/-! ## Part A1: RH ⇔ no zeros in the right half `re s > 1/2` -/

/-- Unconditional: a point with positive real part is not a trivial zero `-2(n+1)`. -/
lemma not_trivial_of_re_pos {s : ℂ} (hs : 0 < s.re) : ¬∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at hs
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Unconditional reflection: if `ζ s = 0`, `0 < re s` and `s ≠ 1`, then `ζ (1 - s) = 0`. -/
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

/-- **RH, half-plane form.** Mathlib's `RiemannHypothesis` holds iff `ζ s ≠ 0` for every `s`
with `1/2 < re s`. The point `s = 1` is included on the right; there `ζ 1` is Mathlib's junk value,
which is nonzero (`riemannZeta_one_ne_zero`). -/
theorem RH_iff_noZerosRightHalf :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s hs hz
    by_cases hs1 : s = 1
    · subst hs1; exact riemannZeta_one_ne_zero hz
    · have h := hRH s hz (not_trivial_of_re_pos (by linarith)) hs1
      linarith
  · intro h s hz htriv hs1
    obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exfalso
      exact h (1 - s) (by simp; linarith) (zeta_one_sub_eq_zero hz h0 hs1)
    · exact heq
    · exact absurd hz (h s hgt)

/-! ## Part A2: quasi-RH with exponent `θ` -/

/-- Quasi-Riemann hypothesis with exponent `θ` (not proved here; false for `θ < 1/2` since zeros on the critical line exist (Hardy 1914); for `1/2 ≤ θ < 1` open in the refereed literature, with a 2026 claim for `θ = 7/8` by OpenAI that is not checked here):
every nontrivial zero
`s ≠ 1` of `ζ` has `re s ≤ θ`. The meaningful range is `1/2 ≤ θ < 1`. -/
def QuasiRH (θ : ℝ) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re ≤ θ

/-- `RH → QuasiRH θ` for every `θ ≥ 1/2`. -/
theorem RH_imp_quasiRH {θ : ℝ} (hθ : 1 / 2 ≤ θ) : RiemannHypothesis → QuasiRH θ := by
  intro hRH s hz htriv hs1
  rw [hRH s hz htriv hs1]; exact hθ

/-- Monotonicity: `θ ≤ θ'` and `QuasiRH θ` give `QuasiRH θ'`. -/
theorem quasiRH_mono {θ θ' : ℝ} (h : θ ≤ θ') : QuasiRH θ → QuasiRH θ' :=
  fun hq s hz htriv hs1 => (hq s hz htriv hs1).trans h

/-- `QuasiRH (1/2) → RH` (by the functional-equation reflection `s ↦ 1 - s`). -/
theorem quasiRH_half_imp_RH : QuasiRH (1 / 2) → RiemannHypothesis := by
  intro hq s hz htriv hs1
  obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
  have hle := hq s hz htriv hs1
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hz' := zeta_one_sub_eq_zero hz h0 hs1
    have hre : (1 - s).re = 1 - s.re := by simp
    have htriv' := not_trivial_of_re_pos (s := 1 - s) (by rw [hre]; linarith)
    have hs1' : 1 - s ≠ 1 := by
      intro h; have : (1 - s).re = (1 : ℂ).re := by rw [h]
      simp at this; linarith
    have := hq (1 - s) hz' htriv' hs1'
    rw [hre] at this; linarith
  · exact heq

/-- `RiemannHypothesis ↔ QuasiRH (1/2)`. -/
theorem RH_iff_quasiRH_half : RiemannHypothesis ↔ QuasiRH (1 / 2) :=
  ⟨RH_imp_quasiRH le_rfl, quasiRH_half_imp_RH⟩

/-- Unconditional: `QuasiRH 1` holds (every nontrivial zero `s ≠ 1` has `re s < 1`). This is only the classical non-vanishing on `re s ≥ 1`; it is not the quasi-RH `∃ θ < 1, QuasiRH θ`. -/
theorem quasiRH_one : QuasiRH 1 :=
  fun _ hz htriv _ => (zeta_zero_in_strip hz htriv).2.le

/-- Half-plane form of `QuasiRH θ` for `θ ≥ 0`: `QuasiRH θ ↔ ∀ s, θ < re s → s ≠ 1 → ζ s ≠ 0`. -/
theorem quasiRH_iff_noZeros {θ : ℝ} (hθ : 0 ≤ θ) :
    QuasiRH θ ↔ ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro hq s hs hs1 hz
    have := hq s hz (not_trivial_of_re_pos (by linarith)) hs1
    linarith
  · intro h s hz htriv hs1
    by_contra hlt
    push Not at hlt
    exact h s hlt hs1 hz

/-- If `QuasiRH θ` held with some `θ < 1/2`, then `ζ` would have no nontrivial zero `s ≠ 1`
at all (reflection). This is only an implication; no statement about the existence of zeros
is proved here. -/
theorem quasiRH_lt_half_imp_noNontrivialZeros {θ : ℝ} (hθ : θ < 1 / 2) (hq : QuasiRH θ) :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → False := by
  intro s hz htriv hs1
  obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
  have hle := hq s hz htriv hs1
  have hz' := zeta_one_sub_eq_zero hz h0 hs1
  have hre : (1 - s).re = 1 - s.re := by simp
  have htriv' := not_trivial_of_re_pos (s := 1 - s) (by rw [hre]; linarith)
  have hs1' : 1 - s ≠ 1 := by
    intro h; have : (1 - s).re = (1 : ℂ).re := by rw [h]
    simp at this; linarith
  have := hq (1 - s) hz' htriv' hs1'
  rw [hre] at this; linarith

/-! ## Part A3: MertensBound ⇒ no zeros in `re s > 1/2` (corollary of mlib3) -/

/-- `MertensBound → ∀ s, 1/2 < re s → ζ s ≠ 0` (including `s = 1`, junk value). -/
theorem mertensBound_noZerosRightHalf :
    MertensBound → ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 :=
  fun hM => RH_iff_noZerosRightHalf.mp (mertensBound_imp_RH hM)

/-- `MertensBound → QuasiRH θ` for every `θ ≥ 1/2`. -/
theorem mertensBound_imp_quasiRH {θ : ℝ} (hθ : 1 / 2 ≤ θ) : MertensBound → QuasiRH θ :=
  fun hM => RH_imp_quasiRH hθ (mertensBound_imp_RH hM)

end TromboRHEquiv

#print axioms TromboRHEquiv.F_eq_zero
#print axioms TromboRHEquiv.F_eq_sum
#print axioms TromboRHEquiv.F_locInt
#print axioms TromboRHEquiv.partial_bigO
#print axioms TromboRHEquiv.LSeries_moebius_eq_g
#print axioms TromboRHEquiv.g_differentiableAt
#print axioms TromboRHEquiv.isPreconnected_U
#print axioms TromboRHEquiv.mertensBound_zeta_ne_zero
#print axioms TromboRHEquiv.zeta_zero_in_strip
#print axioms TromboRHEquiv.mertensBound_imp_RH
#print axioms TromboRHEquiv.not_trivial_of_re_pos
#print axioms TromboRHEquiv.zeta_one_sub_eq_zero
#print axioms TromboRHEquiv.RH_iff_noZerosRightHalf
#print axioms TromboRHEquiv.RH_imp_quasiRH
#print axioms TromboRHEquiv.quasiRH_mono
#print axioms TromboRHEquiv.quasiRH_half_imp_RH
#print axioms TromboRHEquiv.RH_iff_quasiRH_half
#print axioms TromboRHEquiv.quasiRH_one
#print axioms TromboRHEquiv.quasiRH_iff_noZeros
#print axioms TromboRHEquiv.quasiRH_lt_half_imp_noNontrivialZeros
#print axioms TromboRHEquiv.mertensBound_noZerosRightHalf
#print axioms TromboRHEquiv.mertensBound_imp_quasiRH

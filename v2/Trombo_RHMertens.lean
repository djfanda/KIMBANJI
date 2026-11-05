import Trombo_ZetaLogBound
import Trombo_PerronMoebius
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Items 6–7: contour shift and assembly of `RH → MertensBound`

* `invZeta s := (s - 1) / Z s` is the holomorphic version of `1/ζ` (it agrees with `(ζ s)⁻¹` for
  `s ≠ 1`, and under RH is holomorphic on `re s > 1/2`; Mathlib's junk value `ζ 1` is avoided).
* Item 6 `RH_contour_shift`: under RH, Cauchy's theorem on the rectangle
  `[σ₀, 2] × [-T, T]` for `invZeta s · x^s / s` (no residue: `s = 0` lies outside, and `s = 1` is a
  zero of `invZeta`, not a pole).
* Supporting bounds: `RH_invZeta_bound` (`‖invZeta s‖ ≤ C (3 + |im s|)^ε` on `1/2+η ≤ re s ≤ 2`),
  `norm_left_integral_le`, `norm_horizontal_integral_le`, `perron_error_le`.
* Item 7 `RH_imp_mertensBound`: `RiemannHypothesis → MertensBound`.
-/

open Complex Set Filter MeasureTheory ArithmeticFunction
open scoped Real Interval ArithmeticFunction.Moebius

namespace TromboRHMertens

open TromboZetaLog

/-! ## `invZeta` -/

/-- The holomorphic reciprocal of `ζ`: `invZeta s = (s - 1) / Z s`, `Z s = (s - 1) ζ(s)`. -/
noncomputable def invZeta (s : ℂ) : ℂ := (s - 1) / Z s

lemma invZeta_of_ne {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [invZeta, Z_of_ne hs, div_mul_eq_div_div, div_self h1, one_div]

/-- Under RH, `Z s ≠ 0` for `re s > 1/2`. -/
lemma RH_Z_ne_zero (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) : Z s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · simp [Z]
  · rw [Z_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (RH_zeta_ne_zero hRH hs)

/-- Under RH, `invZeta` is complex-differentiable at every `s` with `re s > 1/2`. -/
lemma RH_invZeta_differentiableAt (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ invZeta s :=
  (differentiableAt_id.sub_const 1).div (Z_differentiable s) (RH_Z_ne_zero hRH hs)

/-! ## Item 6: contour shift -/

/-- The Perron integrand on the plane: `invZeta s · x^s / s`. -/
noncomputable def perronF (x : ℝ) (s : ℂ) : ℂ := invZeta s * ((x : ℂ) ^ s / s)

lemma perronF_vertical (x c t : ℝ) :
    perronF x ((c : ℂ) + t * I) = invZeta ((c : ℂ) + t * I) * TauCeti.perronIntegrand x c t := by
  rw [perronF, TauCeti.perronIntegrand_def]

/-- **Item 6 (contour shift).** Under RH, for `x > 0`, `1/2 < σ₀ ≤ 2` and real `T`:
`I • (∫_{-T}^{T} invZeta(2+it) P(x,2,t) dt − ∫_{-T}^{T} invZeta(σ₀+it) P(x,σ₀,t) dt)
   = ∫_{σ₀}^{2} F(σ + iT) dσ − ∫_{σ₀}^{2} F(σ − iT) dσ`,
with `P` Tau Ceti's `perronIntegrand` and `F = perronF x`. -/
theorem RH_contour_shift (hRH : RiemannHypothesis) {x σ₀ T : ℝ} (hx : 0 < x)
    (hσ₀ : 1 / 2 < σ₀) (hσ₀2 : σ₀ ≤ 2) :
    I • ((∫ t in -T..T, invZeta ((2 : ℝ) + t * I) * TauCeti.perronIntegrand x 2 t) -
        ∫ t in -T..T, invZeta ((σ₀ : ℂ) + t * I) * TauCeti.perronIntegrand x σ₀ t) =
      (∫ σ in σ₀..2, perronF x ((σ : ℂ) + T * I)) -
        ∫ σ in σ₀..2, perronF x ((σ : ℂ) + (-T : ℝ) * I) := by
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn (perronF x)
    ((σ₀ : ℂ) + (-T : ℝ) * I) ((2 : ℝ) + (T : ℝ) * I) ?_
  · simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, add_im,
      mul_im, mul_one, zero_add, add_zero] at hrect
    simp only [perronF_vertical, smul_eq_mul] at hrect ⊢
    linear_combination hrect
  · intro s hs
    rw [mem_reProdIm] at hs
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero,
      zero_mul] at hs
    have hsre : σ₀ ≤ s.re := by
      have := hs.1
      rw [uIcc_of_le (by simpa using hσ₀2)] at this
      simpa using this.1
    have hre : 1 / 2 < s.re := by linarith
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact ((RH_invZeta_differentiableAt hRH hre).mul
      ((differentiableAt_id.const_cpow (Or.inl hxc)).div differentiableAt_id hs0)).differentiableWithinAt

/-! ## Bounds for the shifted contour -/

/-- **Bound for `invZeta` on `1/2 + η ≤ re s ≤ 2`.** Under RH, for `0 < η ≤ 1`, `ε > 0` there is
`C ≥ 0` with `‖invZeta s‖ ≤ C (3 + |im s|)^ε` for all `s` with `1/2 + η ≤ re s ≤ 2`.
(Item 5 for `|im s| ≥ 3`; compactness of `[1/2+η, 2] × [-3, 3]` otherwise.) -/
theorem RH_invZeta_bound (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 + η ≤ s.re → s.re ≤ 2 →
      ‖invZeta s‖ ≤ C * (3 + |s.im|) ^ ε := by
  obtain ⟨C₁, hC₁⟩ := RH_inv_zeta_bound hRH hη hη1 hε
  set K : Set ℂ := Metric.closedBall (5 / 4 : ℂ) 4 ∩ {s | 1 / 2 + η ≤ s.re} with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_re)
  have hcont : ContinuousOn invZeta K := fun s hs => by
    have h := hs.2
    simp only [Set.mem_ofPred_eq] at h
    exact (RH_invZeta_differentiableAt hRH (by linarith)).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  have hCnn : 0 ≤ max C₀ 0 + max C₁ 0 := by positivity
  refine ⟨max C₀ 0 + max C₁ 0, hCnn, fun s hσ hσ2 => ?_⟩
  have hpow : 1 ≤ (3 + |s.im|) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hε.le
  by_cases ht : 3 ≤ |s.im|
  · have hs1 : s ≠ 1 := by
      intro h; rw [h] at ht; simp at ht; norm_num at ht
    rw [invZeta_of_ne hs1]
    have h1 := hC₁ s hσ ht
    have h2 : |s.im| ^ ε ≤ (3 + |s.im|) ^ ε :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith) hε.le
    have h3 : 0 ≤ |s.im| ^ ε := Real.rpow_nonneg (abs_nonneg _) _
    have h4 : 0 ≤ (3 + |s.im|) ^ ε := by linarith
    calc ‖(riemannZeta s)⁻¹‖ ≤ C₁ * |s.im| ^ ε := h1
      _ ≤ max C₁ 0 * (3 + |s.im|) ^ ε := mul_le_mul (le_max_left _ _) h2 h3 (le_max_right _ _)
      _ ≤ (max C₀ 0 + max C₁ 0) * (3 + |s.im|) ^ ε :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right C₀ 0]) h4
  · push Not at ht
    have hsK : s ∈ K := by
      refine ⟨?_, hσ⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have e1 : (s - 5 / 4).re = s.re - 5 / 4 := by simp
      have e2 : (s - 5 / 4).im = s.im := by simp
      calc ‖s - 5 / 4‖ ≤ |(s - 5 / 4).re| + |(s - 5 / 4).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 3 / 4 + 3 := by
            rw [e1, e2]
            have : |s.re - 5 / 4| ≤ 3 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
            linarith
        _ ≤ 4 := by norm_num
    have h0 := hC₀ s hsK
    calc ‖invZeta s‖ ≤ C₀ := h0
      _ ≤ (max C₀ 0 + max C₁ 0) * 1 := by linarith [le_max_left C₀ 0, le_max_right C₁ 0]
      _ ≤ (max C₀ 0 + max C₁ 0) * (3 + |s.im|) ^ ε := mul_le_mul_of_nonneg_left hpow hCnn

/-- `∫_{-T}^{T} (1 + |t|)⁻¹ dt = 2 log (1 + T)` for `T ≥ 0`. -/
lemma integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, (1 + |t|)⁻¹ = 2 * Real.log (1 + T) := by
  have hcont : Continuous (fun t : ℝ => (1 + |t|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + |t|))
  have hpos : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    have h1 : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (fun u : ℝ => u⁻¹) (1 + t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hT] at ht
      simp only [abs_of_nonneg ht.1]
    rw [h1, intervalIntegral.integral_comp_add_left (fun u : ℝ => u⁻¹) 1,
      integral_inv_of_pos (by norm_num) (by linarith)]
    simp
  have hneg : ∫ t in -T..0, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) (fun t : ℝ => (1 + |t|)⁻¹)
    simp only [abs_neg, neg_zero] at h
    rw [← h, hpos]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), hneg, hpos]
  ring

/-- **Left vertical integral.** If `‖invZeta (σ₀ + it)‖ ≤ C (3 + |t|)^ε` for `|t| ≤ T`, with
`x ≥ 1`, `σ₀ ≥ 1/2`, `T ≥ 0`, `C ≥ 0`, `ε ≥ 0`, then
`‖∫_{-T}^{T} invZeta(σ₀+it) P(x,σ₀,t) dt‖ ≤ 8 C x^{σ₀} (3 + T)^ε log (1 + T)`. -/
theorem norm_left_integral_le {x σ₀ T C ε : ℝ} (hx : 1 ≤ x) (hσ₀ : 1 / 2 ≤ σ₀) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hB : ∀ t : ℝ, |t| ≤ T → ‖invZeta ((σ₀ : ℂ) + t * I)‖ ≤ C * (3 + |t|) ^ ε) :
    ‖∫ t in -T..T, invZeta ((σ₀ : ℂ) + t * I) * TauCeti.perronIntegrand x σ₀ t‖ ≤
      8 * C * x ^ σ₀ * (3 + T) ^ ε * Real.log (1 + T) := by
  set K := 4 * C * x ^ σ₀ * (3 + T) ^ ε with hK
  have hxp : 0 < x ^ σ₀ := Real.rpow_pos_of_pos (by linarith) _
  have hTp : 0 ≤ (3 + T) ^ ε := Real.rpow_nonneg (by linarith) _
  have hbound : ∀ t ∈ Ioc (-T) T, ‖invZeta ((σ₀ : ℂ) + t * I) * TauCeti.perronIntegrand x σ₀ t‖
      ≤ K * (1 + |t|)⁻¹ := by
    intro t ht
    have hta : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    rw [norm_mul, TauCeti.norm_perronIntegrand (by linarith)]
    have h1 := hB t hta
    have h2 : (3 + |t|) ^ ε ≤ (3 + T) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by linarith) hε
    have a1 : |σ₀| ≤ Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg t])
    have a2 : |t| ≤ Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg σ₀])
    have hσa : σ₀ ≤ |σ₀| := le_abs_self σ₀
    have hsq : (1 + |t|) / 4 ≤ Real.sqrt (σ₀ ^ 2 + t ^ 2) := by linarith [abs_nonneg t]
    have hsqpos : 0 < (1 + |t|) / 4 := by positivity
    have h3 : x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2) ≤ x ^ σ₀ * (4 * (1 + |t|)⁻¹) := by
      rw [div_le_iff₀ (hsqpos.trans_le hsq)]
      have e : x ^ σ₀ = x ^ σ₀ * (4 * (1 + |t|)⁻¹) * ((1 + |t|) / 4) := by
        field_simp
      calc x ^ σ₀ = x ^ σ₀ * (4 * (1 + |t|)⁻¹) * ((1 + |t|) / 4) := e
        _ ≤ x ^ σ₀ * (4 * (1 + |t|)⁻¹) * Real.sqrt (σ₀ ^ 2 + t ^ 2) := by gcongr
    have h4 : ‖invZeta ((σ₀ : ℂ) + t * I)‖ ≤ C * (3 + T) ^ ε :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hC)
    calc ‖invZeta ((σ₀ : ℂ) + t * I)‖ * (x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2))
        ≤ (C * (3 + T) ^ ε) * (x ^ σ₀ * (4 * (1 + |t|)⁻¹)) :=
          mul_le_mul h4 h3 (by positivity) (mul_nonneg hC hTp)
      _ = K * (1 + |t|)⁻¹ := by rw [hK]; ring
  have hcont : Continuous (fun t : ℝ => K * (1 + |t|)⁻¹) :=
    continuous_const.mul ((continuous_const.add continuous_abs).inv₀ (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + |t|)))
  have hii : IntervalIntegrable (fun t : ℝ => K * (1 + |t|)⁻¹) volume (-T) T :=
    hcont.intervalIntegrable _ _
  have := intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Eventually.of_forall (fun t ht => hbound t ht)) hii
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT] at this
  calc _ ≤ K * (2 * Real.log (1 + T)) := this
    _ = _ := by rw [hK]; ring

/-- **Horizontal integral.** If `‖invZeta (σ + iy)‖ ≤ C (3 + |y|)^ε` for `σ₀ ≤ σ ≤ 2`, with
`x ≥ 1`, `σ₀ ≤ 2`, `y ≠ 0`, `C ≥ 0`, then
`‖∫_{σ₀}^{2} F(σ + iy) dσ‖ ≤ C (3+|y|)^ε x² / |y| · |2 - σ₀|`. -/
theorem norm_horizontal_integral_le {x σ₀ y C ε : ℝ} (hx : 1 ≤ x) (hσ₀2 : σ₀ ≤ 2)
    (hy : 0 < |y|) (hC : 0 ≤ C)
    (hB : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 → ‖invZeta ((σ : ℂ) + y * I)‖ ≤ C * (3 + |y|) ^ ε) :
    ‖∫ σ in σ₀..2, perronF x ((σ : ℂ) + y * I)‖ ≤
      C * (3 + |y|) ^ ε * x ^ (2 : ℝ) / |y| * |2 - σ₀| := by
  have hCe : 0 ≤ C * (3 + |y|) ^ ε := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * (3 + |y|) ^ ε * (x ^ (2 : ℝ) / |y|)) (a := σ₀) (b := 2)
    (f := fun σ : ℝ => perronF x ((σ : ℂ) + y * I)) ?_
  · calc _ ≤ C * (3 + |y|) ^ ε * (x ^ (2 : ℝ) / |y|) * |2 - σ₀| := this
      _ = _ := by ring
  intro σ hσ
  rw [uIoc_of_le hσ₀2] at hσ
  rw [perronF_vertical, norm_mul, TauCeti.norm_perronIntegrand (by linarith)]
  have h1 := hB σ hσ.1.le hσ.2
  have h2 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
  have h3 : |y| ≤ Real.sqrt (σ ^ 2 + y ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg σ])
  have h4 : x ^ σ / Real.sqrt (σ ^ 2 + y ^ 2) ≤ x ^ (2 : ℝ) / |y| :=
    div_le_div₀ (Real.rpow_nonneg (by linarith) _) h2 hy h3
  exact mul_le_mul h1 h4 (div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _)) hCe

/-- **Perron error at `c = 2`, `x = N + 1/2`.** For `N ≥ 1` and `T > 0`:
`∑' n, ‖μ(n)‖ (x/n)² / (π T |log (x/n)|) ≤ (6 x² + 16 x (2N + 1)) / (π T)`. -/
theorem perron_error_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 < T) :
    ∑' n : ℕ, ‖((μ n : ℤ) : ℂ)‖ * ((((N : ℝ) + 1 / 2) / n) ^ (2 : ℝ) /
        (π * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)) ≤
      (6 * ((N : ℝ) + 1 / 2) ^ 2 + 16 * ((N : ℝ) + 1 / 2) * (2 * N + 1)) / (π * T) := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hx : 0 < x := by positivity
  have hx1 : 3 / 2 ≤ x := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hπT : 0 < π * T := mul_pos Real.pi_pos hT
  have hlog2 : 1 / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set ind : ℕ → ℝ := fun n => if n < 2 * N + 1 then 16 * x else 0 with hind
  set g : ℕ → ℝ := fun n => (3 * (x ^ 2 * (n : ℝ) ^ (-2 : ℝ)) + ind n) / (π * T) with hg
  set e : ℕ → ℝ := fun n => ‖((μ n : ℤ) : ℂ)‖ * ((x / n) ^ (2 : ℝ) / (π * T * |Real.log (x / n)|))
    with he
  have hind0 : ∀ n, 0 ≤ ind n := fun n => by
    simp only [hind]; split_ifs <;> linarith
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    simp only [he]
    exact mul_nonneg (norm_nonneg _) (div_nonneg (Real.rpow_nonneg (by positivity) _)
      (by positivity))
  -- pointwise bound
  have hle : ∀ n, e n ≤ g n := by
    intro n
    simp only [he, hg]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [CharP.cast_eq_zero, div_zero]
      rw [Real.zero_rpow (by norm_num)]
      simp only [zero_div, mul_zero]
      exact div_nonneg (add_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _))) (hind0 0)) hπT.le
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      norm_cast; exact ArithmeticFunction.abs_moebius_le_one
    set y := x / n with hydef
    have hy : 0 < y := div_pos hx hnr
    have hy2 : y ^ (2 : ℝ) = x ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
      rw [hydef, Real.div_rpow hx.le hnr.le, Real.rpow_neg hnr.le, div_eq_mul_inv]
      norm_cast
    have hypos : 0 ≤ y ^ (2 : ℝ) := Real.rpow_nonneg hy.le _
    -- reduce to a bound for `y² / (πT |log y|)`
    suffices hsuff : y ^ (2 : ℝ) / (π * T * |Real.log y|) ≤
        (3 * (x ^ 2 * (n : ℝ) ^ (-2 : ℝ)) + ind n) / (π * T) by
      calc ‖((μ n : ℤ) : ℂ)‖ * (y ^ (2 : ℝ) / (π * T * |Real.log y|))
          ≤ 1 * (y ^ (2 : ℝ) / (π * T * |Real.log y|)) :=
            mul_le_mul_of_nonneg_right hμ (div_nonneg hypos (by positivity))
        _ ≤ _ := by rw [one_mul]; exact hsuff
    have hdiv : ∀ L : ℝ, 0 < L → L ≤ |Real.log y| →
        y ^ (2 : ℝ) / (π * T * |Real.log y|) ≤ y ^ (2 : ℝ) / L / (π * T) := by
      intro L hL hLle
      rw [div_div, mul_comm L]
      exact div_le_div_of_nonneg_left hypos (mul_pos hπT hL) (mul_le_mul_of_nonneg_left hLle hπT.le)
    by_cases hA : Real.log 2 ≤ |Real.log y|
    · calc y ^ (2 : ℝ) / (π * T * |Real.log y|) ≤ y ^ (2 : ℝ) / Real.log 2 / (π * T) :=
            hdiv _ (by linarith) hA
        _ ≤ (3 * (x ^ 2 * (n : ℝ) ^ (-2 : ℝ)) + ind n) / (π * T) := by
            apply div_le_div_of_nonneg_right _ hπT.le
            rw [div_le_iff₀ (by linarith), ← hy2]
            have ha : 0 ≤ 3 * y ^ (2 : ℝ) + ind n :=
              add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hypos) (hind0 n)
            calc y ^ (2 : ℝ) = 3 * y ^ (2 : ℝ) * (1 / 3) := by ring
              _ ≤ (3 * y ^ (2 : ℝ) + ind n) * (1 / 3) := by
                  have := hind0 n
                  gcongr; linarith
              _ ≤ (3 * y ^ (2 : ℝ) + ind n) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 ha
    · push Not at hA
      -- then `1/2 < y < 2`
      have hy2' : y < 2 := by
        by_contra h; push Not at h
        have := Real.log_le_log (by norm_num) h
        rw [abs_of_nonneg (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])] at hA
        linarith
      have hyhalf : 1 / 2 < y := by
        by_contra h; push Not at h
        have h1 := Real.log_le_log hy h
        have h2 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
        rw [h2] at h1
        have : |Real.log y| = - Real.log y := abs_of_neg (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
        linarith
      have hn2x : (n : ℝ) < 2 * x := by
        rw [hydef, lt_div_iff₀ hnr] at hyhalf; linarith
      have hindn : ind n = 16 * x := by
        simp only [hind]
        rw [ite_eq_left]
        have : (n : ℝ) < 2 * N + 1 := by rw [hxdef] at hn2x; linarith
        exact_mod_cast this
      -- `|log y| ≥ 1/(4x)`
      have hlogb : 1 / (4 * x) ≤ |Real.log y| := by
        rcases le_or_gt n N with hnN | hnN
        · have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
          have h1 := Real.one_sub_inv_le_log_of_pos hy
          have hyinv : y⁻¹ = n / x := by rw [hydef, inv_div]
          rw [hyinv] at h1
          have h2 : 1 / (4 * x) ≤ 1 - n / x := by
            rw [div_le_iff₀ (by positivity)]
            have : 1 - n / x = (x - n) / x := by field_simp
            rw [this, div_mul_eq_mul_div, le_div_iff₀ hx]
            nlinarith
          exact (h2.trans h1).trans (le_abs_self _)
        · have hnN' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hnN
          have h1 := Real.one_sub_inv_le_log_of_pos (inv_pos.mpr hy)
          rw [inv_inv, Real.log_inv] at h1
          have h2 : 1 / (4 * x) ≤ 1 - y := by
            rw [hydef]
            have : 1 - x / n = (n - x) / n := by field_simp
            rw [this, div_le_div_iff₀ (by positivity) hnr]
            nlinarith
          exact (h2.trans h1).trans (neg_le_abs _)
      have hLpos : 0 < 1 / (4 * x) := by positivity
      calc y ^ (2 : ℝ) / (π * T * |Real.log y|) ≤ y ^ (2 : ℝ) / (1 / (4 * x)) / (π * T) :=
            hdiv _ hLpos hlogb
        _ ≤ (3 * (x ^ 2 * (n : ℝ) ^ (-2 : ℝ)) + ind n) / (π * T) := by
            apply div_le_div_of_nonneg_right _ hπT.le
            rw [hindn, div_div_eq_mul_div, div_one]
            have hyy : y ^ (2 : ℝ) ≤ 4 := by
              rw [show y ^ (2 : ℝ) = y ^ 2 by norm_cast]; nlinarith
            have : 0 ≤ 3 * (x ^ 2 * (n : ℝ) ^ (-2 : ℝ)) :=
              mul_nonneg (by norm_num) (mul_nonneg (by positivity) (Real.rpow_nonneg hnr.le _))
            have := mul_le_mul_of_nonneg_right hyy (by positivity : (0 : ℝ) ≤ 4 * x)
            linarith
  -- summation
  have hp2 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hS2 : ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) ≤ 2 := by
    have h := tsum_nat_rpow_neg_le (p := 2) (by norm_num)
    norm_num at h ⊢; exact h
  have hind_sum : HasSum ind (∑ n ∈ Finset.range (2 * N + 1), ind n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [hind]; rw [ite_eq_right (by omega)])
  have hind_val : ∑ n ∈ Finset.range (2 * N + 1), ind n = (2 * N + 1) * (16 * x) := by
    rw [Finset.sum_congr rfl (fun n hn => by
      simp only [Finset.mem_range] at hn; simp only [hind]; rw [ite_eq_left hn])]
    simp
  have hgsum : HasSum g ((3 * (x ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) +
      (2 * N + 1) * (16 * x)) / (π * T)) := by
    rw [← hind_val]
    exact (((hp2.hasSum.mul_left (x ^ 2)).mul_left 3).add hind_sum).div_const _
  have hesum : Summable e := Summable.of_nonneg_of_le he0 hle hgsum.summable
  calc ∑' n, e n ≤ ∑' n, g n := hesum.tsum_le_tsum hle hgsum.summable
    _ = (3 * (x ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) + (2 * N + 1) * (16 * x)) / (π * T) :=
        hgsum.tsum_eq
    _ ≤ (6 * x ^ 2 + 16 * x * (2 * N + 1)) / (π * T) := by
        apply div_le_div_of_nonneg_right _ hπT.le
        nlinarith [sq_nonneg x]

/-! ## Item 7: assembly -/

/-- Mertens-type bound (as in `Trombo_Mertens.lean`, with `TromboPerron.mertensM`, which is
the same function `x ↦ ∑_{1 ≤ n ≤ ⌊x⌋} μ(n)`): for every `ε > 0` there is `C` with
`|M(x)| ≤ C · x^(1/2+ε)` for all real `x ≥ 1`. -/
def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |(TromboPerron.mertensM x : ℝ)| ≤ C * x ^ ((1 : ℝ) / 2 + ε)

/-- `N + 1/2` is never a natural number. -/
lemma half_off (N : ℕ) : ∀ n : ℕ, (N : ℝ) + 1 / 2 ≠ n := by
  intro n h
  have h2 : ((2 * N + 1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; linarith
  have h3 : 2 * N + 1 = 2 * n := by exact_mod_cast h2
  omega

/-- `x^a ≤ x^p` for `x ≥ 1`, `a ≤ p`. -/
lemma rpow_le_of_le {x a p : ℝ} (hx : 1 ≤ x) (hap : a ≤ p) : x ^ a ≤ x ^ p :=
  Real.rpow_le_rpow_of_exponent_le hx hap

/-- **Key estimate at half-integers.** Under RH, for every `ε > 0` there is `K` with
`|M(N + 1/2)| ≤ K (N + 1/2)^(1/2+ε)` for all natural `N ≥ 1`. -/
theorem RH_mertens_half (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(TromboPerron.mertensM ((N : ℝ) + 1 / 2) : ℝ)| ≤
        K * ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε) := by
  set η := min (ε / 4) 1 with hηdef
  have hη : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε / 4 := min_le_left _ _
  set e := ε / 16 with hedef
  have he : 0 < e := by positivity
  obtain ⟨C, hC0, hC⟩ := RH_invZeta_bound hRH hη hη1 he
  set σ₀ := 1 / 2 + η with hσ₀def
  set p := (1 : ℝ) / 2 + ε with hpdef
  refine ⟨8 * C / e * (4 : ℝ) ^ (2 * e) + 4 * C * (4 : ℝ) ^ e + 13, fun N hN => ?_⟩
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 3 / 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set T : ℝ := x ^ (2 : ℝ) with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow (by linarith) (by norm_num)
  have hT0 : 0 < T := by linarith
  have hTsq : T = x ^ 2 := by rw [hTdef]; norm_cast
  -- Perron (item 1) and its error (c = 2)
  have hP := TromboPerron.mertensM_perron (x := x) (c := 2) (T := T) hx0 (by norm_num) hT0
    (half_off N)
  have hE := perron_error_le hN hT0
  rw [← hxdef] at hE
  -- the Perron integral with `invZeta`
  have hRconv : (∫ t in -T..T, (riemannZeta (((2 : ℝ) : ℂ) + t * I))⁻¹ *
      TauCeti.perronIntegrand x 2 t) =
      ∫ t in -T..T, invZeta (((2 : ℝ) : ℂ) + t * I) * TauCeti.perronIntegrand x 2 t := by
    congr 1; funext t
    rw [invZeta_of_ne]
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [hRconv] at hP
  set R := ∫ t in -T..T, invZeta (((2 : ℝ) : ℂ) + t * I) * TauCeti.perronIntegrand x 2 t with hR
  set Lf := ∫ t in -T..T, invZeta ((σ₀ : ℂ) + t * I) * TauCeti.perronIntegrand x σ₀ t with hL
  set Ht := ∫ σ in σ₀..2, perronF x ((σ : ℂ) + T * I) with hHt
  set Hb := ∫ σ in σ₀..2, perronF x ((σ : ℂ) + (-T : ℝ) * I) with hHb
  -- contour shift (item 6)
  have hshift := RH_contour_shift hRH (x := x) (σ₀ := σ₀) (T := T) hx0 (by linarith)
    (by linarith)
  rw [← hR, ← hL, ← hHt, ← hHb] at hshift
  have hRL : ‖R‖ ≤ ‖Lf‖ + ‖Ht‖ + ‖Hb‖ := by
    have h1 : ‖R - Lf‖ = ‖Ht - Hb‖ := by
      rw [← hshift, norm_smul, Complex.norm_I, one_mul]
    have h2 := norm_sub_le Ht Hb
    have h3 : ‖R‖ ≤ ‖R - Lf‖ + ‖Lf‖ := by
      calc ‖R‖ = ‖(R - Lf) + Lf‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  -- the three contour pieces
  have hbound : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 → ‖invZeta s‖ ≤ C * (3 + |s.im|) ^ e :=
    fun s h1 h2 => hC s h1 h2
  have hLb := norm_left_integral_le (x := x) (σ₀ := σ₀) (T := T) (C := C) (ε := e)
    (by linarith) (by linarith) hT0.le hC0 he.le
    (fun t _ => by simpa using hbound ((σ₀ : ℂ) + t * I) (by simp) (by simp; linarith))
  have hHtb := norm_horizontal_integral_le (x := x) (σ₀ := σ₀) (y := T) (C := C) (ε := e)
    (by linarith) (by linarith) (by rw [abs_of_pos hT0]; exact hT0) hC0
    (fun σ h1 h2 => by simpa using hbound ((σ : ℂ) + T * I) (by simpa using h1) (by simpa using h2))
  have hHbb := norm_horizontal_integral_le (x := x) (σ₀ := σ₀) (y := -T) (C := C) (ε := e)
    (by linarith) (by linarith) (by rw [abs_neg, abs_of_pos hT0]; exact hT0) hC0
    (fun σ h1 h2 => by
      simpa using hbound ((σ : ℂ) + (-T : ℝ) * I) (by simpa using h1) (by simpa using h2))
  rw [← hL] at hLb
  rw [← hHt] at hHtb
  rw [← hHb] at hHbb
  rw [abs_neg, abs_of_pos hT0] at hHbb
  rw [abs_of_pos hT0] at hHtb
  -- numerical simplification
  have h4T : 3 + T ≤ 4 * T := by linarith
  have h4T1 : 1 + T ≤ 4 * T := by linarith
  have hY1 : 1 ≤ 4 * T := by linarith
  have hYe : (3 + T) ^ e ≤ (4 * T) ^ e := Real.rpow_le_rpow (by linarith) h4T he.le
  have hlog : Real.log (1 + T) ≤ (4 * T) ^ e / e :=
    (Real.log_le_log (by linarith) h4T1).trans (Real.log_le_rpow_div (by linarith) he)
  have hY0 : 0 ≤ (4 * T) ^ e := Real.rpow_nonneg (by linarith) _
  have hxs : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx0.le _
  have hxT : x ^ (2 : ℝ) / T = 1 := by rw [hTdef, div_self (by positivity)]
  have h2σ : |2 - σ₀| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hLb' : ‖Lf‖ ≤ 8 * C / e * (x ^ σ₀ * ((4 * T) ^ e) ^ 2) := by
    have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    have hc1 : 0 ≤ 8 * C * x ^ σ₀ := mul_nonneg (mul_nonneg (by norm_num) hC0) hxs
    calc ‖Lf‖ ≤ 8 * C * x ^ σ₀ * (3 + T) ^ e * Real.log (1 + T) := hLb
      _ ≤ 8 * C * x ^ σ₀ * (4 * T) ^ e * ((4 * T) ^ e / e) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hYe hc1) hlog hlog0 (mul_nonneg hc1 hY0)
      _ = 8 * C / e * (x ^ σ₀ * ((4 * T) ^ e) ^ 2) := by ring
  have hHtb' : ‖Ht‖ ≤ 2 * C * (4 * T) ^ e := by
    calc ‖Ht‖ ≤ C * (3 + T) ^ e * x ^ (2 : ℝ) / T * |2 - σ₀| := hHtb
      _ = C * (3 + T) ^ e * (x ^ (2 : ℝ) / T) * |2 - σ₀| := by ring
      _ ≤ C * (4 * T) ^ e * 1 * 2 := by rw [hxT]; gcongr
      _ = 2 * C * (4 * T) ^ e := by ring
  have hHbb' : ‖Hb‖ ≤ 2 * C * (4 * T) ^ e := by
    calc ‖Hb‖ ≤ C * (3 + T) ^ e * x ^ (2 : ℝ) / T * |2 - σ₀| := hHbb
      _ = C * (3 + T) ^ e * (x ^ (2 : ℝ) / T) * |2 - σ₀| := by ring
      _ ≤ C * (4 * T) ^ e * 1 * 2 := by rw [hxT]; gcongr
      _ = 2 * C * (4 * T) ^ e := by ring
  have hE' : (6 * x ^ 2 + 16 * x * (2 * N + 1)) / (π * T) ≤ 13 := by
    have h2N : (2 * N + 1 : ℝ) = 2 * x := by rw [hxdef]; ring
    rw [h2N, ← hTsq, div_le_iff₀ (mul_pos Real.pi_pos hT0)]
    have : 16 * x * (2 * x) = 32 * T := by rw [hTsq]; ring
    rw [this]
    have := mul_lt_mul_of_pos_right Real.pi_gt_three hT0
    linarith
  -- powers of `x`
  have h4Te : (4 * T) ^ e = (4 : ℝ) ^ e * x ^ (2 * e) := by
    rw [Real.mul_rpow (by norm_num) hT0.le, hTdef, ← Real.rpow_mul hx0.le]
  have hpow1 : x ^ σ₀ * ((4 * T) ^ e) ^ 2 = (4 : ℝ) ^ (2 * e) * x ^ (σ₀ + 4 * e) := by
    have r1 : ((4 : ℝ) ^ e) ^ 2 = (4 : ℝ) ^ (2 * e) := by
      rw [← Real.rpow_natCast ((4 : ℝ) ^ e) 2, ← Real.rpow_mul (by norm_num)]
      push_cast; ring_nf
    have r2 : (x ^ (2 * e)) ^ 2 = x ^ (4 * e) := by
      rw [← Real.rpow_natCast (x ^ (2 * e)) 2, ← Real.rpow_mul hx0.le]
      push_cast; ring_nf
    rw [h4Te, mul_pow, r1, r2, Real.rpow_add hx0 σ₀ (4 * e)]
    ring
  have hxp1 : x ^ (σ₀ + 4 * e) ≤ x ^ p := rpow_le_of_le (by linarith) (by
    rw [hσ₀def, hpdef, hedef]; linarith)
  have hxp2 : x ^ (2 * e) ≤ x ^ p := rpow_le_of_le (by linarith) (by
    rw [hpdef, hedef]; linarith)
  have hxp3 : 1 ≤ x ^ p := Real.one_le_rpow (by linarith) (by rw [hpdef]; linarith)
  have h4e : 0 ≤ (4 : ℝ) ^ e := Real.rpow_nonneg (by norm_num) _
  have h4e2 : 0 ≤ (4 : ℝ) ^ (2 * e) := Real.rpow_nonneg (by norm_num) _
  have hCe : 0 ≤ 8 * C / e := by positivity
  -- combine
  have hMnorm : |(TromboPerron.mertensM x : ℝ)| = ‖((TromboPerron.mertensM x : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
  have hpi : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hpi0 : 0 ≤ (2 * π)⁻¹ := by positivity
  have hnormP : ‖(((2 * π : ℝ) : ℂ)⁻¹ * R)‖ = (2 * π)⁻¹ * ‖R‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hM1 : ‖((TromboPerron.mertensM x : ℤ) : ℂ)‖ ≤
      ‖(((2 * π : ℝ) : ℂ)⁻¹ * R)‖ + ‖(((2 * π : ℝ) : ℂ)⁻¹ * R) - ((TromboPerron.mertensM x : ℤ) : ℂ)‖ := by
    calc ‖((TromboPerron.mertensM x : ℤ) : ℂ)‖
        = ‖(((2 * π : ℝ) : ℂ)⁻¹ * R) - ((((2 * π : ℝ) : ℂ)⁻¹ * R) -
            ((TromboPerron.mertensM x : ℤ) : ℂ))‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have hRsum : ‖R‖ ≤ 8 * C / e * ((4 : ℝ) ^ (2 * e) * x ^ p) + 4 * C * ((4 : ℝ) ^ e * x ^ p) := by
    have a1 : 8 * C / e * (x ^ σ₀ * ((4 * T) ^ e) ^ 2) ≤ 8 * C / e * ((4 : ℝ) ^ (2 * e) * x ^ p) := by
      rw [hpow1]; gcongr
    have a2 : 2 * C * (4 * T) ^ e ≤ 2 * C * ((4 : ℝ) ^ e * x ^ p) := by
      rw [h4Te]; gcongr
    linarith
  rw [hMnorm]
  calc ‖((TromboPerron.mertensM x : ℤ) : ℂ)‖
      ≤ (2 * π)⁻¹ * ‖R‖ + 13 := by
        rw [hnormP] at hM1; linarith
    _ ≤ 1 * ‖R‖ + 13 := by gcongr
    _ ≤ (8 * C / e * (4 : ℝ) ^ (2 * e) + 4 * C * (4 : ℝ) ^ e) * x ^ p + 13 * x ^ p := by
        have e1 : 8 * C / e * ((4 : ℝ) ^ (2 * e) * x ^ p) + 4 * C * ((4 : ℝ) ^ e * x ^ p) =
            (8 * C / e * (4 : ℝ) ^ (2 * e) + 4 * C * (4 : ℝ) ^ e) * x ^ p := by ring
        linarith
    _ = _ := by ring

/-- **Item 7 (main theorem).** `RiemannHypothesis → MertensBound`: under RH, for every `ε > 0`
there is `C` with `|M(x)| ≤ C x^(1/2+ε)` for all real `x ≥ 1`. -/
theorem RH_imp_mertensBound : RiemannHypothesis → MertensBound := by
  intro hRH ε hε
  obtain ⟨K, hK⟩ := RH_mertens_half hRH hε
  set p := (1 : ℝ) / 2 + ε with hpdef
  have hp : 0 ≤ p := by rw [hpdef]; linarith
  refine ⟨max K 0 * (2 : ℝ) ^ p, fun x hx => ?_⟩
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hfloor : ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  have hMeq : TromboPerron.mertensM x = TromboPerron.mertensM ((N : ℝ) + 1 / 2) := by
    unfold TromboPerron.mertensM
    rw [hfloor]
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx' : (N : ℝ) + 1 / 2 ≤ 2 * x := by linarith
  have hpos : 0 < (N : ℝ) + 1 / 2 := by positivity
  have h1 := hK N hN
  have h2 : ((N : ℝ) + 1 / 2) ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow hpos.le hx' hp
  have h3 : (2 * x) ^ p = (2 : ℝ) ^ p * x ^ p := Real.mul_rpow (by norm_num) (by linarith)
  have h4 : 0 ≤ ((N : ℝ) + 1 / 2) ^ p := Real.rpow_nonneg hpos.le _
  rw [hMeq]
  calc |(TromboPerron.mertensM ((N : ℝ) + 1 / 2) : ℝ)| ≤ K * ((N : ℝ) + 1 / 2) ^ p := h1
    _ ≤ max K 0 * ((N : ℝ) + 1 / 2) ^ p := mul_le_mul_of_nonneg_right (le_max_left _ _) h4
    _ ≤ max K 0 * ((2 : ℝ) ^ p * x ^ p) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max K 0 * (2 : ℝ) ^ p * x ^ p := by ring

end TromboRHMertens

#print axioms TromboRHMertens.invZeta_of_ne
#print axioms TromboRHMertens.RH_Z_ne_zero
#print axioms TromboRHMertens.RH_invZeta_differentiableAt
#print axioms TromboRHMertens.perronF_vertical
#print axioms TromboRHMertens.RH_contour_shift
#print axioms TromboRHMertens.RH_invZeta_bound
#print axioms TromboRHMertens.integral_inv_one_add_abs
#print axioms TromboRHMertens.norm_left_integral_le
#print axioms TromboRHMertens.norm_horizontal_integral_le
#print axioms TromboRHMertens.perron_error_le
#print axioms TromboRHMertens.half_off
#print axioms TromboRHMertens.rpow_le_of_le
#print axioms TromboRHMertens.RH_mertens_half
#print axioms TromboRHMertens.RH_imp_mertensBound

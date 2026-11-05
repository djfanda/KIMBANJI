import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trombo certificate, rung 4: `L(1, χ₋₃) = π / (3√3)`

Main theorem `Trombo.tendsto_L_one_chi3`: the partial sums `∑_{n<N} χ(n+1)/(n+1)` converge to
`π / (3√3)`. `chi3` is the same definition as in `Trombo_Chi3Sine.lean` (repeated here so the
file is self-contained). The series is written directly with `chi3`; it is not linked here to
Mathlib's `DirichletCharacter.LFunction`.

Ingredients from Mathlib: Dirichlet's test
(`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`), the complex logarithm series
(`Complex.hasSum_taylorSeries_neg_log'`), Abel's limit theorem
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`), continuity of `Complex.log` on the slit plane
and `Complex.log_exp`.
-/

open Real Filter Topology Finset

/-- The character modulo 3: `0` if `3 ∣ n`, `1` if `n ≡ 1 (mod 3)`, `-1` if `n ≡ 2 (mod 3)`. -/
def chi3 (n : ℤ) : ℤ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

namespace Trombo

/-- `ω = -1/2 + (√3/2) i`. -/
noncomputable def ω : ℂ := ⟨-1/2, √3/2⟩
/-- `ω' = -1/2 - (√3/2) i` (the conjugate of `ω`). -/
noncomputable def ω' : ℂ := ⟨-1/2, -(√3/2)⟩

lemma s3 : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)

lemma ω_mul_ω' : ω * ω' = 1 := by
  apply Complex.ext <;> simp [ω, ω'] <;> nlinarith [s3]

lemma ω_sq : ω * ω = ω' := by
  apply Complex.ext <;> simp [ω, ω'] <;> nlinarith [s3]

lemma ω'_sq : ω' * ω' = ω := by
  apply Complex.ext <;> simp [ω, ω'] <;> nlinarith [s3]

lemma ω_cube : ω ^ 3 = 1 := by
  rw [pow_succ, pow_two, ω_sq, mul_comm, ω_mul_ω']

lemma ω'_cube : ω' ^ 3 = 1 := by
  rw [pow_succ, pow_two, ω'_sq, ω_mul_ω']

lemma chi3_nat (m : ℕ) : chi3 (m : ℤ) =
    if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 := by
  unfold chi3
  have h : ((m : ℤ) % 3) = ((m % 3 : ℕ) : ℤ) := by push_cast; rfl
  rw [h]
  have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 3) <;> simp

/-- `ω^m - ω'^m = i·√3·χ(m)`. -/
lemma pow_sub_pow (m : ℕ) : ω ^ m - ω' ^ m = (Complex.I * (√3 : ℝ)) * (chi3 (m : ℤ) : ℂ) := by
  have hm : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod m 3).symm
  have h1 : ω ^ m = ω ^ (m % 3) := by
    conv_lhs => rw [hm]
    rw [pow_add, pow_mul, ω_cube, one_pow, one_mul]
  have h2 : ω' ^ m = ω' ^ (m % 3) := by
    conv_lhs => rw [hm]
    rw [pow_add, pow_mul, ω'_cube, one_pow, one_mul]
  rw [h1, h2, chi3_nat]
  have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 3)
  · simp
  · apply Complex.ext <;> simp [ω, ω']
  · rw [pow_two, pow_two, ω_sq, ω'_sq]
    apply Complex.ext <;> simp [ω, ω']
    ring

/-- The coefficient sequence `a n = χ(n+1)/(n+1)`. -/
noncomputable def a (n : ℕ) : ℝ := (chi3 ((n : ℤ) + 1) : ℝ) / ((n : ℝ) + 1)

/-- Partial sums of `χ(1), χ(2), …` are `1` or `0`. -/
lemma partial_chi3 (n : ℕ) :
    ∑ i ∈ range n, (chi3 ((i : ℤ) + 1) : ℝ) = if n % 3 = 1 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hc : chi3 ((n : ℤ) + 1) = chi3 ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hc, chi3_nat]
    have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
    · have h' : (n + 1) % 3 = 1 := by omega
      simp [h, h']
    · have h' : (n + 1) % 3 = 2 := by omega
      simp [h, h']
    · have h' : (n + 1) % 3 = 0 := by omega
      simp [h, h']

/-- The partial sums of `∑ a n` converge (Dirichlet's test). -/
lemma exists_limit : ∃ l : ℝ, Tendsto (fun N ↦ ∑ n ∈ range N, a n) atTop (𝓝 l) := by
  have hanti : Antitone (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) := by
    intro x y hxy
    have : (x : ℝ) ≤ y := by exact_mod_cast hxy
    simp only
    gcongr
  have hb : ∀ n, ‖∑ i ∈ range n, (chi3 ((i : ℤ) + 1) : ℝ)‖ ≤ 1 := by
    intro n
    rw [partial_chi3]
    split_ifs <;> simp
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_one_div_add_atTop_nhds_zero_nat hb
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨l, ?_⟩
  convert hl using 2 with N
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [a, smul_eq_mul]
  ring

lemma norm_ω : ‖ω‖ = 1 := by
  have h : ‖ω‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [ω]; nlinarith [s3]
  have := norm_nonneg ω
  nlinarith

lemma norm_ω' : ‖ω'‖ = 1 := by
  have h : ‖ω'‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [ω']; nlinarith [s3]
  have := norm_nonneg ω'
  nlinarith

/-- `V x = (log(1 - ω' x) - log(1 - ω x)) / (i√3)`. -/
noncomputable def V (x : ℝ) : ℂ :=
  (Complex.log (1 - ω' * x) - Complex.log (1 - ω * x)) / (Complex.I * (√3 : ℝ))

/-- For `0 < x < 1`: `∑ a n xⁿ = Re (V x / x)`. -/
lemma hasSum_series {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n ↦ a n * x ^ n) ((V x / x).re) := by
  have hn1 : ‖ω * (x : ℂ)‖ < 1 := by
    rw [norm_mul, norm_ω, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
  have hn2 : ‖ω' * (x : ℂ)‖ < 1 := by
    rw [norm_mul, norm_ω', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
  have h1 := Complex.hasSum_taylorSeries_neg_log' hn1
  have h2 := Complex.hasSum_taylorSeries_neg_log' hn2
  have h3 := (h1.sub h2).div_const (Complex.I * (√3 : ℝ) * x)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hs : ((√3 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  have hx : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hfun : (fun n : ℕ ↦ ((ω * x) ^ (n + 1) / (n + 1) - (ω' * x) ^ (n + 1) / (n + 1)) /
      (Complex.I * (√3 : ℝ) * x)) = fun n ↦ ((a n * x ^ n : ℝ) : ℂ) := by
    funext n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have e : (ω * x) ^ (n + 1) / (n + 1) - (ω' * x) ^ (n + 1) / (n + 1) =
        (ω ^ (n + 1) - ω' ^ (n + 1)) * (x : ℂ) ^ (n + 1) / (n + 1) := by ring
    rw [e, pow_sub_pow]
    simp only [a]
    push_cast
    field_simp
    ring
  rw [hfun] at h3
  have h4 := Complex.hasSum_re h3
  simp only [Complex.ofReal_re] at h4
  convert h4 using 2
  simp only [V]
  field_simp
  ring

lemma one_sub_ω' : 1 - ω' = Complex.exp (((Real.log √3 : ℝ) : ℂ) + ((π / 6 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (Real.sqrt_pos.mpr (by norm_num)),
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  apply Complex.ext <;> simp [ω'] <;> nlinarith [s3]

lemma one_sub_ω : 1 - ω = Complex.exp (((Real.log √3 : ℝ) : ℂ) + ((-(π / 6) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (Real.sqrt_pos.mpr (by norm_num)),
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  apply Complex.ext <;> simp [ω] <;> nlinarith [s3]

lemma log_one_sub_ω' : Complex.log (1 - ω') = ((Real.log √3 : ℝ) : ℂ) + ((π / 6 : ℝ) : ℂ) * Complex.I := by
  rw [one_sub_ω', Complex.log_exp] <;> simp <;> linarith [Real.pi_pos]

lemma log_one_sub_ω : Complex.log (1 - ω) = ((Real.log √3 : ℝ) : ℂ) + ((-(π / 6) : ℝ) : ℂ) * Complex.I := by
  rw [one_sub_ω, Complex.log_exp] <;> simp <;> linarith [Real.pi_pos]

lemma V_one : (V 1 / ((1 : ℝ) : ℂ)).re = π / (3 * √3) := by
  have hs : ((√3 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  have : V 1 / ((1 : ℝ) : ℂ) = ((π / (3 * √3) : ℝ) : ℂ) := by
    simp only [V, Complex.ofReal_one, mul_one, div_one, log_one_sub_ω', log_one_sub_ω]
    field_simp
    push_cast
    ring_nf
    field_simp
  rw [this, Complex.ofReal_re]

lemma continuousAt_V : ContinuousAt (fun x : ℝ ↦ (V x / x).re) 1 := by
  have hω : 1 - ω * ((1 : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp [ω]; norm_num
  have hω' : 1 - ω' * ((1 : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp [ω']; norm_num
  have c1 : ContinuousAt (fun x : ℝ ↦ Complex.log (1 - ω * x)) 1 :=
    ContinuousAt.comp (f := fun x : ℝ ↦ 1 - ω * (x : ℂ)) (continuousAt_clog hω) (by fun_prop)
  have c2 : ContinuousAt (fun x : ℝ ↦ Complex.log (1 - ω' * x)) 1 :=
    ContinuousAt.comp (f := fun x : ℝ ↦ 1 - ω' * (x : ℂ)) (continuousAt_clog hω') (by fun_prop)
  have c3 : ContinuousAt (fun x : ℝ ↦ V x / x) 1 := by
    simp only [V]
    refine ((c2.sub c1).div_const _).div (by fun_prop) (by simp)
  exact Complex.continuous_re.continuousAt.comp c3

/-- **`L(1, χ₋₃) = π / (3√3)`**, in partial-sum form: the partial sums
`∑_{n < N} χ(n+1)/(n+1)` tend to `π / (3√3)` as `N → ∞`.
(Stated with `Filter.Tendsto` of partial sums, as in Mathlib's `Real.tendsto_sum_pi_div_four`,
because the series converges only conditionally; `HasSum` would require unconditional
convergence. That `HasSum` fails is not proved here.)
Proof: Dirichlet's test gives convergence to some `l`; for `0 < x < 1` the power series equals
`Re((log(1-ω̄x) - log(1-ωx)) / (i√3 x))` via the complex log series; Abel's limit theorem and
continuity at `x = 1` identify `l` with `(π/6 - (-π/6)) / √3 = π/(3√3)`. -/
theorem tendsto_L_one_chi3 :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, (chi3 ((n : ℤ) + 1) : ℝ) / ((n : ℝ) + 1)) atTop
      (𝓝 (π / (3 * Real.sqrt 3))) := by
  obtain ⟨l, hl⟩ := exists_limit
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hev : (fun x : ℝ ↦ ∑' n, a n * x ^ n) =ᶠ[𝓝[<] 1] (fun x ↦ (V x / x).re) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hasSum_series hx.1 hx.2).tsum_eq
  have h1 : Tendsto (fun x : ℝ ↦ (V x / x).re) (𝓝[<] 1) (𝓝 l) := habel.congr' hev
  have h2 : Tendsto (fun x : ℝ ↦ (V x / x).re) (𝓝[<] 1) (𝓝 (π / (3 * √3))) := by
    rw [← V_one]
    exact continuousAt_V.tendsto.mono_left nhdsWithin_le_nhds
  have hl' : l = π / (3 * √3) := tendsto_nhds_unique h1 h2
  rw [← hl']
  exact hl

end Trombo

#print axioms Trombo.s3
#print axioms Trombo.ω_mul_ω'
#print axioms Trombo.ω_sq
#print axioms Trombo.ω'_sq
#print axioms Trombo.ω_cube
#print axioms Trombo.ω'_cube
#print axioms Trombo.chi3_nat
#print axioms Trombo.pow_sub_pow
#print axioms Trombo.partial_chi3
#print axioms Trombo.exists_limit
#print axioms Trombo.norm_ω
#print axioms Trombo.norm_ω'
#print axioms Trombo.hasSum_series
#print axioms Trombo.one_sub_ω'
#print axioms Trombo.one_sub_ω
#print axioms Trombo.log_one_sub_ω'
#print axioms Trombo.log_one_sub_ω
#print axioms Trombo.V_one
#print axioms Trombo.continuousAt_V
#print axioms Trombo.tendsto_L_one_chi3

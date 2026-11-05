import Mathlib

/-!
# Kimbanji_Needle : Leibniz partial sums, error bound, and the Buffon integral

Mathlib check (grep, Mathlib b63f6e8):
* `Real.tendsto_sum_pi_div_four`  (Mathlib/Analysis/Real/Pi/Leibniz.lean) : EXISTS (quoted below).
* `Antitone.tendsto_alternating_series_of_tendsto_zero` : EXISTS, but gives only convergence,
  no error bound; so the bound `|S_N - pi/4| <= 1/(2N+1)` is proved here by hand.
* Buffon's needle theorem (any name containing "Buffon"): NOT in Mathlib.
  The measure-theoretic statement "P(hit) = 2l/(pi d)" is NOT proved in this file.
  What is proved: the integral `(1/pi) * int_0^pi (l/d) sin = 2l/(pi d)`, i.e. the
  evaluation step that follows once the hit-probability at angle theta is modelled as (l/d) sin theta.
-/

open Finset Filter Topology
open scoped Real

namespace KimbanjiNeedle

/-- Leibniz partial sum `S_N = sum_{k<N} (-1)^k/(2k+1)`. -/
noncomputable def S (N : ℕ) : ℝ := ∑ i ∈ range N, (-1 : ℝ) ^ i / (2 * i + 1)

/-- Quoted from Mathlib: `S_N -> pi/4`. -/
theorem S_tendsto : Tendsto S atTop (𝓝 (π / 4)) := Real.tendsto_sum_pi_div_four

theorem S_succ (n : ℕ) : S (n + 1) = S n + (-1 : ℝ) ^ n / (2 * n + 1) := by
  unfold S; rw [sum_range_succ]

theorem S_two_step_even {m : ℕ} (h : Even m) : S m ≤ S (m + 2) := by
  have h1 : S (m + 2) = S m + (-1 : ℝ) ^ m / (2 * m + 1)
      + (-1 : ℝ) ^ (m + 1) / (2 * ((m + 1 : ℕ) : ℝ) + 1) := by
    rw [S_succ (m + 1), S_succ m]
  rw [h1, h.neg_one_pow, (h.add_one).neg_one_pow]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (1 : ℝ) / (2 * ((m : ℝ) + 1) + 1) ≤ 1 / (2 * m + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e : (-1 : ℝ) / (2 * ((m : ℝ) + 1) + 1) = -(1 / (2 * ((m : ℝ) + 1) + 1)) := by ring
  rw [e]
  linarith

theorem S_two_step_odd {m : ℕ} (h : Odd m) : S (m + 2) ≤ S m := by
  have h1 : S (m + 2) = S m + (-1 : ℝ) ^ m / (2 * m + 1)
      + (-1 : ℝ) ^ (m + 1) / (2 * ((m + 1 : ℕ) : ℝ) + 1) := by
    rw [S_succ (m + 1), S_succ m]
  rw [h1, h.neg_one_pow, (h.add_one).neg_one_pow]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (1 : ℝ) / (2 * ((m : ℝ) + 1) + 1) ≤ 1 / (2 * m + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : (-1 : ℝ) / (2 * (m : ℝ) + 1) = -(1 / (2 * (m : ℝ) + 1)) := by ring
  rw [e2]
  linarith

/-- even-index partial sums lie below the limit. -/
theorem S_le_limit_of_even {n : ℕ} (hn : Even n) : S n ≤ π / 4 := by
  have key : ∀ j : ℕ, S n ≤ S (n + 2 * j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have he : Even (n + 2 * j) := hn.add (even_two_mul j)
      have := S_two_step_even he
      have e : n + 2 * (j + 1) = n + 2 * j + 2 := by ring
      rw [e]; exact ih.trans this
  have ht : Tendsto (fun j : ℕ => S (n + 2 * j)) atTop (𝓝 (π / 4)) := by
    refine S_tendsto.comp ?_
    exact tendsto_atTop_mono (fun j => (by omega : j ≤ n + 2 * j)) tendsto_id
  exact ge_of_tendsto' ht key

theorem limit_le_S_of_odd {n : ℕ} (hn : Odd n) : π / 4 ≤ S n := by
  have key : ∀ j : ℕ, S (n + 2 * j) ≤ S n := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have ho : Odd (n + 2 * j) := hn.add_even (even_two_mul j)
      have := S_two_step_odd ho
      have e : n + 2 * (j + 1) = n + 2 * j + 2 := by ring
      rw [e]; exact this.trans ih
  have ht : Tendsto (fun j : ℕ => S (n + 2 * j)) atTop (𝓝 (π / 4)) := by
    refine S_tendsto.comp ?_
    exact tendsto_atTop_mono (fun j => (by omega : j ≤ n + 2 * j)) tendsto_id
  exact le_of_tendsto' ht key

/-- **Error bound** `|S_N - pi/4| <= 1/(2N+1)` (proved here; Mathlib has only convergence). -/
theorem S_error_le (N : ℕ) : |S N - π / 4| ≤ 1 / (2 * (N : ℝ) + 1) := by
  have hs : S (N + 1) = S N + (-1 : ℝ) ^ N / (2 * N + 1) := S_succ N
  have hpos : (0 : ℝ) < 2 * N + 1 := by positivity
  rcases Nat.even_or_odd N with he | ho
  · have h1 := S_le_limit_of_even he
    have h2 : π / 4 ≤ S (N + 1) := limit_le_S_of_odd (he.add_one)
    rw [he.neg_one_pow] at hs
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := limit_le_S_of_odd ho
    have h2 : S (N + 1) ≤ π / 4 := S_le_limit_of_even (ho.add_one)
    rw [ho.neg_one_pow] at hs
    rw [abs_of_nonneg (by linarith)]
    have : -1 / (2 * (N : ℝ) + 1) = -(1 / (2 * (N : ℝ) + 1)) := by ring
    linarith

/-- Euler-type average of two consecutive partial sums: error at most half the step. -/
theorem S_avg_error_le (N : ℕ) :
    |(S N + S (N + 1)) / 2 - π / 4| ≤ 1 / (2 * (2 * (N : ℝ) + 1)) := by
  have h := S_error_le N
  have h' := S_error_le (N + 1)
  have hs := S_succ N
  have hpos : (0 : ℝ) < 2 * N + 1 := by positivity
  rcases Nat.even_or_odd N with he | ho
  · have h1 := S_le_limit_of_even he
    have h2 : π / 4 ≤ S (N + 1) := limit_le_S_of_odd he.add_one
    rw [he.neg_one_pow] at hs
    rw [abs_le]; constructor <;> (field_simp at hs ⊢; nlinarith [hs])
  · have h1 := limit_le_S_of_odd ho
    have h2 : S (N + 1) ≤ π / 4 := S_le_limit_of_even ho.add_one
    rw [ho.neg_one_pow] at hs
    rw [abs_le]; constructor <;> (field_simp at hs ⊢; nlinarith [hs])

/-! ### Buffon integral -/

/-- `int_0^pi sin = 2`. -/
theorem integral_sin_zero_pi : ∫ x in (0 : ℝ)..π, Real.sin x = 2 := by
  rw [integral_sin]; norm_num

/-- Evaluation step of Buffon (needle length `l`, line spacing `d > 0`):
`(1/pi) * int_0^pi (l/d) sin theta dtheta = 2 l / (pi d)`.
The modelling assumption "hit probability at angle theta equals (l/d) sin theta (l <= d)"
is NOT proved here. -/
theorem buffon_integral (l d : ℝ) :
    (1 / π) * ∫ θ in (0 : ℝ)..π, (l / d) * Real.sin θ = 2 * l / (π * d) := by
  rw [intervalIntegral.integral_const_mul, integral_sin_zero_pi]
  have := Real.pi_pos
  by_cases hd : d = 0
  · simp [hd]
  · field_simp

end KimbanjiNeedle

#print axioms KimbanjiNeedle.S_error_le
#print axioms KimbanjiNeedle.S_avg_error_le
#print axioms KimbanjiNeedle.integral_sin_zero_pi
#print axioms KimbanjiNeedle.buffon_integral

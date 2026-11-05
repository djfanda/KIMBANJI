import Mathlib

/-!
# 황금비 φ 와 π  (Trombo / Kimbanji, 2026-11-04)
순수 수학. 이 파일은 밀레니엄 문제와 무관하다.
-/

open Real Filter Topology

namespace KimbanjiPhiPi

noncomputable abbrev phi : ℝ := Real.goldenRatio

lemma phi_def : phi = (1 + √5) / 2 := rfl

lemma phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

lemma phi_pos : 0 < phi := Real.goldenRatio_pos

lemma sqrt5_sq : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-! ## 1. φ = 2cos(π/5),  1/φ = 2 sin(π/10) = φ - 1 -/

theorem phi_eq_two_cos : phi = 2 * Real.cos (π / 5) := by
  rw [Real.cos_pi_div_five, phi_def]; ring

theorem inv_phi_eq_phi_sub_one : phi⁻¹ = phi - 1 := by
  have h : phi * (phi - 1) = 1 := by nlinarith [phi_sq]
  exact inv_eq_of_mul_eq_one_right h

theorem sin_pi_div_ten : Real.sin (π / 10) = (√5 - 1) / 4 := by
  have h1 : Real.sin (π / 10) = Real.cos (2 * (π / 5)) := by
    rw [← Real.cos_pi_div_two_sub]; congr 1; ring
  rw [h1, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [sqrt5_sq]

theorem inv_phi_eq_two_sin : phi⁻¹ = 2 * Real.sin (π / 10) := by
  rw [inv_phi_eq_phi_sub_one, sin_pi_div_ten, phi_def]; ring

/-! ## 2. arctan(1/φ) + arctan(1/φ³) = π/4 -/

lemma pair_aux (p : ℝ) (hp : 0 < p) (h : p ^ 2 = p + 1) :
    (1 / p + 1 / p ^ 3) / (1 - 1 / p * (1 / p ^ 3)) = 1 := by
  have hq : p ^ 3 = 2 * p + 1 := by nlinarith
  have h4 : p ^ 4 = 3 * p + 2 := by nlinarith
  have h1 : 1 < p := by nlinarith
  have hlt : (1 / p) * (1 / p ^ 3) < 1 := by
    have : 1 < p * p ^ 3 := by nlinarith [pow_pos hp 3]
    rw [div_mul_div_comm, one_mul, div_lt_one (by positivity)]; exact this
  have hd : (1 : ℝ) - 1 / p * (1 / p ^ 3) ≠ 0 := by intro h'; linarith
  rw [div_eq_one_iff_eq hd]
  have hp0 : p ≠ 0 := hp.ne'
  field_simp
  nlinarith [hq, h4]

theorem arctan_phi_pair :
    Real.arctan (1 / phi) + Real.arctan (1 / phi ^ 3) = π / 4 := by
  have hp := phi_pos
  have h1 : 1 < phi := Real.one_lt_goldenRatio
  have hlt : (1 / phi) * (1 / phi ^ 3) < 1 := by
    have : 1 < phi * phi ^ 3 := by nlinarith [pow_pos hp 3, one_lt_pow₀ h1 (by norm_num : 3 ≠ 0)]
    rw [div_mul_div_comm, one_mul, div_lt_one (by positivity)]; exact this
  rw [Real.arctan_add hlt, pair_aux phi hp phi_sq, Real.arctan_one]

/-! ## 3. Fibonacci, Cassini, arctan telescoping -/

lemma fib_cassini (m : ℕ) :
    ((Nat.fib (m + 2) : ℤ)) * Nat.fib m - (Nat.fib (m + 1) : ℤ) ^ 2 = (-1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have e1 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
    have e2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, e1]
    rw [e2] at ih ⊢
    linear_combination (-1 : ℤ) * ih

/-- `F_m F_{m+3} - F_{m+1} F_{m+2} = (-1)^(m+1)` (d'Ocagne 꼴). -/
lemma fib_docagne (m : ℕ) :
    (Nat.fib m : ℤ) * Nat.fib (m + 3) - (Nat.fib (m + 1) : ℤ) * Nat.fib (m + 2)
      = (-1) ^ (m + 1) := by
  have e1 : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    rw [show m + 3 = (m + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  have e2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  have c := fib_cassini m
  rw [e1]
  rw [e2] at c ⊢
  linear_combination c

lemma fib_pos_real {n : ℕ} (h : 0 < n) : (0 : ℝ) < Nat.fib n := by
  exact_mod_cast Nat.fib_pos.mpr h

lemma two_le_fib {n : ℕ} (h : 3 ≤ n) : (2 : ℝ) ≤ Nat.fib n := by
  have : 2 ≤ Nat.fib n := by
    calc 2 = Nat.fib 3 := by decide
      _ ≤ Nat.fib n := Nat.fib_mono h
  exact_mod_cast this

lemma split_aux (a b c : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 0 < c)
    (hd : c * (a + b) = a * b - 1) :
    Real.arctan (1 / c) = Real.arctan (1 / a) + Real.arctan (1 / b) := by
  have ha0 : a ≠ 0 := by positivity
  have hb0 : b ≠ 0 := by positivity
  have hlt : (1 / a) * (1 / b) < 1 := by
    rw [div_mul_div_comm, one_mul, div_lt_one (by positivity)]; nlinarith
  rw [Real.arctan_add hlt]
  congr 1
  have hab : a * b - 1 ≠ 0 := by nlinarith
  have hne1 : (1 : ℝ) - 1 / a * (1 / b) ≠ 0 := by intro h; linarith
  rw [eq_div_iff hne1]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp
  nlinarith [hd]

/-- n ≥ 1:  arctan(1/F_{2n}) = arctan(1/F_{2n+1}) + arctan(1/F_{2n+2}). -/
theorem arctan_fib_split (n : ℕ) (hn : 1 ≤ n) :
    Real.arctan (1 / (Nat.fib (2 * n) : ℝ))
      = Real.arctan (1 / (Nat.fib (2 * n + 1) : ℝ))
        + Real.arctan (1 / (Nat.fib (2 * n + 2) : ℝ)) := by
  have ha : (2 : ℝ) ≤ Nat.fib (2 * n + 1) := two_le_fib (by omega)
  have hb : (2 : ℝ) ≤ Nat.fib (2 * n + 2) := two_le_fib (by omega)
  have h0 : (0 : ℝ) < Nat.fib (2 * n) := fib_pos_real (by omega)
  have hd : (Nat.fib (2 * n) : ℝ) * Nat.fib (2 * n + 3)
        - (Nat.fib (2 * n + 1) : ℝ) * Nat.fib (2 * n + 2) = -1 := by
    have := fib_docagne (2 * n)
    have h2 : ((-1 : ℤ)) ^ (2 * n + 1) = -1 := by
      rw [pow_succ, pow_mul]; simp
    rw [h2] at this
    exact_mod_cast this
  have e1 : (Nat.fib (2 * n + 3) : ℝ) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
    rw [show 2 * n + 3 = (2 * n + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  rw [e1] at hd
  exact split_aux _ _ _ ha hb h0 (by linarith)

/-- 부분합 정확식: Σ_{k=0}^{N} arctan(1/F_{2k+1}) = π/2 − arctan(1/F_{2N+2}). -/
theorem arctan_fib_partial (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), Real.arctan (1 / (Nat.fib (2 * k + 1) : ℝ))
      = π / 2 - Real.arctan (1 / (Nat.fib (2 * N + 2) : ℝ)) := by
  induction N with
  | zero =>
    have f1 : Nat.fib (2 * 0 + 1) = 1 := by decide
    have f2 : Nat.fib (2 * 0 + 2) = 1 := by decide
    rw [Finset.sum_range_one, f1, f2]
    norm_num [Real.arctan_one]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := arctan_fib_split (N + 1) (by omega)
    have e1 : 2 * (N + 1) = 2 * N + 2 := by ring
    have e2 : 2 * (N + 1) + 1 = 2 * (N + 1) + 1 := rfl
    rw [e1] at h
    have e3 : 2 * N + 2 + 1 = 2 * (N + 1) + 1 := by ring
    have e4 : 2 * N + 2 + 2 = 2 * (N + 1) + 2 := by ring
    rw [e3, e4] at h
    linarith

theorem fib_even_tendsto :
    Tendsto (fun N : ℕ => (Nat.fib (2 * N + 2) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := Nat.le_fib_self (by omega : 5 ≤ 2 * N + 2)
  have : N ≤ Nat.fib (2 * N + 2) := by omega
  exact_mod_cast this

/-- 극한: Σ_{k≥0} arctan(1/F_{2k+1}) = π/2 (부분합의 극한). -/
theorem arctan_fib_tendsto :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), Real.arctan (1 / (Nat.fib (2 * k + 1) : ℝ)))
      atTop (𝓝 (π / 2)) := by
  have h1 : Tendsto (fun N : ℕ => 1 / (Nat.fib (2 * N + 2) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp fib_even_tendsto)
  have h2 : Tendsto (fun N : ℕ => Real.arctan (1 / (Nat.fib (2 * N + 2) : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp h1
  have h3 := (tendsto_const_nhds (x := π / 2)).sub h2
  simp only [sub_zero] at h3
  refine h3.congr (fun N => ?_)
  exact (arctan_fib_partial N).symm

theorem arctan_fib_hasSum :
    HasSum (fun k : ℕ => Real.arctan (1 / (Nat.fib (2 * k + 1) : ℝ))) (π / 2) := by
  have hnn : ∀ k : ℕ, 0 ≤ Real.arctan (1 / (Nat.fib (2 * k + 1) : ℝ)) := by
    intro k
    have : (0 : ℝ) < Nat.fib (2 * k + 1) := fib_pos_real (by omega)
    rw [← Real.arctan_zero]
    exact Real.arctan_strictMono.monotone (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  exact (tendsto_add_atTop_iff_nat 1).mp arctan_fib_tendsto

/-! ## 4. φ 의 거듭제곱: φ^(n+1) = F_{n+1} φ + F_n -/

theorem phi_pow_fib (n : ℕ) :
    phi ^ (n + 1) = (Nat.fib (n + 1) : ℝ) * phi + Nat.fib n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [pow_succ, ih, e]
    nlinarith [phi_sq]

/-- 비네 공식 (Mathlib 인용): F_n = (φ^n − ψ^n)/√5. -/
theorem binet (n : ℕ) : (Nat.fib n : ℝ) = (phi ^ n - Real.goldenConj ^ n) / √5 :=
  Real.coe_fib_eq n

theorem phi_inv_pow_identity : phi ^ 2 - phi = 1 ∧ phi - phi⁻¹ = 1 := by
  refine ⟨by nlinarith [phi_sq], ?_⟩
  rw [inv_phi_eq_phi_sub_one]; ring

/-! ## 4b. 루카스 짝수 번째 arctan 망원합: Σ_{k≥1} arctan(1/L_{2k}) = arctan(1/φ)
(L_{2k} = F_{2k-1} + F_{2k+1}).  수치 탐색에서 발견한 뒤 증명한 항목; 문헌 확인 전. -/

lemma t_facts : 0 < phi⁻¹ ∧ phi⁻¹ < 1 ∧ phi⁻¹ ^ 2 = 1 - phi⁻¹ := by
  have h1 : 1 < phi := Real.one_lt_goldenRatio
  have e := inv_phi_eq_phi_sub_one
  refine ⟨inv_pos.mpr phi_pos, inv_lt_one_of_one_lt₀ h1, ?_⟩
  rw [e]; nlinarith [phi_sq]

theorem tele_step (j : ℕ) :
    Real.arctan (1 / (phi ^ (2 * j + 2) + (phi⁻¹) ^ (2 * j + 2)))
      = Real.arctan ((phi⁻¹) ^ (2 * j + 1)) - Real.arctan ((phi⁻¹) ^ (2 * j + 3)) := by
  obtain ⟨ht, ht1, ht2⟩ := t_facts
  set t : ℝ := phi⁻¹ with htdef
  have hphi : ∀ m : ℕ, phi ^ m = (t ^ m)⁻¹ := by
    intro m; rw [htdef, inv_pow, inv_inv]
  rw [hphi]
  set x : ℝ := t ^ (2 * j + 1) with hx
  have hx0 : 0 < x := pow_pos ht _
  have h2 : t ^ (2 * j + 2) = x * t := by rw [hx]; ring
  have h3 : t ^ (2 * j + 3) = x * t ^ 2 := by rw [hx]; ring
  rw [h2, h3, sub_eq_add_neg, ← Real.arctan_neg]
  have hxt : 0 < x * t := mul_pos hx0 ht
  have hlt : x * (-(x * t ^ 2)) < 1 := by nlinarith [mul_pos hx0 hx0, sq_nonneg t]
  rw [Real.arctan_add hlt]
  congr 1
  have hn : x + -(x * t ^ 2) = x * t := by rw [ht2]; ring
  have hd : (1 : ℝ) - x * (-(x * t ^ 2)) = 1 + (x * t) ^ 2 := by ring
  rw [hn, hd]
  field_simp

theorem tele_partial (N : ℕ) :
    ∑ j ∈ Finset.range N, Real.arctan (1 / (phi ^ (2 * j + 2) + (phi⁻¹) ^ (2 * j + 2)))
      = Real.arctan (phi⁻¹) - Real.arctan ((phi⁻¹) ^ (2 * N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, tele_step N]
    have : 2 * (N + 1) + 1 = 2 * N + 3 := by ring
    rw [this]; ring

theorem tele_tendsto :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N,
        Real.arctan (1 / (phi ^ (2 * j + 2) + (phi⁻¹) ^ (2 * j + 2))))
      atTop (𝓝 (Real.arctan (1 / phi))) := by
  obtain ⟨ht, ht1, -⟩ := t_facts
  have h1 : Tendsto (fun N : ℕ => (phi⁻¹) ^ (2 * N + 1)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht1
    have hN : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop :=
      tendsto_atTop_mono (fun N : ℕ => (by simp only [id]; omega : id N ≤ 2 * N + 1)) tendsto_id
    exact this.comp hN
  have h2 : Tendsto (fun N : ℕ => Real.arctan ((phi⁻¹) ^ (2 * N + 1))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp h1
  have h3 := (tendsto_const_nhds (x := Real.arctan (phi⁻¹))).sub h2
  simp only [sub_zero] at h3
  rw [one_div]
  exact h3.congr (fun N => (tele_partial N).symm)

/-- 비네 꼴: F_m + F_{m+2} = φ^{m+1} + ψ^{m+1}  (= L_{m+1}). -/
theorem fib_add_fib_add_two (m : ℕ) :
    (Nat.fib m : ℝ) + Nat.fib (m + 2) = phi ^ (m + 1) + Real.goldenConj ^ (m + 1) := by
  have h5 : (√5) ≠ 0 := by positivity
  have hs : √5 = phi - Real.goldenConj := (Real.goldenRatio_sub_goldenConj).symm
  have hpp : phi * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
  rw [binet m, binet (m + 2), ← add_div, div_eq_iff h5, hs]
  linear_combination (phi ^ m - Real.goldenConj ^ m) * hpp
    + (phi ^ m) * (Real.goldenRatio_sq) * 0 + 0 * Real.goldenConj_sq

theorem goldenConj_even_pow (j : ℕ) :
    Real.goldenConj ^ (2 * j + 2) = (phi⁻¹) ^ (2 * j + 2) := by
  rw [Real.inv_goldenRatio, neg_pow, show (-1 : ℝ) ^ (2 * j + 2) = 1 by
    rw [pow_add, pow_mul]; simp]; simp

/-- Σ_{k≥1} arctan(1/L_{2k}) = arctan(1/φ),  L_{2k} = F_{2k-1}+F_{2k+1}. -/
theorem arctan_lucas_even_tendsto :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N,
        Real.arctan (1 / ((Nat.fib (2 * j + 1) : ℝ) + Nat.fib (2 * j + 3))))
      atTop (𝓝 (Real.arctan (1 / phi))) := by
  have key : ∀ j : ℕ, ((Nat.fib (2 * j + 1) : ℝ) + Nat.fib (2 * j + 3))
      = phi ^ (2 * j + 2) + (phi⁻¹) ^ (2 * j + 2) := by
    intro j
    rw [fib_add_fib_add_two (2 * j + 1)]
    rw [← goldenConj_even_pow j]
  simpa only [key] using tele_tendsto

/-! ## 5. 바젤 값 ζ(2)=π²/6 은 황금비가 아니다 -/

lemma phi_bounds : (1.618 : ℝ) < phi ∧ phi < 1.6181 := by
  have h5 : (2.236 : ℝ) < √5 := by
    rw [show (2.236 : ℝ) = √(2.236 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h6 : √5 < 2.2361 := by
    rw [show (2.2361 : ℝ) = √(2.2361 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [phi_def]; constructor <;> linarith

theorem basel_gt_phi : phi < π ^ 2 / 6 := by
  have := Real.pi_gt_d4
  have hb := phi_bounds
  nlinarith

theorem basel_ne_phi : π ^ 2 / 6 ≠ phi := (basel_gt_phi).ne'

theorem basel_gap : 0.026 < π ^ 2 / 6 - phi ∧ π ^ 2 / 6 - phi < 0.027 := by
  have a := Real.pi_gt_d4
  have b := Real.pi_lt_d4
  have hb := phi_bounds
  constructor <;> nlinarith

theorem hasSum_basel_ne_phi :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) ∧ π ^ 2 / 6 ≠ phi :=
  ⟨hasSum_zeta_two, basel_ne_phi⟩

end KimbanjiPhiPi

#print axioms KimbanjiPhiPi.phi_eq_two_cos
#print axioms KimbanjiPhiPi.inv_phi_eq_two_sin
#print axioms KimbanjiPhiPi.arctan_phi_pair
#print axioms KimbanjiPhiPi.fib_docagne
#print axioms KimbanjiPhiPi.arctan_fib_split
#print axioms KimbanjiPhiPi.arctan_fib_partial
#print axioms KimbanjiPhiPi.arctan_fib_tendsto
#print axioms KimbanjiPhiPi.arctan_fib_hasSum
#print axioms KimbanjiPhiPi.phi_pow_fib
#print axioms KimbanjiPhiPi.basel_ne_phi
#print axioms KimbanjiPhiPi.basel_gap
#print axioms KimbanjiPhiPi.hasSum_basel_ne_phi
#print axioms KimbanjiPhiPi.tele_step
#print axioms KimbanjiPhiPi.fib_add_fib_add_two
#print axioms KimbanjiPhiPi.arctan_lucas_even_tendsto

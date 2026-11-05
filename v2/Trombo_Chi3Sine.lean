import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Trombo certificates, rungs 1 and 2

* `chi3` : the non-principal Dirichlet character modulo 3, written as an integer function.
* `chi3_eq_sin` : for every integer `n`, `chi3 n = (2/√3) · sin(2πn/3)` in `ℝ`.
* `infinite_primes_one_mod_six`, `infinite_primes_five_mod_six` : Dirichlet's theorem
  (from Mathlib) specialised to the two classes `1` and `5` modulo `6`.
-/

open Real

/-- The character modulo 3: `0` if `3 ∣ n`, `1` if `n ≡ 1 (mod 3)`, `-1` if `n ≡ 2 (mod 3)`.
(`Int.emod` is used, so `n % 3 ∈ {0,1,2}` also for negative `n`.) -/
def chi3 (n : ℤ) : ℤ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

/-- **Sine identity.** For every integer `n`,
`(chi3 n : ℝ) = 2 / √3 * sin (2 * π * n / 3)`. -/
theorem chi3_eq_sin (n : ℤ) :
    (chi3 n : ℝ) = 2 / Real.sqrt 3 * Real.sin (2 * π * n / 3) := by
  have hdecomp : (2 * π * n / 3 : ℝ) = 2 * π * ((n % 3 : ℤ) : ℝ) / 3 + ((n / 3 : ℤ) : ℝ) * (2 * π) := by
    have h := Int.emod_add_mul_ediv n 3
    have h' : ((n : ℤ) : ℝ) = ((n % 3 : ℤ) : ℝ) + 3 * ((n / 3 : ℤ) : ℝ) := by
      exact_mod_cast h.symm
    rw [h']; ring
  rw [hdecomp, Real.sin_add_int_mul_two_pi]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hr0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hr3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · simp [chi3, h]
  · have : Real.sin (2 * π * ((1 : ℤ) : ℝ) / 3) = Real.sqrt 3 / 2 := by
      rw [show (2 * π * ((1 : ℤ) : ℝ) / 3) = π - π / 3 by push_cast; ring, Real.sin_pi_sub,
        Real.sin_pi_div_three]
    rw [h, this]
    simp only [chi3, h]
    field_simp
    norm_num
  · have : Real.sin (2 * π * ((2 : ℤ) : ℝ) / 3) = -(Real.sqrt 3 / 2) := by
      rw [show (2 * π * ((2 : ℤ) : ℝ) / 3) = π / 3 + π by push_cast; ring, Real.sin_add_pi,
        Real.sin_pi_div_three]
    rw [h, this]
    simp only [chi3, h]
    field_simp
    norm_num

/-- **Dirichlet, class 1 mod 6.** There are infinitely many primes `p` with `p ≡ 1 (mod 6)`
(stated as `(p : ZMod 6) = 1`). Direct specialisation of Mathlib's
`Nat.infinite_setOfPred_prime_and_eq_mod`. -/
theorem infinite_primes_one_mod_six :
    {p : ℕ | p.Prime ∧ (p : ZMod 6) = 1}.Infinite :=
  Nat.infinite_setOfPred_prime_and_eq_mod isUnit_one

/-- **Dirichlet, class 5 mod 6.** There are infinitely many primes `p` with `p ≡ 5 (mod 6)`
(stated as `(p : ZMod 6) = 5`). Direct specialisation of Mathlib's
`Nat.infinite_setOfPred_prime_and_eq_mod`, using that `5` is a unit in `ZMod 6`. -/
theorem infinite_primes_five_mod_six :
    {p : ℕ | p.Prime ∧ (p : ZMod 6) = 5}.Infinite := by
  have hu : IsUnit (5 : ZMod 6) := by
    exact isUnit_iff_exists_inv.mpr ⟨5, by decide⟩
  exact Nat.infinite_setOfPred_prime_and_eq_mod hu

/-- The same two classes in `%` form: for every `N` there are primes `p > N` with `p % 6 = 1`,
and primes `p > N` with `p % 6 = 5`. -/
theorem exists_prime_gt_one_and_five_mod_six (N : ℕ) :
    (∃ p > N, p.Prime ∧ p % 6 = 1) ∧ (∃ p > N, p.Prime ∧ p % 6 = 5) := by
  constructor
  · obtain ⟨p, hmem, hgt⟩ := Set.infinite_iff_exists_gt.mp infinite_primes_one_mod_six N
    refine ⟨p, hgt, hmem.1, ?_⟩
    have h1 : ((p : ℕ) : ZMod 6) = ((1 : ℕ) : ZMod 6) := by simpa using hmem.2
    simpa using (ZMod.natCast_eq_natCast_iff' p 1 6).mp h1
  · obtain ⟨p, hmem, hgt⟩ := Set.infinite_iff_exists_gt.mp infinite_primes_five_mod_six N
    refine ⟨p, hgt, hmem.1, ?_⟩
    have h1 : ((p : ℕ) : ZMod 6) = ((5 : ℕ) : ZMod 6) := by simpa using hmem.2
    simpa using (ZMod.natCast_eq_natCast_iff' p 5 6).mp h1

#print axioms chi3_eq_sin
#print axioms infinite_primes_one_mod_six
#print axioms infinite_primes_five_mod_six
#print axioms exists_prime_gt_one_and_five_mod_six

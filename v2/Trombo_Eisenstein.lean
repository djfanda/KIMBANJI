import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Int.ModEq

/-!
# Trombo certificate, rung 5: primes `p ≡ 1 (mod 3)` are values of `x² + xy + y²`

* `exists_sq_add_add_one_eq_zero` : if `p ≡ 1 (mod 3)` is prime, some `g : ZMod p`
  satisfies `g² + g + 1 = 0` (Cauchy's theorem gives an element of order 3 in `(ZMod p)ˣ`).
* `thue` : Thue's lemma (A. Thue, 1902) by pigeonhole: for `p > 0` and any integer `a` there are integers
  `x, y`, not both zero, with `|x|, |y| ≤ ⌊√p⌋` and `p ∣ x - a·y`.
* `eisenstein_rep_int` / `eisenstein_rep` : every prime `p ≡ 1 (mod 3)` equals
  `x² + x·y + y²` for some integers, and also for some natural numbers.
-/

namespace Trombo

/-- If `p` is prime with `p % 3 = 1`, there is `g : ZMod p` with `g^2 + g + 1 = 0`. -/
theorem exists_sq_add_add_one_eq_zero (p : ℕ) [hp : Fact p.Prime] (h3 : p % 3 = 1) :
    ∃ g : ZMod p, g ^ 2 + g + 1 = 0 := by
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  have hcube : (g : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have hne : (g : ZMod p) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext h
    rw [this, orderOf_one] at hg
    norm_num at hg
  refine ⟨g, ?_⟩
  have hprod : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by
    have : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = (g : ZMod p) ^ 3 - 1 := by ring
    rw [this, hcube, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

/-- **Thue's lemma** (pigeonhole form). For `0 < p` and any integer `a`, there exist integers
`x, y`, not both zero, with `|x| ≤ √p`, `|y| ≤ √p` (integer square root) and `p ∣ x - a * y`. -/
theorem thue (p : ℕ) (hp : 0 < p) (a : ℤ) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ |x| ≤ Nat.sqrt p ∧ |y| ≤ Nat.sqrt p ∧ (p : ℤ) ∣ x - a * y := by
  set s := Nat.sqrt p with hs
  let S : Finset (ℕ × ℕ) := (Finset.range (s + 1)) ×ˢ (Finset.range (s + 1))
  let f : ℕ × ℕ → ℕ := fun uv ↦ (((uv.1 : ℤ) - a * uv.2) % (p : ℤ)).toNat
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hcard : (Finset.range p).card < S.card := by
    simp only [S, Finset.card_product, Finset.card_range]
    have := Nat.lt_succ_sqrt' p
    rw [← hs] at this
    nlinarith [this]
  have hmaps : ∀ uv ∈ S, f uv ∈ Finset.range p := by
    intro uv _
    simp only [f, Finset.mem_range]
    have h1 := Int.emod_nonneg ((uv.1 : ℤ) - a * uv.2) hpz.ne'
    have h2 := Int.emod_lt_of_pos ((uv.1 : ℤ) - a * uv.2) hpz
    omega
  obtain ⟨⟨u1, v1⟩, h1, ⟨u2, v2⟩, h2, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [S, Finset.mem_product, Finset.mem_range] at h1 h2
  refine ⟨(u1 : ℤ) - u2, (v1 : ℤ) - v2, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    apply hne
    have e1 : u1 = u2 := by omega
    have e2 : v1 = v2 := by omega
    rw [e1, e2]
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega
  · have m1 := Int.emod_nonneg ((u1 : ℤ) - a * v1) hpz.ne'
    have m2 := Int.emod_nonneg ((u2 : ℤ) - a * v2) hpz.ne'
    simp only [f] at heq
    have heq' : ((u1 : ℤ) - a * v1) % p = ((u2 : ℤ) - a * v2) % p := by omega
    have hd := (Int.ModEq.dvd (show ((u2 : ℤ) - a * v2) ≡ ((u1 : ℤ) - a * v1) [ZMOD p] from heq'.symm))
    have : (u1 : ℤ) - a * v1 - (u2 - a * v2) = (u1 - u2) - a * (v1 - v2) := by ring
    rw [this] at hd
    exact hd

/-- `⌊√p⌋² < p` for a prime `p`. -/
lemma sqrt_sq_lt_prime {p : ℕ} (hp : p.Prime) : Nat.sqrt p ^ 2 < p := by
  have hle := Nat.sqrt_le' p
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hdvd : Nat.sqrt p ∣ p := ⟨Nat.sqrt p, by rw [sq] at h; exact h.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · rw [h1] at h; norm_num at h; exact hp.one_lt.ne h
    · rw [h1] at h
      have := hp.one_lt
      nlinarith

/-- **Eisenstein representation (integers).** Every prime `p` with `p % 3 = 1` is of the form
`x² + x·y + y²` with `x, y ∈ ℤ`. -/
theorem eisenstein_rep_int (p : ℕ) (hp : p.Prime) (h3 : p % 3 = 1) :
    ∃ x y : ℤ, (p : ℤ) = x ^ 2 + x * y + y ^ 2 := by
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_sq_add_add_one_eq_zero p h3
  set a : ℤ := (g.val : ℤ) with ha
  have hga : ((a : ℤ) : ZMod p) = g := by simp [ha]
  have hpa : (p : ℤ) ∣ a ^ 2 + a + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hga, hg]
  obtain ⟨x, y, hxy0, hx, hy, hdiv⟩ := thue p hp.pos a
  have hs := sqrt_sq_lt_prime hp
  have hsz : ((Nat.sqrt p : ℤ)) ^ 2 < (p : ℤ) := by exact_mod_cast hs
  have hx2 : x ^ 2 < p := by
    have : x ^ 2 ≤ (Nat.sqrt p : ℤ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    linarith
  have hy2 : y ^ 2 < p := by
    have : y ^ 2 ≤ (Nat.sqrt p : ℤ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    linarith
  set n := x ^ 2 + x * y + y ^ 2 with hn
  have hdn : (p : ℤ) ∣ n := by
    have e : n = (x - a * y) * (x + a * y + y) + y ^ 2 * (a ^ 2 + a + 1) := by rw [hn]; ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hdiv _) (dvd_mul_of_dvd_right hpa _)
  have hpos : 0 < n := by
    have h4 : 4 * n = (2 * x + y) ^ 2 + 3 * y ^ 2 := by rw [hn]; ring
    rcases hxy0 with h | h
    · by_cases hy0 : y = 0
      · subst hy0
        have : 0 < x ^ 2 := by positivity
        rw [hn]; nlinarith
      · have : 0 < y ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * x + y)]
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * x + y)]
  have hlt : n < 3 * p := by rw [hn]; nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  obtain ⟨k, hk⟩ := hdn
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hk1 : 0 < k := by
    by_contra hc; push Not at hc; nlinarith
  have hk3 : k < 3 := by
    by_contra hc; push Not at hc; nlinarith
  interval_cases k
  · exact ⟨x, y, by rw [← hn, hk, mul_one]⟩
  · exfalso
    -- `x² + xy + y² = 2p` forces `x, y` even, then `2 ∣ p`, so `p = 2`, contradicting `p % 3 = 1`.
    have hz : ((x : ZMod 2)) ^ 2 + (x : ZMod 2) * (y : ZMod 2) + (y : ZMod 2) ^ 2 = 0 := by
      have : ((n : ℤ) : ZMod 2) = 0 := by
        rw [hk, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact ⟨p, by ring⟩
      rw [hn] at this
      push_cast at this
      exact this
    have key : ∀ u v : ZMod 2, u ^ 2 + u * v + v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide
    obtain ⟨hx0, hy0⟩ := key _ _ hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0 hy0
    obtain ⟨x', rfl⟩ := hx0
    obtain ⟨y', rfl⟩ := hy0
    have h2p : (2 : ℤ) ∣ (p : ℤ) := ⟨x' ^ 2 + x' * y' + y' ^ 2, by
      have : n * 1 = n := mul_one n
      linarith [hk, show n = 4 * (x' ^ 2 + x' * y' + y' ^ 2) by rw [hn]; ring]⟩
    have h2p' : 2 ∣ p := by exact_mod_cast h2p
    rcases hp.eq_one_or_self_of_dvd 2 h2p' with h | h
    · norm_num at h
    · omega

/-- **Eisenstein representation (naturals).** Every prime `p` with `p % 3 = 1` is of the form
`x² + x·y + y²` with `x, y ∈ ℕ`. -/
theorem eisenstein_rep (p : ℕ) (hp : p.Prime) (h3 : p % 3 = 1) :
    ∃ x y : ℕ, p = x ^ 2 + x * y + y ^ 2 := by
  obtain ⟨x, y, h⟩ := eisenstein_rep_int p hp h3
  -- reduce sign patterns to the natural-number case
  suffices H : ∃ u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ (p : ℤ) = u ^ 2 + u * v + v ^ 2 by
    obtain ⟨u, v, hu, hv, huv⟩ := H
    refine ⟨u.toNat, v.toNat, ?_⟩
    have e1 : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu
    have e2 : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv
    have : ((p : ℕ) : ℤ) = ((u.toNat ^ 2 + u.toNat * v.toNat + v.toNat ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [e1, e2]; exact huv
    exact_mod_cast this
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · exact ⟨x, y, hx, hy, h⟩
  · -- x ≥ 0, y ≤ 0, write w = -y
    rcases le_total (-y) x with hxy | hxy
    · exact ⟨x + y, -y, by linarith, by linarith, by rw [h]; ring⟩
    · exact ⟨-y - x, x, by linarith, hx, by rw [h]; ring⟩
  · rcases le_total (-x) y with hxy | hxy
    · exact ⟨y + x, -x, by linarith, by linarith, by rw [h]; ring⟩
    · exact ⟨-x - y, y, by linarith, hy, by rw [h]; ring⟩
  · exact ⟨-x, -y, by linarith, by linarith, by rw [h]; ring⟩

end Trombo

#print axioms Trombo.exists_sq_add_add_one_eq_zero
#print axioms Trombo.thue
#print axioms Trombo.sqrt_sq_lt_prime
#print axioms Trombo.eisenstein_rep_int
#print axioms Trombo.eisenstein_rep

import IsingCriticality.Approximants
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Arithmetic scope of the criticality construction

The square-lattice anchor is irrational precisely for nonsquare natural q.
The GP4 approximant is rational at rational inputs. Neither assertion identifies
an approximation with a higher-dimensional physical critical probability.

The factorial-cell theorem is an explicit conditional irrationality criterion.
No factorial-cell certificates for a higher-dimensional physical threshold are
constructed in this file.
-/

namespace IsingCriticality
noncomputable section

/-- The odds-to-probability map preserves irrationality, including its totalized
value at v = -1 (where both v and its image are rational). -/
theorem irrational_odds_iff (v : ℝ) :
    Irrational (v / (1 + v)) ↔ Irrational v := by
  constructor
  · intro h
    by_contra hv
    obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hv
    rw [hr] at h
    apply (Rat.not_irrational (r / (1 + r)))
    simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_one] using h
  · intro hv
    have hsum : Irrational (1 + v) := by
      simpa only [Nat.cast_one] using hv.natCast_add 1
    have heq : v / (1 + v) = 1 - (1 + v)⁻¹ := by
      field_simp [hsum.ne_zero] <;> ring
    rw [heq]
    simpa only [Nat.cast_one] using hsum.inv.natCast_sub 1

/-- Exact square-lattice formula. Its identification with physical criticality
is supplied by the cited planar random-cluster theorem, not formalized here. -/
def squareLatticeAnchor (q : ℕ) : ℝ :=
  Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ))

theorem squareLatticeAnchor_irrational_iff (q : ℕ) :
    Irrational (squareLatticeAnchor q) ↔ ¬ IsSquare q := by
  unfold squareLatticeAnchor
  rw [irrational_odds_iff, irrational_sqrt_natCast_iff]

theorem squareLatticeAnchor_two_irrational :
    Irrational (squareLatticeAnchor 2) := by
  unfold squareLatticeAnchor
  apply (irrational_odds_iff _).2
  simpa only [Nat.cast_ofNat] using irrational_sqrt_two

theorem squareLatticeAnchor_three_irrational :
    Irrational (squareLatticeAnchor 3) := by
  unfold squareLatticeAnchor
  exact (irrational_odds_iff _).2 Nat.prime_three.irrational_sqrt

theorem squareLatticeAnchor_one : squareLatticeAnchor 1 = 1 / 2 := by
  norm_num [squareLatticeAnchor]

theorem squareLatticeAnchor_one_not_irrational :
    ¬ Irrational (squareLatticeAnchor 1) := by
  rw [squareLatticeAnchor_one]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (Rat.not_irrational (1 / 2 : ℚ))

/-- Rational counterpart of GP4, used only to exhibit its arithmetic nature. -/
def gp4Rational (q d : ℚ) : ℚ :=
  let s := 2 * d - 1
  let a := 1 + (8 - 3 * q) / (2 * s ^ 2) + 3 * (8 - 3 * q) / (2 * s ^ 3) +
    3 * (68 - 31 * q + q ^ 2) / (2 * s ^ 4)
  q * a / (2 * d - 1 + (q - 1) * a)

theorem gp4_ratCast (q d : ℚ) :
    gp4 (q : ℝ) (d : ℝ) = (gp4Rational q d : ℝ) := by
  simp [gp4, gp4A, gp4Rational]

theorem gp4_ratCast_not_irrational (q d : ℚ) :
    ¬ Irrational (gp4 (q : ℝ) (d : ℝ)) := by
  rw [gp4_ratCast]
  exact Rat.not_irrational _

theorem gp4_natCast_not_irrational (q d : ℕ) :
    ¬ Irrational (gp4 (q : ℝ) (d : ℝ)) := by
  simpa only [Rat.cast_natCast] using
    gp4_ratCast_not_irrational (q : ℚ) (d : ℚ)

/-- Eventual strict factorial cells exclude every rational denominator.
The hypothesis is a universal certificate requirement, not an established
property of any physical critical threshold. -/
theorem irrational_of_eventual_scaled_factorial_cells {x : ℝ}
    (h : ∃ N : ℕ, ∀ n ≥ N, ∃ A : ℤ,
      (A : ℝ) < (n.factorial : ℝ) * x ∧
      (n.factorial : ℝ) * x < (A : ℝ) + 1) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  rcases h with ⟨N, hN⟩
  let n := max N r.den
  have hdiv : r.den ∣ n.factorial :=
    Nat.dvd_factorial r.den_pos (le_max_right N r.den)
  rcases hdiv with ⟨k, hk⟩
  obtain ⟨A, hlo, hhi⟩ := hN n (le_max_left N r.den)
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have heq : (n.factorial : ℝ) * (r : ℝ) =
      (((k : ℤ) * r.num : ℤ) : ℝ) := by
    rw [Rat.cast_def, hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    field_simp [hd] <;> ring
  rw [heq] at hlo hhi
  have hlo' : A < (k : ℤ) * r.num := by exact_mod_cast hlo
  have hhi' : (k : ℤ) * r.num < A + 1 := by exact_mod_cast hhi
  omega

/-- Division-form version of the earlier factorial-cell research criterion. -/
theorem irrational_of_eventual_factorial_cells {x : ℝ}
    (h : ∃ N : ℕ, ∀ n ≥ N, ∃ A : ℤ,
      (A : ℝ) / (n.factorial : ℝ) < x ∧
      x < ((A : ℝ) + 1) / (n.factorial : ℝ)) :
    Irrational x := by
  apply irrational_of_eventual_scaled_factorial_cells
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨A, hlo, hhi⟩ := hN n hn
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  refine ⟨A, ?_, ?_⟩
  · simpa only [mul_comm] using (div_lt_iff₀ hpos).1 hlo
  · simpa only [mul_comm] using (lt_div_iff₀ hpos).1 hhi

end
end IsingCriticality

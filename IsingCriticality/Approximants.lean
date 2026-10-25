import PCD.Q3Defs

namespace IsingCriticality
noncomputable section

/-- Reciprocal-coordination GP4 correction. Literature coefficients are inputs. -/
def gp4A (q d : ℝ) : ℝ :=
  let s := 2*d-1
  1 + (8-3*q)/(2*s^2) + 3*(8-3*q)/(2*s^3) + 3*(68-31*q+q^2)/(2*s^4)

/-- Continuous-branch approximant; not defined to be the physical threshold. -/
def gp4 (q d : ℝ) : ℝ := q * gp4A q d / (2*d-1+(q-1)*gp4A q d)

/-- The GP4 equation is solved exactly by the rational formula. -/
theorem gp4_solves (q d : ℝ) (h : 2*d-1+(q-1)*gp4A q d ≠ 0) :
    (2*d-1+(q-1)*gp4A q d) * gp4 q d = q * gp4A q d := by
  unfold gp4
  field_simp

/-- Uniqueness here is algebraic uniqueness, not identification with criticality. -/
theorem gp4_unique (q d p : ℝ) (h : 2*d-1+(q-1)*gp4A q d ≠ 0)
    (hp : (2*d-1+(q-1)*gp4A q d)*p = q*gp4A q d) : p = gp4 q d := by
  unfold gp4
  apply (eq_div_iff h).2
  simpa [mul_comm] using hp

theorem gp4_q2_correction (d : ℝ) :
    gp4A 2 d = 1 + 1/(2*d-1)^2 + 3/(2*d-1)^3 + 15/(2*d-1)^4 := by
  by_cases h : 2*d-1 = 0
  · simp [gp4A, h]
  · unfold gp4A
    field_simp
    ring

theorem gp4_q1_d3 : gp4 1 3 = 782/3125 := by norm_num [gp4, gp4A]
theorem gp4_q2_d3 : gp4 2 3 = 272/761 := by norm_num [gp4, gp4A]

/-- Formula-only certification for all q=1,2 rows: exact rational arithmetic. -/
theorem gp4_q2_d3_rounds8 : PCD.roundsTo8Real (gp4 2 3) 35742444 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d3_rounds8 : PCD.roundsTo8Real (gp4 1 3) 25024000 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d4_rounds8 : PCD.roundsTo8Real (gp4 1 4) 15666092 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d5_rounds8 : PCD.roundsTo8Real (gp4 1 5) 11664888 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d6_rounds8 : PCD.roundsTo8Real (gp4 1 6) 9365356 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d7_rounds8 : PCD.roundsTo8Real (gp4 1 7) 7847711 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d8_rounds8 : PCD.roundsTo8Real (gp4 1 8) 6763062 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d9_rounds8 : PCD.roundsTo8Real (gp4 1 9) 5946233 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d10_rounds8 : PCD.roundsTo8Real (gp4 1 10) 5307663 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q1_d11_rounds8 : PCD.roundsTo8Real (gp4 1 11) 4794152 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d4_rounds8 : PCD.roundsTo8Real (gp4 2 4) 25771005 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d5_rounds8 : PCD.roundsTo8Real (gp4 2 5) 20336817 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d6_rounds8 : PCD.roundsTo8Real (gp4 2 6) 16842847 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d7_rounds8 : PCD.roundsTo8Real (gp4 2 7) 14389230 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d8_rounds8 : PCD.roundsTo8Real (gp4 2 8) 12565949 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d9_rounds8 : PCD.roundsTo8Real (gp4 2 9) 11155704 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d10_rounds8 : PCD.roundsTo8Real (gp4 2 10) 10031559 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

 theorem gp4_q2_d11_rounds8 : PCD.roundsTo8Real (gp4 2 11) 9114064 := by
  norm_num [PCD.roundsTo8Real, gp4, gp4A]

end
end IsingCriticality

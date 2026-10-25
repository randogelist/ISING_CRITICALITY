import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=8. -/
theorem q3_d8_enclosure : rat 16627150159 100000000000 < pSquare 8 ∧ pSquare 8 < rat 8313575087 50000000000 := by
  rcases root2_d8_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 8 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 248786427 1250000000 < vB 8 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 8 < rat 1990291417 10000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 8 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 24886193 400000000 < tB 8 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 8 < rat 311077413 5000000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 1941944511 10000000000 < tRatio 8 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 8 < rat 485486129 2500000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 8 := by
    have : (0 : ℝ) < rat 1941944511 10000000000 := by norm_num [rat]
    linarith
  have hr4L : (rat 1941944511 10000000000) ^ 4 < (tRatio 8) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 8) ^ 4 < (rat 485486129 2500000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((7 : ℝ) / 2) := by norm_num
  have hdL : rat 20182213 10000000000 < deltaSquare 8 := by
    change rat 20182213 10000000000 < ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 8) ^ 4
    have h0 : rat 20182213 10000000000 < ((7 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1941944511 10000000000) ^ 4 := by
      norm_num [rat]
    have h1 : ((7 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1941944511 10000000000) ^ 4 <
        ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1941944511 10000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1941944511 10000000000) ^ 4 <
        ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 8) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 8 < rat 10091107 5000000000 := by
    change ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 8) ^ 4 < rat 10091107 5000000000
    have h1 : ((7 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 8) ^ 4 <
        ((7 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 8) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((7 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((7 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 8) ^ 4 <
        ((7 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 485486129 2500000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((7 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 485486129 2500000000) ^ 4 < rat 10091107 5000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 313131331 312500000 < Real.exp (rat 20182213 10000000000) := by
    calc
      rat 313131331 312500000 < ∑ m ∈ Finset.range 7, (rat 20182213 10000000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 20182213 10000000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 10091107 5000000000) < rat 5010101297 5000000000 := by
    calc
      Real.exp (rat 10091107 5000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 10091107 5000000000) ^ m / m.factorial) +
            (rat 10091107 5000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 5010101297 5000000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 313131331 312500000 < Real.exp (deltaSquare 8) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 8) < rat 5010101297 5000000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 8 := by
    have : (0 : ℝ) < rat 248786427 1250000000 := by norm_num [rat]
    linarith
  have hvsL : rat 3116113 15625000 < vSquare 8 := by
    unfold vSquare
    have h0 : rat 3116113 15625000 < (rat 248786427 1250000000) * (rat 313131331 312500000) := by norm_num [rat]
    have h1 : (rat 248786427 1250000000) * (rat 313131331 312500000) < vB 8 * (rat 313131331 312500000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 8 * (rat 313131331 312500000) < vB 8 * Real.exp (deltaSquare 8) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 8 < rat 997156161 5000000000 := by
    unfold vSquare
    have h1 : vB 8 * Real.exp (deltaSquare 8) < vB 8 * (rat 5010101297 5000000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 8 * (rat 5010101297 5000000000) < (rat 1990291417 10000000000) * (rat 5010101297 5000000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 1990291417 10000000000) * (rat 5010101297 5000000000) < rat 997156161 5000000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 8 := by
    have : (0 : ℝ) < rat 3116113 15625000 := by norm_num [rat]
    linarith
  have hpL : rat 16627150159 100000000000 < pSquare 8 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 8)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 8 < rat 8313575087 50000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 8)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=8 rounds to 8 decimals. -/
theorem q3_d8_rounds8 : roundsTo8Real (pSquare 8) 16627150 := by
  rcases q3_d8_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((16627150 : ℝ) / 100000000 - 1 / 200000000) < rat 16627150159 100000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 8313575087 50000000000 < ((16627150 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

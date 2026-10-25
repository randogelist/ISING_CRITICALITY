import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=10. -/
theorem q3_d10_enclosure : rat 2681001507 20000000000 < pSquare 10 ∧ pSquare 10 < rat 6702503779 50000000000 := by
  rcases root2_d10_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 10 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 1546464351 10000000000 < vB 10 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 10 < rat 1546464353 10000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 10 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 490217963 10000000000 < tB 10 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 10 < rat 122554491 2500000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 15301273 100000000 < tRatio 10 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 10 < rat 191265913 1250000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 10 := by
    have : (0 : ℝ) < rat 15301273 100000000 := by norm_num [rat]
    linarith
  have hr4L : (rat 15301273 100000000) ^ 4 < (tRatio 10) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 10) ^ 4 < (rat 191265913 1250000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((9 : ℝ) / 2) := by norm_num
  have hdL : rat 2500439 2500000000 < deltaSquare 10 := by
    change rat 2500439 2500000000 < ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 10) ^ 4
    have h0 : rat 2500439 2500000000 < ((9 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 15301273 100000000) ^ 4 := by
      norm_num [rat]
    have h1 : ((9 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 15301273 100000000) ^ 4 <
        ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 15301273 100000000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 15301273 100000000) ^ 4 <
        ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 10) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 10 < rat 10001757 10000000000 := by
    change ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 10) ^ 4 < rat 10001757 10000000000
    have h1 : ((9 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 10) ^ 4 <
        ((9 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 10) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((9 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((9 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 10) ^ 4 <
        ((9 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 191265913 1250000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((9 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 191265913 1250000000) ^ 4 < rat 10001757 10000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 10010006759 10000000000 < Real.exp (rat 2500439 2500000000) := by
    calc
      rat 10010006759 10000000000 < ∑ m ∈ Finset.range 7, (rat 2500439 2500000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 2500439 2500000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 10001757 10000000000) < rat 10010006761 10000000000 := by
    calc
      Real.exp (rat 10001757 10000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 10001757 10000000000) ^ m / m.factorial) +
            (rat 10001757 10000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 10010006761 10000000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 10010006759 10000000000 < Real.exp (deltaSquare 10) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 10) < rat 10010006761 10000000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 10 := by
    have : (0 : ℝ) < rat 1546464351 10000000000 := by norm_num [rat]
    linarith
  have hvsL : rat 77400593 500000000 < vSquare 10 := by
    unfold vSquare
    have h0 : rat 77400593 500000000 < (rat 1546464351 10000000000) * (rat 10010006759 10000000000) := by norm_num [rat]
    have h1 : (rat 1546464351 10000000000) * (rat 10010006759 10000000000) < vB 10 * (rat 10010006759 10000000000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 10 * (rat 10010006759 10000000000) < vB 10 * Real.exp (deltaSquare 10) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 10 < rat 1548011863 10000000000 := by
    unfold vSquare
    have h1 : vB 10 * Real.exp (deltaSquare 10) < vB 10 * (rat 10010006761 10000000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 10 * (rat 10010006761 10000000000) < (rat 1546464353 10000000000) * (rat 10010006761 10000000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 1546464353 10000000000) * (rat 10010006761 10000000000) < rat 1548011863 10000000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 10 := by
    have : (0 : ℝ) < rat 77400593 500000000 := by norm_num [rat]
    linarith
  have hpL : rat 2681001507 20000000000 < pSquare 10 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 10)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 10 < rat 6702503779 50000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 10)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=10 rounds to 8 decimals. -/
theorem q3_d10_rounds8 : roundsTo8Real (pSquare 10) 13405008 := by
  rcases q3_d10_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((13405008 : ℝ) / 100000000 - 1 / 200000000) < rat 2681001507 20000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 6702503779 50000000000 < ((13405008 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

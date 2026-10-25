import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=5. -/
theorem q3_d5_enclosure : rat 26065060823 100000000000 < pSquare 5 ∧ pSquare 5 < rat 26065060841 100000000000 := by
  rcases root2_d5_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 5 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 3493435161 10000000000 < vB 5 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 5 < rat 1746717581 5000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 5 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 521510431 5000000000 < tB 5 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 5 < rat 1043020863 10000000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 1627801117 5000000000 < tRatio 5 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 5 < rat 3255602239 10000000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 5 := by
    have : (0 : ℝ) < rat 1627801117 5000000000 := by norm_num [rat]
    linarith
  have hr4L : (rat 1627801117 5000000000) ^ 4 < (tRatio 5) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 5) ^ 4 < (rat 3255602239 10000000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((4 : ℝ) / 2) := by norm_num
  have hdL : rat 45548999 5000000000 < deltaSquare 5 := by
    change rat 45548999 5000000000 < ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 5) ^ 4
    have h0 : rat 45548999 5000000000 < ((4 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1627801117 5000000000) ^ 4 := by
      norm_num [rat]
    have h1 : ((4 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1627801117 5000000000) ^ 4 <
        ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1627801117 5000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1627801117 5000000000) ^ 4 <
        ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 5) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 5 < rat 91097999 10000000000 := by
    change ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 5) ^ 4 < rat 91097999 10000000000
    have h1 : ((4 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 5) ^ 4 <
        ((4 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 5) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((4 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((4 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 5) ^ 4 <
        ((4 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 3255602239 10000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((4 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 3255602239 10000000000) ^ 4 < rat 91097999 10000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 10091514203 10000000000 < Real.exp (rat 45548999 5000000000) := by
    calc
      rat 10091514203 10000000000 < ∑ m ∈ Finset.range 7, (rat 45548999 5000000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 45548999 5000000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 91097999 10000000000) < rat 2018302841 2000000000 := by
    calc
      Real.exp (rat 91097999 10000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 91097999 10000000000) ^ m / m.factorial) +
            (rat 91097999 10000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 2018302841 2000000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 10091514203 10000000000 < Real.exp (deltaSquare 5) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 5) < rat 2018302841 2000000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 5 := by
    have : (0 : ℝ) < rat 3493435161 10000000000 := by norm_num [rat]
    linarith
  have hvsL : rat 1762702527 5000000000 < vSquare 5 := by
    unfold vSquare
    have h0 : rat 1762702527 5000000000 < (rat 3493435161 10000000000) * (rat 10091514203 10000000000) := by norm_num [rat]
    have h1 : (rat 3493435161 10000000000) * (rat 10091514203 10000000000) < vB 5 * (rat 10091514203 10000000000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 5 * (rat 10091514203 10000000000) < vB 5 * Real.exp (deltaSquare 5) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 5 < rat 3525405057 10000000000 := by
    unfold vSquare
    have h1 : vB 5 * Real.exp (deltaSquare 5) < vB 5 * (rat 2018302841 2000000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 5 * (rat 2018302841 2000000000) < (rat 1746717581 5000000000) * (rat 2018302841 2000000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 1746717581 5000000000) * (rat 2018302841 2000000000) < rat 3525405057 10000000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 5 := by
    have : (0 : ℝ) < rat 1762702527 5000000000 := by norm_num [rat]
    linarith
  have hpL : rat 26065060823 100000000000 < pSquare 5 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 5)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 5 < rat 26065060841 100000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 5)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=5 rounds to 8 decimals. -/
theorem q3_d5_rounds8 : roundsTo8Real (pSquare 5) 26065061 := by
  rcases q3_d5_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((26065061 : ℝ) / 100000000 - 1 / 200000000) < rat 26065060823 100000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 26065060841 100000000000 < ((26065061 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

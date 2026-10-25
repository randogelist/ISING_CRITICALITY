import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=9. -/
theorem q3_d9_enclosure : rat 3710660897 25000000000 < pSquare 9 ∧ pSquare 9 < rat 14842643611 100000000000 := by
  rcases root2_d9_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 9 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 13924337 80000000 < vB 9 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 9 < rat 1740542127 10000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 9 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 274182797 5000000000 < tB 9 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 9 < rat 109673119 2000000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 1711624683 10000000000 < tRatio 9 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 9 < rat 106976543 625000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 9 := by
    have : (0 : ℝ) < rat 1711624683 10000000000 := by norm_num [rat]
    linarith
  have hr4L : (rat 1711624683 10000000000) ^ 4 < (tRatio 9) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 9) ^ 4 < (rat 106976543 625000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((8 : ℝ) / 2) := by norm_num
  have hdL : rat 13920269 10000000000 < deltaSquare 9 := by
    change rat 13920269 10000000000 < ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 9) ^ 4
    have h0 : rat 13920269 10000000000 < ((8 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1711624683 10000000000) ^ 4 := by
      norm_num [rat]
    have h1 : ((8 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 1711624683 10000000000) ^ 4 <
        ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1711624683 10000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 1711624683 10000000000) ^ 4 <
        ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 9) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 9 < rat 1392027 1000000000 := by
    change ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 9) ^ 4 < rat 1392027 1000000000
    have h1 : ((8 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 9) ^ 4 <
        ((8 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 9) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((8 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((8 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 9) ^ 4 <
        ((8 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 106976543 625000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((8 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 106976543 625000000) ^ 4 < rat 1392027 1000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 5006964981 5000000000 < Real.exp (rat 13920269 10000000000) := by
    calc
      rat 5006964981 5000000000 < ∑ m ∈ Finset.range 7, (rat 13920269 10000000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 13920269 10000000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 1392027 1000000000) < rat 2503482491 2500000000 := by
    calc
      Real.exp (rat 1392027 1000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 1392027 1000000000) ^ m / m.factorial) +
            (rat 1392027 1000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 2503482491 2500000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 5006964981 5000000000 < Real.exp (deltaSquare 9) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 9) < rat 2503482491 2500000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 9 := by
    have : (0 : ℝ) < rat 13924337 80000000 := by norm_num [rat]
    linarith
  have hvsL : rat 1742966693 10000000000 < vSquare 9 := by
    unfold vSquare
    have h0 : rat 1742966693 10000000000 < (rat 13924337 80000000) * (rat 5006964981 5000000000) := by norm_num [rat]
    have h1 : (rat 13924337 80000000) * (rat 5006964981 5000000000) < vB 9 * (rat 5006964981 5000000000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 9 * (rat 5006964981 5000000000) < vB 9 * Real.exp (deltaSquare 9) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 9 < rat 217870837 1250000000 := by
    unfold vSquare
    have h1 : vB 9 * Real.exp (deltaSquare 9) < vB 9 * (rat 2503482491 2500000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 9 * (rat 2503482491 2500000000) < (rat 1740542127 10000000000) * (rat 2503482491 2500000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 1740542127 10000000000) * (rat 2503482491 2500000000) < rat 217870837 1250000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 9 := by
    have : (0 : ℝ) < rat 1742966693 10000000000 := by norm_num [rat]
    linarith
  have hpL : rat 3710660897 25000000000 < pSquare 9 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 9)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 9 < rat 14842643611 100000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 9)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=9 rounds to 8 decimals. -/
theorem q3_d9_rounds8 : roundsTo8Real (pSquare 9) 14842644 := by
  rcases q3_d9_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((14842644 : ℝ) / 100000000 - 1 / 200000000) < rat 3710660897 25000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 14842643611 100000000000 < ((14842644 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

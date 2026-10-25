import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=7. -/
theorem q3_d7_enclosure : rat 18902489253 100000000000 < pSquare 7 ∧ pSquare 7 < rat 18902489267 100000000000 := by
  rcases root2_d7_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 7 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 1161829393 5000000000 < vB 7 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 7 < rat 2323658787 10000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 7 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 179718113 2500000000 < tB 7 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 7 < rat 718872453 10000000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 280478901 1250000000 < tRatio 7 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 7 < rat 2243831213 10000000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 7 := by
    have : (0 : ℝ) < rat 280478901 1250000000 := by norm_num [rat]
    linarith
  have hr4L : (rat 280478901 1250000000) ^ 4 < (tRatio 7) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 7) ^ 4 < (rat 2243831213 10000000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((6 : ℝ) / 2) := by norm_num
  have hdL : rat 15417199 5000000000 < deltaSquare 7 := by
    change rat 15417199 5000000000 < ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 7) ^ 4
    have h0 : rat 15417199 5000000000 < ((6 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 280478901 1250000000) ^ 4 := by
      norm_num [rat]
    have h1 : ((6 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 280478901 1250000000) ^ 4 <
        ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 280478901 1250000000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 280478901 1250000000) ^ 4 <
        ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 7) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 7 < rat 30834399 10000000000 := by
    change ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 7) ^ 4 < rat 30834399 10000000000
    have h1 : ((6 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 7) ^ 4 <
        ((6 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 7) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((6 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((6 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 7) ^ 4 <
        ((6 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 2243831213 10000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((6 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 2243831213 10000000000) ^ 4 < rat 30834399 10000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 156732531 156250000 < Real.exp (rat 15417199 5000000000) := by
    calc
      rat 156732531 156250000 < ∑ m ∈ Finset.range 7, (rat 15417199 5000000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 15417199 5000000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 30834399 10000000000) < rat 5015440993 5000000000 := by
    calc
      Real.exp (rat 30834399 10000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 30834399 10000000000) ^ m / m.factorial) +
            (rat 30834399 10000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 5015440993 5000000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 156732531 156250000 < Real.exp (deltaSquare 7) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 7) < rat 5015440993 5000000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 7 := by
    have : (0 : ℝ) < rat 1161829393 5000000000 := by norm_num [rat]
    linarith
  have hvsL : rat 466166941 2000000000 < vSquare 7 := by
    unfold vSquare
    have h0 : rat 466166941 2000000000 < (rat 1161829393 5000000000) * (rat 156732531 156250000) := by norm_num [rat]
    have h1 : (rat 1161829393 5000000000) * (rat 156732531 156250000) < vB 7 * (rat 156732531 156250000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 7 * (rat 156732531 156250000) < vB 7 * Real.exp (deltaSquare 7) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 7 < rat 2330834707 10000000000 := by
    unfold vSquare
    have h1 : vB 7 * Real.exp (deltaSquare 7) < vB 7 * (rat 5015440993 5000000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 7 * (rat 5015440993 5000000000) < (rat 2323658787 10000000000) * (rat 5015440993 5000000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 2323658787 10000000000) * (rat 5015440993 5000000000) < rat 2330834707 10000000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 7 := by
    have : (0 : ℝ) < rat 466166941 2000000000 := by norm_num [rat]
    linarith
  have hpL : rat 18902489253 100000000000 < pSquare 7 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 7)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 7 < rat 18902489267 100000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 7)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=7 rounds to 8 decimals. -/
theorem q3_d7_rounds8 : roundsTo8Real (pSquare 7) 18902489 := by
  rcases q3_d7_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((18902489 : ℝ) / 100000000 - 1 / 200000000) < rat 18902489253 100000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 18902489267 100000000000 < ((18902489 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

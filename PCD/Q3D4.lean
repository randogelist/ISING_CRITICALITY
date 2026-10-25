import PCD.Q3BaseBounds

namespace PCD

noncomputable section

/-- Rigorous rational enclosure of the q=3 square-loop formula at d=4. -/
theorem q3_d4_enclosure : rat 16116787993 50000000000 < pSquare 4 ∧ pSquare 4 < rat 3223357601 10000000000 := by
  rcases root2_d4_bounds with ⟨hxL, hxU⟩
  rcases tB2_bounds with ⟨ht2L, ht2U⟩
  rcases log_three_halves_bounds with ⟨hlogL, hlogU⟩

  have hvDen : 0 < (2 : ℝ) - root2 4 := by
    norm_num [rat] at hxU ⊢
    linarith
  have hvL : rat 4667212021 10000000000 < vB 4 := by
    unfold vB
    rw [lt_div_iff₀ hvDen]
    norm_num [rat] at hxL ⊢
    linarith
  have hvU : vB 4 < rat 4667212023 10000000000 := by
    unfold vB
    rw [div_lt_iff₀ hvDen]
    norm_num [rat] at hxU ⊢
    linarith

  have htDen : 0 < (4 : ℝ) - root2 4 := by
    norm_num [rat] at hxU ⊢
    linarith
  have htL : rat 1346289981 10000000000 < tB 4 := by
    unfold tB
    rw [lt_div_iff₀ htDen]
    norm_num [rat] at hxL ⊢
    linarith
  have htU : tB 4 < rat 673144991 5000000000 := by
    unfold tB
    rw [div_lt_iff₀ htDen]
    norm_num [rat] at hxU ⊢
    linarith

  have ht2pos : 0 < tB 2 := by
    norm_num [rat] at ht2L
    linarith
  have hrL : rat 65659411 156250000 < tRatio 4 := by
    unfold tRatio
    rw [lt_div_iff₀ ht2pos]
    norm_num [rat] at htL ht2U ⊢
    linarith
  have hrU : tRatio 4 < rat 420220231 1000000000 := by
    unfold tRatio
    rw [div_lt_iff₀ ht2pos]
    norm_num [rat] at htU ht2L ⊢
    linarith
  have hrpos : 0 < tRatio 4 := by
    have : (0 : ℝ) < rat 65659411 156250000 := by norm_num [rat]
    linarith
  have hr4L : (rat 65659411 156250000) ^ 4 < (tRatio 4) ^ 4 := by
    exact pow_lt_pow_left₀ hrL (by norm_num [rat]) (by norm_num)
  have hr4U : (tRatio 4) ^ 4 < (rat 420220231 1000000000) ^ 4 := by
    exact pow_lt_pow_left₀ hrU (le_of_lt hrpos) (by norm_num)

  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by
    have : (0 : ℝ) < rat 4054651081 10000000000 := by norm_num [rat]
    linarith
  have hcpos : 0 < ((3 : ℝ) / 2) := by norm_num
  have hdL : rat 4741247 250000000 < deltaSquare 4 := by
    change rat 4741247 250000000 < ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 4) ^ 4
    have h0 : rat 4741247 250000000 < ((3 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 65659411 156250000) ^ 4 := by
      norm_num [rat]
    have h1 : ((3 : ℝ) / 2) * (rat 4054651081 10000000000) * (rat 65659411 156250000) ^ 4 <
        ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 65659411 156250000) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogL hcpos) (by norm_num [rat])
    have hcoef : 0 < ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) := mul_pos hcpos hlogpos
    have h2 : ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (rat 65659411 156250000) ^ 4 <
        ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 4) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4L hcoef
    exact h0.trans (h1.trans h2)
  have hdU : deltaSquare 4 < rat 94824941 5000000000 := by
    change ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 4) ^ 4 < rat 94824941 5000000000
    have h1 : ((3 : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio 4) ^ 4 <
        ((3 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 4) ^ 4 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlogU hcpos) (pow_pos hrpos 4)
    have hcoefU : 0 < ((3 : ℝ) / 2) * (rat 40546510811 100000000000) := by norm_num [rat]
    have h2 : ((3 : ℝ) / 2) * (rat 40546510811 100000000000) * (tRatio 4) ^ 4 <
        ((3 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 420220231 1000000000) ^ 4 := by
      exact mul_lt_mul_of_pos_left hr4U hcoefU
    have h3 : ((3 : ℝ) / 2) * (rat 40546510811 100000000000) * (rat 420220231 1000000000) ^ 4 < rat 94824941 5000000000 := by
      norm_num [rat]
    exact h1.trans (h2.trans h3)

  have heConstL : rat 1273932457 1250000000 < Real.exp (rat 4741247 250000000) := by
    calc
      rat 1273932457 1250000000 < ∑ m ∈ Finset.range 7, (rat 4741247 250000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 4741247 250000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 7
  have heConstU : Real.exp (rat 94824941 5000000000) < rat 10191459659 10000000000 := by
    calc
      Real.exp (rat 94824941 5000000000) ≤
          (∑ m ∈ Finset.range 7, (rat 94824941 5000000000) ^ m / m.factorial) +
            (rat 94824941 5000000000) ^ 7 * (7 + 1) / (Nat.factorial 7 * 7) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < rat 10191459659 10000000000 := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  have heL : rat 1273932457 1250000000 < Real.exp (deltaSquare 4) :=
    heConstL.trans (Real.exp_strictMono hdL)
  have heU : Real.exp (deltaSquare 4) < rat 10191459659 10000000000 :=
    (Real.exp_strictMono hdU).trans heConstU

  have hvBpos : 0 < vB 4 := by
    have : (0 : ℝ) < rat 4667212021 10000000000 := by norm_num [rat]
    linarith
  have hvsL : rat 4756570301 10000000000 < vSquare 4 := by
    unfold vSquare
    have h0 : rat 4756570301 10000000000 < (rat 4667212021 10000000000) * (rat 1273932457 1250000000) := by norm_num [rat]
    have h1 : (rat 4667212021 10000000000) * (rat 1273932457 1250000000) < vB 4 * (rat 1273932457 1250000000) := by
      exact mul_lt_mul_of_pos_right hvL (by norm_num [rat])
    have h2 : vB 4 * (rat 1273932457 1250000000) < vB 4 * Real.exp (deltaSquare 4) := by
      exact mul_lt_mul_of_pos_left heL hvBpos
    exact h0.trans (h1.trans h2)
  have hvsU : vSquare 4 < rat 2378285153 5000000000 := by
    unfold vSquare
    have h1 : vB 4 * Real.exp (deltaSquare 4) < vB 4 * (rat 10191459659 10000000000) := by
      exact mul_lt_mul_of_pos_left heU hvBpos
    have h2 : vB 4 * (rat 10191459659 10000000000) < (rat 4667212023 10000000000) * (rat 10191459659 10000000000) := by
      exact mul_lt_mul_of_pos_right hvU (by norm_num [rat])
    have h3 : (rat 4667212023 10000000000) * (rat 10191459659 10000000000) < rat 2378285153 5000000000 := by norm_num [rat]
    exact h1.trans (h2.trans h3)

  have hvspos : 0 < vSquare 4 := by
    have : (0 : ℝ) < rat 4756570301 10000000000 := by norm_num [rat]
    linarith
  have hpL : rat 16116787993 50000000000 < pSquare 4 := by
    unfold pSquare
    rw [lt_div_iff₀ (by linarith : 0 < 1 + vSquare 4)]
    norm_num [rat] at hvsL ⊢
    nlinarith
  have hpU : pSquare 4 < rat 3223357601 10000000000 := by
    unfold pSquare
    rw [div_lt_iff₀ (by linarith : 0 < 1 + vSquare 4)]
    norm_num [rat] at hvsU ⊢
    nlinarith
  exact ⟨hpL, hpU⟩

/-- The analytic square-loop q=3 prediction at d=4 rounds to 8 decimals. -/
theorem q3_d4_rounds8 : roundsTo8Real (pSquare 4) 32233576 := by
  rcases q3_d4_enclosure with ⟨hL, hU⟩
  unfold roundsTo8Real
  constructor
  · exact (by norm_num [rat] :
      ((32233576 : ℝ) / 100000000 - 1 / 200000000) < rat 16116787993 50000000000).trans hL
  · exact hU.trans (by norm_num [rat] :
      rat 3223357601 10000000000 < ((32233576 : ℝ) / 100000000 + 1 / 200000000))

end
end PCD

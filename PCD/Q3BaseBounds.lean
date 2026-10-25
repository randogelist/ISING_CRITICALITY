import PCD.Q3Defs

namespace PCD

noncomputable section

theorem root2_d2_bounds :
    rat 141421356237 100000000000 < root2 2 ∧ root2 2 < rat 70710678119 50000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 141421356237 100000000000) (y := (2 : ℝ)) (z := (2 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 70710678119 50000000000) (z := (2 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d3_bounds :
    rat 125992104989 100000000000 < root2 3 ∧ root2 3 < rat 12599210499 10000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 125992104989 100000000000) (y := (2 : ℝ)) (z := (3 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 12599210499 10000000000) (z := (3 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d4_bounds :
    rat 237841423 200000000 < root2 4 ∧ root2 4 < rat 118920711501 100000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 237841423 200000000) (y := (2 : ℝ)) (z := (4 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 118920711501 100000000000) (z := (4 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d5_bounds :
    rat 114869835499 100000000000 < root2 5 ∧ root2 5 < rat 229739671 200000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 114869835499 100000000000) (y := (2 : ℝ)) (z := (5 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 229739671 200000000) (z := (5 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d6_bounds :
    rat 11224620483 10000000000 < root2 6 ∧ root2 6 < rat 112246204831 100000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 11224620483 10000000000) (y := (2 : ℝ)) (z := (6 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 112246204831 100000000000) (z := (6 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d7_bounds :
    rat 110408951367 100000000000 < root2 7 ∧ root2 7 < rat 13801118921 12500000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 110408951367 100000000000) (y := (2 : ℝ)) (z := (7 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 13801118921 12500000000) (z := (7 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d8_bounds :
    rat 54525386633 50000000000 < root2 8 ∧ root2 8 < rat 109050773267 100000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 54525386633 50000000000) (y := (2 : ℝ)) (z := (8 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 109050773267 100000000000) (z := (8 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d9_bounds :
    rat 108005973889 100000000000 < root2 9 ∧ root2 9 < rat 10800597389 10000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 108005973889 100000000000) (y := (2 : ℝ)) (z := (9 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 10800597389 10000000000) (z := (9 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d10_bounds :
    rat 107177346253 100000000000 < root2 10 ∧ root2 10 < rat 53588673127 50000000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 107177346253 100000000000) (y := (2 : ℝ)) (z := (10 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 53588673127 50000000000) (z := (10 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem root2_d11_bounds :
    rat 106504108943 100000000000 < root2 11 ∧ root2 11 < rat 6656506809 6250000000 := by
  constructor
  · unfold root2
    exact (Real.lt_rpow_inv_iff_of_pos
      (x := rat 106504108943 100000000000) (y := (2 : ℝ)) (z := (11 : ℝ))
      (by norm_num [rat]) (by norm_num) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])
  · unfold root2
    exact (Real.rpow_inv_lt_iff_of_pos
      (x := (2 : ℝ)) (y := rat 6656506809 6250000000) (z := (11 : ℝ))
      (by norm_num) (by norm_num [rat]) (by norm_num)).2 (by
        norm_num [rat, Real.rpow_natCast])

theorem log_three_halves_bounds :
    rat 4054651081 10000000000 < Real.log ((3 : ℝ) / 2) ∧
    Real.log ((3 : ℝ) / 2) < rat 40546510811 100000000000 := by
  constructor
  · apply (Real.lt_log_iff_exp_lt (x := rat 4054651081 10000000000) (y := (3 : ℝ) / 2) (by norm_num)).2
    calc
      Real.exp (rat 4054651081 10000000000) ≤
          (∑ m ∈ Finset.range 13, (rat 4054651081 10000000000) ^ m / m.factorial) +
            (rat 4054651081 10000000000) ^ 13 * (13 + 1) / (Nat.factorial 13 * 13) := by
              exact Real.exp_bound' (by norm_num [rat]) (by norm_num [rat]) (by norm_num)
      _ < (3 : ℝ) / 2 := by
              norm_num [rat, Finset.sum_range_succ, Nat.factorial]
  · apply (Real.log_lt_iff_lt_exp (x := (3 : ℝ) / 2) (y := rat 40546510811 100000000000) (by norm_num)).2
    calc
      (3 : ℝ) / 2 < ∑ m ∈ Finset.range 13, (rat 40546510811 100000000000) ^ m / m.factorial := by
        norm_num [rat, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (rat 40546510811 100000000000) := by
        exact Real.sum_le_exp_of_nonneg (by norm_num [rat]) 13

theorem tB2_bounds : rat 320377241 1000000000 < tB 2 ∧ tB 2 < rat 3203772411 10000000000 := by
  rcases root2_d2_bounds with ⟨hxL, hxU⟩
  have hden : 0 < (4 : ℝ) - root2 2 := by
    norm_num [rat] at hxU ⊢
    linarith
  constructor
  · unfold tB
    rw [lt_div_iff₀ hden]
    norm_num [rat] at hxL ⊢
    linarith
  · unfold tB
    rw [div_lt_iff₀ hden]
    norm_num [rat] at hxU ⊢
    linarith

end
end PCD

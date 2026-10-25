import PCD.Q3D3
import PCD.Q3D4
import PCD.Q3D5
import PCD.Q3D6
import PCD.Q3D7
import PCD.Q3D8
import PCD.Q3D9
import PCD.Q3D10
import PCD.Q3D11

namespace PCD

noncomputable section

theorem q3_all_d3_to_d11_round_to_8 :
    roundsTo8Real (pSquare 3) 42473310 ∧
    roundsTo8Real (pSquare 4) 32233576 ∧
    roundsTo8Real (pSquare 5) 26065061 ∧
    roundsTo8Real (pSquare 6) 21906526 ∧
    roundsTo8Real (pSquare 7) 18902489 ∧
    roundsTo8Real (pSquare 8) 16627150 ∧
    roundsTo8Real (pSquare 9) 14842644 ∧
    roundsTo8Real (pSquare 10) 13405008 ∧
    roundsTo8Real (pSquare 11) 12221782 := by
  exact ⟨q3_d3_rounds8, q3_d4_rounds8, q3_d5_rounds8, q3_d6_rounds8, q3_d7_rounds8, q3_d8_rounds8, q3_d9_rounds8, q3_d10_rounds8, q3_d11_rounds8⟩


/-- Frozen decimal table agrees with the analytic square-loop formula to nearest 1e-8. -/
theorem Q3_SQUARELOOP_8DIGIT_CERTIFIED :
    roundsTo8Real (pSquare 3) 42473310 ∧
    roundsTo8Real (pSquare 4) 32233576 ∧
    roundsTo8Real (pSquare 5) 26065061 ∧
    roundsTo8Real (pSquare 6) 21906526 ∧
    roundsTo8Real (pSquare 7) 18902489 ∧
    roundsTo8Real (pSquare 8) 16627150 ∧
    roundsTo8Real (pSquare 9) 14842644 ∧
    roundsTo8Real (pSquare 10) 13405008 ∧
    roundsTo8Real (pSquare 11) 12221782 := q3_all_d3_to_d11_round_to_8

end
end PCD

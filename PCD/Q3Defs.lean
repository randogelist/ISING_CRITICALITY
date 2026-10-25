import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Finset
open scoped BigOperators

namespace PCD

noncomputable section

/-- Exact rational cast helper used by all certificates. -/
def rat (n d : Nat) : ℝ := (n : ℝ) / (d : ℝ)

/-- The real d-th root of 2 used by the q=3 Bethe/coexistence expression. -/
def root2 (d : Nat) : ℝ := (2 : ℝ) ^ ((d : ℝ)⁻¹)

/-- q=3 Bethe-like bond variable as a function of dimension. -/
def vB (d : Nat) : ℝ :=
  2 * (root2 d - 1) / (2 - root2 d)

/-- Simplified t(v_B,3)=v_B/(3+v_B). -/
def tB (d : Nat) : ℝ :=
  2 * (root2 d - 1) / (4 - root2 d)

/-- Ratio to the exactly anchored d=2 row. -/
def tRatio (d : Nat) : ℝ := tB d / tB 2

/-- Square-loop exponent for q=3. -/
def deltaSquare (d : Nat) : ℝ :=
  (((d - 1 : Nat) : ℝ) / 2) * Real.log ((3 : ℝ) / 2) * (tRatio d) ^ 4

/-- Square-loop corrected v variable. -/
def vSquare (d : Nat) : ℝ :=
  vB d * Real.exp (deltaSquare d)

/-- The q=3 square-loop coexistence prediction in FK p-coordinates. -/
def pSquare (d : Nat) : ℝ :=
  vSquare d / (1 + vSquare d)

/-- Nearest rounding at 8 decimals, stated as the open half-unit interval. -/
def roundsTo8Real (x : ℝ) (display : Nat) : Prop :=
  (display : ℝ) / 100000000 - 1 / 200000000 < x ∧
  x < (display : ℝ) / 100000000 + 1 / 200000000

end
end PCD

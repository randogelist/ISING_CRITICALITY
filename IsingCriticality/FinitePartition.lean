import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite Potts objects and the FK probability coordinate

This file proves finite algebraic identities.  It does not identify the
square-loop approximation with an infinite-volume critical threshold.
-/

namespace IsingCriticality

noncomputable section

/-- The FK probability corresponding to a nonnegative bond activity. -/
def probabilityOfActivity (v : ℝ) : ℝ := v / (1 + v)

/-- The inverse odds coordinate, on probabilities below one. -/
def activityOfProbability (p : ℝ) : ℝ := p / (1 - p)

theorem probabilityOfActivity_mem_Ico {v : ℝ} (hv : 0 ≤ v) :
    probabilityOfActivity v ∈ Set.Ico (0 : ℝ) 1 := by
  have hd : 0 < 1 + v := by linarith
  constructor
  · exact div_nonneg hv (le_of_lt hd)
  · exact (div_lt_one hd).2 (by linarith)

theorem probabilityOfActivity_pos {v : ℝ} (hv : 0 < v) :
    0 < probabilityOfActivity v := by
  exact div_pos hv (by linarith)

theorem probabilityOfActivity_strictMonoOn :
    StrictMonoOn probabilityOfActivity (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  change a / (1 + a) < b / (1 + b)
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + a)
    (by linarith : 0 < 1 + b)).2
  nlinarith

theorem activity_probability_inverse {v : ℝ} (hv : 0 ≤ v) :
    activityOfProbability (probabilityOfActivity v) = v := by
  have h : 1 + v ≠ 0 := by linarith
  unfold activityOfProbability probabilityOfActivity
  field_simp
  ring

theorem probability_activity_inverse {p : ℝ} (hp : p < 1) :
    probabilityOfActivity (activityOfProbability p) = p := by
  have h : 1 - p ≠ 0 := by linarith
  unfold activityOfProbability probabilityOfActivity
  field_simp
  ring

/-- Exact conversion from the Potts coupling K, where v = exp K - 1. -/
theorem probability_exp_activity (K : ℝ) :
    probabilityOfActivity (Real.exp K - 1) = 1 - Real.exp (-K) := by
  rw [probabilityOfActivity, Real.exp_neg]
  have h : Real.exp K ≠ 0 := ne_of_gt (Real.exp_pos K)
  field_simp
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact finite spin partition polynomial, with natural coefficients.
Supply each undirected edge once in `edges`. -/
def pottsPartitionPolynomial (edges : Finset (V × V)) (q : ℕ) : Polynomial ℕ :=
  ∑ σ : V → Fin q, ∏ e ∈ edges,
    if σ e.1 = σ e.2 then (1 + Polynomial.X) else 1

/-- The same exact finite partition function evaluated at a real activity. -/
def pottsPartition (edges : Finset (V × V)) (q : ℕ) (v : ℝ) : ℝ :=
  ∑ σ : V → Fin q, ∏ e ∈ edges, if σ e.1 = σ e.2 then (1 + v) else 1

theorem evaluate_pottsPartitionPolynomial (edges : Finset (V × V))
    (q : ℕ) (v : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) v (pottsPartitionPolynomial edges q) =
      pottsPartition edges q v := by
  change (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) v)
    (pottsPartitionPolynomial edges q) = _
  simp [pottsPartitionPolynomial, pottsPartition, map_sum, map_prod, apply_ite]

/-- Exact spin formulation with Boltzmann factor exp K per agreeing edge. -/
def pottsBoltzmannPartition (edges : Finset (V × V)) (q : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : V → Fin q, ∏ e ∈ edges, Real.exp (if σ e.1 = σ e.2 then K else 0)

theorem pottsPartition_eq_boltzmann (edges : Finset (V × V))
    (q : ℕ) (K : ℝ) :
    pottsPartition edges q (Real.exp K - 1) = pottsBoltzmannPartition edges q K := by
  unfold pottsPartition pottsBoltzmannPartition
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> simp

theorem pottsPartition_pos (edges : Finset (V × V))
    {q : ℕ} (hq : 0 < q) {v : ℝ} (hv : 0 ≤ v) :
    0 < pottsPartition edges q v := by
  let σ₀ : V → Fin q := fun _ => ⟨0, hq⟩
  unfold pottsPartition
  apply Finset.sum_pos'
  · intro σ _
    apply Finset.prod_nonneg
    intro e _
    split_ifs <;> linarith
  · refine ⟨σ₀, Finset.mem_univ _, ?_⟩
    apply Finset.prod_pos
    intro e _
    split_ifs <;> linarith

/-- A spin-summed polynomial in the FK probability coordinate.  Expanding
the product selects open edges and enforces equal colors on each of them. -/
def probabilityPartition (edges : Finset (V × V)) (q : ℕ) (p : ℝ) : ℝ :=
  ∑ σ : V → Fin q, ∏ e ∈ edges,
    ((1 - p) + p * (if σ e.1 = σ e.2 then 1 else 0))

/-- Finite normalization identity, independent of any thermodynamic limit. -/
theorem probabilityPartition_eq_activity (edges : Finset (V × V))
    (q : ℕ) {p : ℝ} (hp : p < 1) :
    probabilityPartition edges q p =
      (1 - p) ^ edges.card * pottsPartition edges q (activityOfProbability p) := by
  have hd : 1 - p ≠ 0 := by linarith
  unfold probabilityPartition pottsPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  unfold activityOfProbability
  split_ifs
  · field_simp
  · simp

/-- Vertices of an actual finite hypercubic box. -/
abbrev BoxVertex (d side : ℕ) := Fin d → Fin side

/-- Positively oriented nearest-neighbor edges: each undirected edge occurs once. -/
def boxEdges (d side : ℕ) : Finset (BoxVertex d side × BoxVertex d side) :=
  Finset.univ.filter fun e => ∃ i : Fin d,
    (e.2 i).val = (e.1 i).val + 1 ∧ ∀ j : Fin d, j ≠ i → e.2 j = e.1 j

/-- A concrete finite hypercubic Potts partition polynomial. -/
def boxPartitionPolynomial (d side q : ℕ) : Polynomial ℕ :=
  pottsPartitionPolynomial (boxEdges d side) q

theorem evaluate_boxPartitionPolynomial (d side q : ℕ) (v : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) v (boxPartitionPolynomial d side q) =
      pottsPartition (boxEdges d side) q v :=
  evaluate_pottsPartitionPolynomial (boxEdges d side) q v

/-- A finite spin partition sum restricted to an explicit set of assignments. -/
def restrictedPartition (edges : Finset (V × V)) {q : ℕ}
    (states : Finset (V → Fin q)) (v : ℝ) : ℝ :=
  ∑ σ ∈ states, ∏ e ∈ edges, if σ e.1 = σ e.2 then (1 + v) else 1

def restrictedPartitionPolynomial (edges : Finset (V × V)) {q : ℕ}
    (states : Finset (V → Fin q)) : Polynomial ℕ :=
  ∑ σ ∈ states, ∏ e ∈ edges,
    if σ e.1 = σ e.2 then (1 + Polynomial.X) else 1

omit [Fintype V] [DecidableEq V] in
theorem evaluate_restrictedPartitionPolynomial (edges : Finset (V × V))
    {q : ℕ} (states : Finset (V → Fin q)) (v : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) v (restrictedPartitionPolynomial edges states) =
      restrictedPartition edges states v := by
  change (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) v)
    (restrictedPartitionPolynomial edges states) = _
  simp [restrictedPartitionPolynomial, restrictedPartition, map_sum, map_prod, apply_ite]

omit [Fintype V] [DecidableEq V] in
theorem restrictedPartition_pos (edges : Finset (V × V)) {q : ℕ}
    (states : Finset (V → Fin q)) (hs : states.Nonempty) {v : ℝ} (hv : 0 ≤ v) :
    0 < restrictedPartition edges states v := by
  unfold restrictedPartition
  apply Finset.sum_pos'
  · intro σ _
    apply Finset.prod_nonneg
    intro e _
    split_ifs <;> linarith
  · obtain ⟨σ, hσ⟩ := hs
    refine ⟨σ, hσ, ?_⟩
    apply Finset.prod_pos
    intro e _
    split_ifs <;> linarith

/-- Boundary vertices of the box with side 2R+1. -/
def OnBoxBoundary (d R : ℕ) (x : BoxVertex d (2 * R + 1)) : Prop :=
  ∃ i : Fin d, (x i).val = 0 ∨ (x i).val = 2 * R

/-- The center of the box, in coordinates 0,...,2R. -/
def boxCenter (d R : ℕ) : BoxVertex d (2 * R + 1) :=
  fun _ => ⟨R, by omega⟩

/-- Fixed-color (wired-spin) boundary assignments. -/
def wiredStates (d R q : ℕ) : Finset (BoxVertex d (2 * R + 1) → Fin q) := by
  classical
  exact Finset.univ.filter fun σ => ∀ x, OnBoxBoundary d R x → (σ x).val = 0

/-- Those fixed-boundary assignments whose center also has color zero. -/
def wiredCenterStates (d R q : ℕ) : Finset (BoxVertex d (2 * R + 1) → Fin q) :=
  (wiredStates d R q).filter fun σ => (σ (boxCenter d R)).val = 0

theorem wiredStates_nonempty (d R : ℕ) {q : ℕ} (hq : 0 < q) :
    (wiredStates d R q).Nonempty := by
  refine ⟨fun _ => ⟨0, hq⟩, ?_⟩
  simp [wiredStates]

def wiredPartitionPolynomial (d R q : ℕ) : Polynomial ℕ :=
  restrictedPartitionPolynomial (boxEdges d (2 * R + 1)) (wiredStates d R q)

def wiredCenterPolynomial (d R q : ℕ) : Polynomial ℕ :=
  restrictedPartitionPolynomial (boxEdges d (2 * R + 1)) (wiredCenterStates d R q)

def wiredPartition (d R q : ℕ) (v : ℝ) : ℝ :=
  restrictedPartition (boxEdges d (2 * R + 1)) (wiredStates d R q) v

def wiredCenterPartition (d R q : ℕ) (v : ℝ) : ℝ :=
  restrictedPartition (boxEdges d (2 * R + 1)) (wiredCenterStates d R q) v

theorem evaluate_wiredPartitionPolynomial (d R q : ℕ) (v : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) v (wiredPartitionPolynomial d R q) =
      wiredPartition d R q v :=
  evaluate_restrictedPartitionPolynomial _ _ _

theorem evaluate_wiredCenterPolynomial (d R q : ℕ) (v : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) v (wiredCenterPolynomial d R q) =
      wiredCenterPartition d R q v :=
  evaluate_restrictedPartitionPolynomial _ _ _

theorem wiredPartition_pos (d R : ℕ) {q : ℕ} (hq : 0 < q)
    {v : ℝ} (hv : 0 ≤ v) : 0 < wiredPartition d R q v :=
  restrictedPartition_pos _ _ (wiredStates_nonempty d R hq) hv

/-- Normalized center magnetization in the exact finite wired-spin model.
The Edwards–Sokal identification with FK connectivity is not asserted here. -/
def wiredMagnetization (d R q : ℕ) (v : ℝ) : ℝ :=
  ((q : ℝ) * wiredCenterPartition d R q v / wiredPartition d R q v - 1) /
    ((q : ℝ) - 1)

/-- The exact rational target equation with all denominators cleared. -/
theorem wiredMagnetization_root_iff (d R : ℕ) {q : ℕ} (hq : 1 < q)
    {v : ℝ} (hv : 0 ≤ v) :
    wiredMagnetization d R q v = 1 / ((R : ℝ) + 1) ↔
      ((R : ℝ) + 1) * (q : ℝ) * wiredCenterPartition d R q v =
        ((R : ℝ) + q) * wiredPartition d R q v := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : 0 < q := by omega
  have hz : wiredPartition d R q v ≠ 0 := ne_of_gt (wiredPartition_pos d R hq0 hv)
  have hd : (q : ℝ) - 1 ≠ 0 := by linarith
  have hr : (R : ℝ) + 1 ≠ 0 := by positivity
  unfold wiredMagnetization
  field_simp
  constructor <;> intro h <;> nlinarith

/-- Finite spin partition function in the disagreement-weight gauge.
Unlike p/(1-p), this polynomial definition also works at p=1. -/
def restrictedProbabilityPartition (edges : Finset (V × V)) {q : ℕ}
    (states : Finset (V → Fin q)) (p : ℝ) : ℝ :=
  ∑ σ ∈ states, ∏ e ∈ edges, if σ e.1 = σ e.2 then 1 else (1 - p)

def wiredProbabilityPartition (d R q : ℕ) (p : ℝ) : ℝ :=
  restrictedProbabilityPartition (boxEdges d (2 * R + 1)) (wiredStates d R q) p

def wiredProbabilityCenterPartition (d R q : ℕ) (p : ℝ) : ℝ :=
  restrictedProbabilityPartition (boxEdges d (2 * R + 1)) (wiredCenterStates d R q) p

theorem wiredProbabilityPartition_pos (d R : ℕ) {q : ℕ} (hq : 0 < q)
    {p : ℝ} (hp : p ≤ 1) : 0 < wiredProbabilityPartition d R q p := by
  unfold wiredProbabilityPartition restrictedProbabilityPartition
  apply Finset.sum_pos'
  · intro σ _
    apply Finset.prod_nonneg
    intro e _
    split_ifs <;> linarith
  · refine ⟨fun _ => ⟨0, hq⟩, ?_, ?_⟩
    · simp [wiredStates]
    · simp

/-- The concrete finite wired-spin observable used by the C++ enumerator.
Identification with the FK center-to-boundary probability is a separate theorem. -/
def wiredObservable (d R q : ℕ) (p : ℝ) : ℝ :=
  ((q : ℝ) * wiredProbabilityCenterPartition d R q p /
    wiredProbabilityPartition d R q p - 1) / ((q : ℝ) - 1)

omit [Fintype V] [DecidableEq V] in
theorem restrictedProbabilityPartition_eq_activity (edges : Finset (V × V))
    {q : ℕ} (states : Finset (V → Fin q)) {p : ℝ} (hp : p < 1) :
    restrictedProbabilityPartition edges states p =
      (1 - p) ^ edges.card * restrictedPartition edges states (activityOfProbability p) := by
  have hd : 1 - p ≠ 0 := by linarith
  unfold restrictedProbabilityPartition restrictedPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  unfold activityOfProbability
  split_ifs
  · field_simp
    ring
  · simp

theorem wiredObservable_eq_activity (d R q : ℕ) {p : ℝ} (hp : p < 1) :
    wiredObservable d R q p = wiredMagnetization d R q (activityOfProbability p) := by
  have hd : (1 - p) ^ (boxEdges d (2 * R + 1)).card ≠ 0 :=
    pow_ne_zero _ (by linarith)
  unfold wiredObservable wiredProbabilityCenterPartition wiredProbabilityPartition
  rw [restrictedProbabilityPartition_eq_activity _ _ hp,
      restrictedProbabilityPartition_eq_activity _ _ hp]
  unfold wiredMagnetization wiredCenterPartition wiredPartition
  rw [← mul_assoc, mul_comm (q : ℝ) ((1 - p) ^ _), mul_assoc, mul_div_mul_left _ _ hd]

end

end IsingCriticality

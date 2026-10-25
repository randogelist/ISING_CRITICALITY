import IsingCriticality.FinitePartition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Conditional identification by finite-volume roots

The theorems in this module expose every analytic hypothesis. They do not assert
that the hypotheses hold for the physical infinite-volume random-cluster model,
and do not identify the square-loop estimator with its physical threshold.
-/

open Filter Topology

namespace IsingCriticality

noncomputable section

/-- The physical-style infimum definition, for a supplied one-arm function. -/
def pcInf (theta : ℝ → ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ 0 < theta p}

private theorem positiveSet_bddBelow (theta : ℝ → ℝ) :
    BddBelow {p : ℝ | p ∈ Set.Icc 0 1 ∧ 0 < theta p} :=
  ⟨0, fun _ hp => hp.1.1⟩

/-- Every positive-percolation point bounds the infimum from above. -/
theorem pcInf_le_of_positive (theta : ℝ → ℝ) {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) (ht : 0 < theta p) : pcInf theta ≤ p :=
  csInf_le (positiveSet_bddBelow theta) ⟨hp, ht⟩

/-- Nonnegative one-arm probability must vanish strictly below the infimum. -/
theorem theta_zero_below_pcInf (theta : ℝ → ℝ) {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) (ht : 0 ≤ theta p) (hpc : p < pcInf theta) :
    theta p = 0 := by
  by_contra hne
  have htpos : 0 < theta p := lt_of_le_of_ne ht (Ne.symm hne)
  exact (not_le_of_gt hpc) (pcInf_le_of_positive theta hp htpos)

/-- Monotonicity makes every point strictly above the infimum supercritical. -/
theorem theta_positive_above_pcInf (theta : ℝ → ℝ)
    (hmono : MonotoneOn theta (Set.Icc 0 1))
    (hne : {p : ℝ | p ∈ Set.Icc 0 1 ∧ 0 < theta p}.Nonempty)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (hpc : pcInf theta < p) :
    0 < theta p := by
  obtain ⟨a, ha, hap⟩ := (csInf_lt_iff (positiveSet_bddBelow theta) hne).mp hpc
  exact lt_of_lt_of_le ha.2 (hmono ha.1 hp hap.le)

/-- General crossing argument: finite roots converge when all points on either
side of `pc` eventually lie on the corresponding side of the root level. -/
theorem crossingRoots_tendsto
    (W : ℕ → ℝ → ℝ) (r level : ℕ → ℝ) (pc : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hmono : ∀ n, MonotoneOn (W n) (Set.Icc 0 1))
    (hroot : ∀ n, W n (r n) = level n)
    (hsub : ∀ p : ℝ, 0 < p → p < pc →
      ∀ᶠ n in atTop, W n p < level n)
    (hsuper : ∀ p : ℝ, pc < p → p < 1 →
      ∀ᶠ n in atTop, level n < W n p) :
    Tendsto r atTop (𝓝 pc) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha0 (hr n).1)
    · have ha0' : 0 ≤ a := le_of_not_gt ha0
      let p : ℝ := (a + pc) / 2
      have hap : a < p := by dsimp [p]; linarith
      have hp0 : 0 < p := lt_of_le_of_lt ha0' hap
      have hppc : p < pc := by dsimp [p]; linarith
      have hp : p ∈ Set.Icc 0 1 := ⟨hp0.le, (lt_trans hppc hpc1).le⟩
      filter_upwards [hsub p hp0 hppc] with n hn
      have hpr : p < r n := by
        by_contra h
        have hw := hmono n (hr n) hp (le_of_not_gt h)
        rw [hroot n] at hw
        exact (not_le_of_gt hn) hw
      exact lt_trans hap hpr
  · intro b hb
    by_cases hb1 : 1 < b
    · exact Filter.Eventually.of_forall (fun n => lt_of_le_of_lt (hr n).2 hb1)
    · have hb1' : b ≤ 1 := le_of_not_gt hb1
      let p : ℝ := (b + pc) / 2
      have hpcp : pc < p := by dsimp [p]; linarith
      have hpb : p < b := by dsimp [p]; linarith
      have hp1 : p < 1 := lt_of_lt_of_le hpb hb1'
      have hp : p ∈ Set.Icc 0 1 := ⟨(lt_trans hpc0 hpcp).le, hp1.le⟩
      filter_upwards [hsuper p hpcp hp1] with n hn
      have hrp : r n < p := by
        by_contra h
        have hw := hmono n hp (hr n) (le_of_not_gt h)
        rw [hroot n] at hw
        exact (not_le_of_gt hn) hw
      exact lt_trans hrp hpb

/-- The shrinking target used by the PCD finite-root construction. -/
def rootLevel (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- A continuous finite-volume crossing function with endpoints 0 and 1
has a root at every PCD level. The analytic inputs remain explicit. -/
theorem finiteRoot_exists (f : ℝ → ℝ) (n : ℕ)
    (hcont : ContinuousOn f (Set.Icc 0 1)) (hzero : f 0 = 0) (hone : f 1 = 1) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, f r = rootLevel n := by
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hlevel : rootLevel n ∈ Set.Icc (f 0) (f 1) := by
    rw [hzero, hone]
    constructor
    · exact (one_div_pos.mpr hd).le
    · dsimp [rootLevel]
      apply (div_le_iff₀ hd).mpr
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hlevel

/-- Strict monotonicity supplies uniqueness of the finite root. -/
theorem finiteRoot_unique (f : ℝ → ℝ) (n : ℕ)
    (hmono : StrictMonoOn f (Set.Icc 0 1)) {r s : ℝ}
    (hr : r ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1)
    (hrf : f r = rootLevel n) (hsf : f s = rootLevel n) : r = s := by
  exact hmono.injOn hr hs (hrf.trans hsf.symm)

/-- A quadratic subcritical upper bound eventually lies below the root level.
The statement does not require a known value of the decay constant. -/
theorem quadratic_bound_eventually_below (f : ℕ → ℝ) (K : ℝ)
    (hbound : ∀ᶠ n in atTop, f n ≤ K / ((n : ℝ) + 2) ^ 2) :
    ∀ᶠ n in atTop, f n < rootLevel n := by
  obtain ⟨N, hN⟩ := exists_nat_gt K
  filter_upwards [hbound, eventually_ge_atTop N] with n hn hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hKd : K < (n : ℝ) + 2 := by linarith
  apply lt_of_le_of_lt hn
  dsimp [rootLevel]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hd) hd).2
  nlinarith [mul_lt_mul_of_pos_right hKd hd]

/-- A uniform positive lower bound eventually lies above the root level. -/
theorem positive_bound_eventually_above (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, c ≤ f n) :
    ∀ᶠ n in atTop, rootLevel n < f n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  filter_upwards [hbound, eventually_ge_atTop N] with n hn hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hinv : 1 / c < (n : ℝ) + 2 := by linarith
  have hprod : 1 < ((n : ℝ) + 2) * c := (div_lt_iff₀ hc).mp hinv
  apply lt_of_lt_of_le _ hn
  exact (div_lt_iff₀ hd).mpr (by nlinarith)

/-- Conditional identification of the finite-root limit with a given `pc`.

To instantiate this with FK data one must still prove finite-root existence,
monotonicity, subcritical decay, and a positive supercritical lower bound for the
actual wired finite-box probabilities. No such facts are postulated as axioms.
-/
theorem finiteRoots_tendsto_of_decay
    (W : ℕ → ℝ → ℝ) (r : ℕ → ℝ) (pc : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hmono : ∀ n, MonotoneOn (W n) (Set.Icc 0 1))
    (hroot : ∀ n, W n (r n) = rootLevel n)
    (hsub : ∀ p : ℝ, 0 < p → p < pc → ∃ K : ℝ,
      ∀ᶠ n in atTop, W n p ≤ K / ((n : ℝ) + 2) ^ 2)
    (hsuper : ∀ p : ℝ, pc < p → p < 1 → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop, c ≤ W n p) :
    Tendsto r atTop (𝓝 pc) := by
  apply crossingRoots_tendsto W r rootLevel pc hpc0 hpc1 hr hmono hroot
  · intro p hp0 hppc
    obtain ⟨K, hK⟩ := hsub p hp0 hppc
    exact quadratic_bound_eventually_below (fun n => W n p) K hK
  · intro p hpcp hp1
    obtain ⟨c, hc, hbound⟩ := hsuper p hpcp hp1
    exact positive_bound_eventually_above (fun n => W n p) c hc hbound

/-- The finite-root limit equals the infimum-defined threshold, conditional on
explicit properties of the supplied finite and infinite-volume probabilities.
The supercritical crossing condition is derived, rather than assumed separately.
-/
theorem finiteRoots_tendsto_pcInf
    (W : ℕ → ℝ → ℝ) (theta : ℝ → ℝ) (r : ℕ → ℝ)
    (htmono : MonotoneOn theta (Set.Icc 0 1))
    (hne : {p : ℝ | p ∈ Set.Icc 0 1 ∧ 0 < theta p}.Nonempty)
    (hpc0 : 0 < pcInf theta) (hpc1 : pcInf theta < 1)
    (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hmono : ∀ n, MonotoneOn (W n) (Set.Icc 0 1))
    (hroot : ∀ n, W n (r n) = rootLevel n)
    (hsub : ∀ p : ℝ, 0 < p → p < pcInf theta → ∃ K : ℝ,
      ∀ᶠ n in atTop, W n p ≤ K / ((n : ℝ) + 2) ^ 2)
    (hfinite : ∀ n p, p ∈ Set.Icc 0 1 → theta p ≤ W n p) :
    Tendsto r atTop (𝓝 (pcInf theta)) := by
  apply finiteRoots_tendsto_of_decay W r (pcInf theta) hpc0 hpc1 hr hmono hroot hsub
  intro p hpcp hp1
  have hp : p ∈ Set.Icc 0 1 := ⟨(lt_trans hpc0 hpcp).le, hp1.le⟩
  refine ⟨theta p, theta_positive_above_pcInf theta htmono hne hp hpcp, ?_⟩
  exact Filter.Eventually.of_forall (fun n => hfinite n p hp)

/-- Infimum over the explicitly defined finite-box wired spin observables.
Identifying this object with an infinite-volume FK probability is a separate
Edwards–Sokal/thermodynamic-limit obligation, not an axiom in this file. -/
def wiredInfiniteObservable (d q : ℕ) (p : ℝ) : ℝ :=
  ⨅ n : ℕ, wiredObservable d (n + 1) q p

/-- Infimum-defined threshold of the concrete wired spin observable. -/
def wiredCriticalPoint (d q : ℕ) : ℝ := pcInf (wiredInfiniteObservable d q)

private theorem wiredValues_bddBelow (d q : ℕ) (p : ℝ)
    (hnonneg : ∀ n : ℕ, 0 ≤ wiredObservable d (n + 1) q p) :
    BddBelow (Set.range (fun n : ℕ => wiredObservable d (n + 1) q p)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hnonneg n

/-- The infimum observable is below every finite-box observable. -/
theorem wiredInfiniteObservable_le (d q n : ℕ) (p : ℝ)
    (hnonneg : ∀ m : ℕ, 0 ≤ wiredObservable d (m + 1) q p) :
    wiredInfiniteObservable d q p ≤ wiredObservable d (n + 1) q p :=
  ciInf_le (wiredValues_bddBelow d q p hnonneg) n

/-- Positivity of finite observables propagates to their infimum. -/
theorem wiredInfiniteObservable_nonneg (d q : ℕ) (p : ℝ)
    (hnonneg : ∀ n : ℕ, 0 ≤ wiredObservable d (n + 1) q p) :
    0 ≤ wiredInfiniteObservable d q p :=
  le_ciInf hnonneg

/-- Monotonicity in p propagates from finite boxes to the infimum observable. -/
theorem wiredInfiniteObservable_monotone (d q : ℕ)
    (hnonneg : ∀ n p, p ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ wiredObservable d (n + 1) q p)
    (hmono : ∀ n : ℕ, MonotoneOn (wiredObservable d (n + 1) q) (Set.Icc 0 1)) :
    MonotoneOn (wiredInfiniteObservable d q) (Set.Icc 0 1) := by
  intro a ha b hb hab
  exact ciInf_mono (wiredValues_bddBelow d q a (fun n => hnonneg n a ha))
    (fun n => hmono n ha hb hab)

/-- Concrete finite-box root identification. This theorem is conditional on
finite-box positivity/monotonicity, the displayed root equations, and a genuine
subcritical decay estimate. It gives no equality for the square-loop estimator.
For the FK interpretation, q ≥ 2 and the Edwards–Sokal bridge must be supplied.
-/
theorem concreteWiredRoots_tendsto
    (d q : ℕ) (r : ℕ → ℝ)
    (hnonneg : ∀ n p, p ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ wiredObservable d (n + 1) q p)
    (hmono : ∀ n : ℕ, MonotoneOn (wiredObservable d (n + 1) q) (Set.Icc 0 1))
    (hne : {p : ℝ | p ∈ Set.Icc 0 1 ∧ 0 < wiredInfiniteObservable d q p}.Nonempty)
    (hpc0 : 0 < wiredCriticalPoint d q) (hpc1 : wiredCriticalPoint d q < 1)
    (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hroot : ∀ n, wiredObservable d (n + 1) q (r n) = rootLevel n)
    (hsub : ∀ p : ℝ, 0 < p → p < wiredCriticalPoint d q → ∃ K : ℝ,
      ∀ᶠ n in atTop, wiredObservable d (n + 1) q p ≤ K / ((n : ℝ) + 2) ^ 2) :
    Tendsto r atTop (𝓝 (wiredCriticalPoint d q)) := by
  apply finiteRoots_tendsto_pcInf
    (fun n => wiredObservable d (n + 1) q) (wiredInfiniteObservable d q) r
    (wiredInfiniteObservable_monotone d q hnonneg hmono) hne hpc0 hpc1 hr hmono hroot hsub
  intro n p hp
  exact wiredInfiniteObservable_le d q n p (fun m => hnonneg m p hp)

/-- A canonical numerical object: the infimum of the exact finite-box root set.
This definition contains no proof fields and does not use benchmark data.
Under the hypotheses of `canonicalWiredRoot_spec`, the root set is a singleton.
-/
def canonicalWiredRoot (d q n : ℕ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧
    wiredObservable d (n + 1) q p = rootLevel n}

/-- The canonical root is the unique finite-volume root when the supplied
finite observable is continuous, strictly increasing, and has endpoints 0,1. -/
theorem canonicalWiredRoot_spec (d q n : ℕ)
    (hcont : ContinuousOn (wiredObservable d (n + 1) q) (Set.Icc 0 1))
    (hzero : wiredObservable d (n + 1) q 0 = 0)
    (hone : wiredObservable d (n + 1) q 1 = 1)
    (hstrict : StrictMonoOn (wiredObservable d (n + 1) q) (Set.Icc 0 1)) :
    canonicalWiredRoot d q n ∈ Set.Icc (0 : ℝ) 1 ∧
      wiredObservable d (n + 1) q (canonicalWiredRoot d q n) = rootLevel n := by
  obtain ⟨r, hr, hrf⟩ := finiteRoot_exists (wiredObservable d (n + 1) q) n hcont hzero hone
  have hset : {p : ℝ | p ∈ Set.Icc 0 1 ∧
      wiredObservable d (n + 1) q p = rootLevel n} = {r} := by
    ext p
    constructor
    · intro hp
      exact Set.mem_singleton_iff.mpr
        (finiteRoot_unique (wiredObservable d (n + 1) q) n hstrict hp.1 hr hp.2 hrf)
    · intro hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact ⟨hr, hrf⟩
  have heq : canonicalWiredRoot d q n = r := by
    simp only [canonicalWiredRoot, hset, csInf_singleton]
  rw [heq]
  exact ⟨hr, hrf⟩

/-- Final concrete conditional identification: a canonically defined finite
root sequence converges to the canonically defined infimum threshold.

All finite structural and subcritical analytic assumptions are explicit. No
claim is made that these hypotheses, or the FK interpretation, have already
been proved for this implementation. No estimator/benchmark is an input.
-/
theorem canonicalWiredRoots_tendsto (d q : ℕ)
    (hcont : ∀ n : ℕ, ContinuousOn (wiredObservable d (n + 1) q) (Set.Icc 0 1))
    (hzero : ∀ n : ℕ, wiredObservable d (n + 1) q 0 = 0)
    (hone : ∀ n : ℕ, wiredObservable d (n + 1) q 1 = 1)
    (hstrict : ∀ n : ℕ, StrictMonoOn (wiredObservable d (n + 1) q) (Set.Icc 0 1))
    (hpc0 : 0 < wiredCriticalPoint d q) (hpc1 : wiredCriticalPoint d q < 1)
    (hsub : ∀ p : ℝ, 0 < p → p < wiredCriticalPoint d q → ∃ K : ℝ,
      ∀ᶠ n in atTop, wiredObservable d (n + 1) q p ≤ K / ((n : ℝ) + 2) ^ 2) :
    Tendsto (canonicalWiredRoot d q) atTop (𝓝 (wiredCriticalPoint d q)) := by
  have hspec := fun n => canonicalWiredRoot_spec d q n
    (hcont n) (hzero n) (hone n) (hstrict n)
  have hnonneg : ∀ n p, p ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ wiredObservable d (n + 1) q p := by
    intro n p hp
    have h := (hstrict n).monotoneOn (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) hp hp.1
    simpa only [hzero n] using h
  have htheta1 : wiredInfiniteObservable d q 1 = 1 := by
    simp [wiredInfiniteObservable, hone]
  have hne : {p : ℝ | p ∈ Set.Icc 0 1 ∧
      0 < wiredInfiniteObservable d q p}.Nonempty := by
    refine ⟨1, ?_, ?_⟩
    · norm_num
    · rw [htheta1]
      norm_num
  exact concreteWiredRoots_tendsto d q (canonicalWiredRoot d q) hnonneg
    (fun n => (hstrict n).monotoneOn) hne hpc0 hpc1
    (fun n => (hspec n).1) (fun n => (hspec n).2) hsub

end
end IsingCriticality

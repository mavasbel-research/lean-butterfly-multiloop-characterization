import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import ButterflyCharacterization.Domain.Abstractions.Loop
import ButterflyCharacterization.Domain.Model.Crossover

namespace ButterflyCharacterization.Domain.Model

noncomputable section

/-!
# Theorem 4.7: Necessary and Sufficient Multiloop Existence Criterion
Formalization and proof of Theorem 4.7 from:
"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"
(IEEE TAC 2022, DOI: 10.1109/TAC.2021.3109533).
-/

/-- Sign alternation condition: The branch difference function D(u) assumes both strictly positive
    and strictly negative values in the interior (u_min, u_max). -/
def HasBranchSignAlternation
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop) : Prop :=
  ∃ (u₁ u₂ : ℝ),
    loop.extrema.u_min < u₁ ∧ u₁ < u₂ ∧ u₂ < loop.extrema.u_max ∧
    branchDifference loop u₁ > 0 ∧ branchDifference loop u₂ < 0

/-- Theorem 4.7 (Multiloop Existence via Intermediate Value Property):
    If the branch difference function D(u) is continuous and exhibits sign alternation
    in the interior (u_min, u_max), then the loop is guaranteed to be a multiloop
    (possesses at least one interior crossover point u_c where D(u_c) = 0). -/
theorem theorem4_7_sign_alternation_implies_multiloop
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop)
    (h_cont : Continuous (branchDifference loop))
    (h_alt : HasBranchSignAlternation loop) :
    ButterflyCharacterization.Domain.Abstractions.IsMultiloop loop := by
  rcases h_alt with ⟨u₁, u₂, h_min_u₁, h_u₁_u₂, h_u₂_max, h_pos, h_neg⟩
  have h_le_u₁_u₂ : u₁ ≤ u₂ := le_of_lt h_u₁_u₂
  have h_subset := intermediate_value_Icc' h_le_u₁_u₂ (Continuous.continuousOn h_cont)
  have h_zero_mem : (0 : ℝ) ∈ Set.Icc (branchDifference loop u₂) (branchDifference loop u₁) := by
    rw [Set.mem_Icc]
    exact ⟨le_of_lt h_neg, le_of_lt h_pos⟩
  have h_in_image := h_subset h_zero_mem
  rcases h_in_image with ⟨c, hc_icc, hc_zero⟩
  rw [Set.mem_Icc] at hc_icc
  rcases hc_icc with ⟨hc_left, hc_right⟩
  use c
  dsimp [ButterflyCharacterization.Domain.Abstractions.IsInteriorCrossoverPoint]
  have hc_min : loop.extrema.u_min < c := lt_of_lt_of_le h_min_u₁ hc_left
  have hc_max : c < loop.extrema.u_max := lt_of_le_of_lt hc_right h_u₂_max
  have hc_eq : loop.y_pos c = loop.y_neg c := by
    dsimp [branchDifference] at hc_zero
    linarith
  exact ⟨hc_min, hc_max, hc_eq⟩

/-- Monotone Loop Non-Crossing Theorem:
    If the branch difference function is strictly positive across the entire interior,
    no interior crossover points can exist, and the loop is NOT a multiloop. -/
theorem strictly_positive_difference_no_interior_crossover
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop)
    (h_strictly_pos : ∀ u : ℝ, loop.extrema.u_min < u → u < loop.extrema.u_max → branchDifference loop u > 0) :
    ¬ (ButterflyCharacterization.Domain.Abstractions.IsMultiloop loop) := by
  intro h_multi
  rcases h_multi with ⟨u_c, h_min_uc, h_uc_max, h_eq⟩
  have h_diff_pos := h_strictly_pos u_c h_min_uc h_uc_max
  dsimp [branchDifference] at h_diff_pos
  linarith

end

end ButterflyCharacterization.Domain.Model

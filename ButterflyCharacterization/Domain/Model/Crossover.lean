import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import ButterflyCharacterization.Domain.Abstractions.Loop

namespace ButterflyCharacterization.Domain.Model

noncomputable section

/-!
# Lemma 4.4: Characterization of Crossover Points in Preisach Loops
Formalization and proof of Lemma 4.4 and Definitions 4.1, 4.3 from:
"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"
(IEEE TAC 2022, DOI: 10.1109/TAC.2021.3109533).
-/

/-- The branch difference function D(u) = y_neg(u) - y_pos(u) measuring
    the vertical gap between descending and ascending branches at input u. -/
def branchDifference (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop) (u : ℝ) : ℝ :=
  loop.y_neg u - loop.y_pos u

/-- Lemma 4.4 (Equivalence of Crossover Definition):
    A point u_c ∈ [u_min, u_max] is a crossover point (Definition 4.1) if and only if
    the branch difference function vanishes at u_c: D(u_c) = 0. -/
theorem lemma4_4_crossover_iff_difference_zero
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop)
    (u_c : ℝ) :
    ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop u_c ↔
    (loop.extrema.u_min ≤ u_c ∧ u_c ≤ loop.extrema.u_max ∧ branchDifference loop u_c = 0) := by
  dsimp [ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint, branchDifference]
  constructor
  · intro ⟨h_min, h_max, h_eq⟩
    refine ⟨h_min, h_max, ?_⟩
    linarith
  · intro ⟨h_min, h_max, h_zero⟩
    refine ⟨h_min, h_max, ?_⟩
    linarith

/-- Reversal endpoints u_min and u_max are always trivial crossover points
    due to loop trajectory closure. -/
theorem reversal_endpoints_are_crossover
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop) :
    ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop loop.extrema.u_min ∧
    ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop loop.extrema.u_max := by
  have h_min : ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop loop.extrema.u_min := by
    rw [lemma4_4_crossover_iff_difference_zero]
    refine ⟨le_refl _, le_of_lt loop.extrema.h_order, ?_⟩
    dsimp [branchDifference]
    linarith [loop.h_rev_min]
  have h_max : ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop loop.extrema.u_max := by
    rw [lemma4_4_crossover_iff_difference_zero]
    refine ⟨le_of_lt loop.extrema.h_order, le_refl _, ?_⟩
    dsimp [branchDifference]
    linarith [loop.h_rev_max]
  exact ⟨h_min, h_max⟩

/-- An interior crossover point represents a genuine non-endpoint branch crossing. -/
theorem interior_crossover_is_crossover
    (loop : ButterflyCharacterization.Domain.Abstractions.HysteresisLoop)
    (u_c : ℝ)
    (h_int : ButterflyCharacterization.Domain.Abstractions.IsInteriorCrossoverPoint loop u_c) :
    ButterflyCharacterization.Domain.Abstractions.IsCrossoverPoint loop u_c := by
  rcases h_int with ⟨h_lt_min, h_lt_max, h_eq⟩
  exact ⟨le_of_lt h_lt_min, le_of_lt h_lt_max, h_eq⟩

end

end ButterflyCharacterization.Domain.Model

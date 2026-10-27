import ButterflyCharacterization

/-!
# Statement tests (unit tier, checked at build time)

1. The exact statement of every formalized paper result is pinned with `#guard_msgs`: a change
   to any hypothesis or conclusion fails the build.
2. Non-vacuity: the definitions are not empty (audit failure modes F1–F5 of
   `/home/mavasbel/Dev/docs/reference/2026-10-26-02-21-lean4-native-lesson-09-critical-reading.md`).
-/

open ButterflyCharacterization.Domain.Model ButterflyCharacterization.Domain.Abstractions

/--
info: @lemma3_1 : ∀ {α β r₀ : ℝ} (I : SimplePeriodicInput),
  β < α →
    I.T ≤ I.t₁ →
      signedArea I.u (ccwRelay α β r₀ I.u) I.t₁ (I.t₁ + I.T) = if I.umin < β ∧ α < I.umax then 2 * (α - β) else 0
-/
#guard_msgs in
#check @lemma3_1

/--
info: @remark3_2 : ∀ {α β r₀ : ℝ} (I : SimplePeriodicInput),
  β < α →
    I.T ≤ I.t₁ →
      signedArea I.u (cwRelay α β r₀ I.u) I.t₁ (I.t₁ + I.T) = if I.umin < β ∧ α < I.umax then -(2 * (α - β)) else 0
-/
#guard_msgs in
#check @remark3_2

/--
info: @FinitePreisach.area : ∀ {n : ℕ} (P : FinitePreisach n) (I : SimplePeriodicInput) {tp : ℝ},
  IsHysteresisLoop P.output I tp → loopArea P.output I = 2 * ∑ i ∈ P.switching I, P.w i * (P.α i - P.β i)
-/
#guard_msgs in
#check @FinitePreisach.area

/--
info: @FinitePreisach.lemma4_4 : ∀ {n : ℕ} {P : FinitePreisach n} {I : SimplePeriodicInput},
  P.AllSwitch I →
    ∀ {υ γ : ℝ},
      IsCrossoverPoint I (P.output I.u) (υ, γ) ↔ υ ∈ Set.Icc I.umin I.umax ∧ γ = P.yUp υ ∧ ∑ i ∈ P.omega υ, P.w i = 0
-/
#guard_msgs in
#check @FinitePreisach.lemma4_4

/--
info: @FinitePreisach.corollary3_4 : ∀ {n : ℕ} (P : FinitePreisach n) (σ : Equiv.Perm (Fin n)) (κ : ℝ),
  (∀ (i : Fin n), P.α (σ i) = κ - P.β i) →
    (∀ (i : Fin n), P.β (σ i) = κ - P.α i) →
      (∀ (i : Fin n), P.w (σ i) = -P.w i) →
        ∀ {I : SimplePeriodicInput} {tp : ℝ},
          IsHysteresisLoop P.output I tp → I.umin + I.umax = κ → loopArea P.output I = 0
-/
#guard_msgs in
#check @FinitePreisach.corollary3_4

/--
info: @FinitePreisach.theorem4_7 : ∀ {n : ℕ} {P : FinitePreisach n} {I : SimplePeriodicInput},
  P.AllSwitch I →
    ∀ {aLo a₁ aHi : ℝ},
      I.umin < aLo →
        aLo < a₁ →
          a₁ < aHi →
            aHi < I.umax →
              ∑ i ∈ P.omega a₁, P.w i = 0 →
                ∑ i ∈ P.omega aLo, P.w i ≠ 0 → ∑ i ∈ P.omega aHi, P.w i ≠ 0 → IsMultiloopOperator P.output
-/
#guard_msgs in
#check @FinitePreisach.theorem4_7

/-- info: @ccwRelay_hysteresis : ∀ {α β r₀ : ℝ}, IsHysteresisOperator (ccwRelay α β r₀) -/
#guard_msgs in
#check @ccwRelay_hysteresis

/-- info: ButterflyCharacterization.Domain.Model.twoRelay_isButterfly : IsButterflyOperator twoRelay.output -/
#guard_msgs in
#check twoRelay_isButterfly

/-- info: ButterflyCharacterization.Domain.Model.twoRelay_isMultiloop : IsMultiloopOperator twoRelay.output -/
#guard_msgs in
#check twoRelay_isMultiloop

/--
info: def ButterflyCharacterization.Domain.Abstractions.IsButterflyOperator : SignalOperator → Prop :=
fun Φ ↦ IsHysteresisOperator Φ ∧ ∃ I tp, IsHysteresisLoop Φ I tp ∧ loopArea Φ I = 0
-/
#guard_msgs in
#print IsButterflyOperator

/-! ### Non-vacuity -/

/-- One positive relay `(1/2, −1/2)`. -/
noncomputable def singleRelay : FinitePreisach 1 :=
  ⟨![1 / 2], ![-1 / 2], fun _ => by norm_num, ![1], ![1]⟩

/-- F1/F2: the loop area is computed, not chosen: a single positive relay has area `2`. -/
theorem singleRelay_area : loopArea singleRelay.output unitCosine = 2 := by
  classical
  rw [FinitePreisach.area_of_late _ _ (le_refl _), FinitePreisach.switching, unitCosine,
    cosineInput_umin, cosineInput_umax, Finset.sum_filter, Fin.sum_univ_one]
  norm_num [singleRelay]

/-- F1: the relay output depends on the input: `+1` above `α`, `−1` below `β`. -/
example : ccwRelay 1 0 0 (fun _ => 2) 0 = 1 ∧ ccwRelay 1 0 0 (fun _ => -1) 0 = -1 :=
  ⟨ccwRelay_of_gt (by norm_num) le_rfl (by norm_num),
    ccwRelay_of_lt (by norm_num) le_rfl (by norm_num)⟩

/-- §III: nonnegative weights exclude clockwise loops. -/
example : ¬ ExhibitsClockwise singleRelay.output :=
  FinitePreisach.not_clockwise_of_nonneg _ fun i => by fin_cases i; norm_num [singleRelay]

/-- F5: strict switching as in eq. (2): an input exactly at `α` does not switch the relay. -/
example : ccwRelay 1 0 (-1) (fun _ => 1) 0 = -1 :=
  ccwRelay_zero (u := fun _ => 1) (by norm_num)

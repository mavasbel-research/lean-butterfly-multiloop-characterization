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
info: @FinitePreisach.lemma4_4 : ∀ {n : ℕ} {P : FinitePreisach n} {I : SimplePeriodicInput} {tp : ℝ},
  IsHysteresisLoop P.output I tp →
    ∀ {υ γ : ℝ},
      IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
        υ ∈ Set.Icc I.umin I.umax ∧ γ = P.yUp I υ ∧ ∑ i ∈ P.omega I υ, P.w i = 0
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
info: @FinitePreisach.theorem4_7 : ∀ {n : ℕ} {P : FinitePreisach n} {β₀ aLo a₁ aHi α₀ : ℝ},
  β₀ < aLo →
    aLo < a₁ →
      a₁ < aHi →
        aHi < α₀ →
          ∑ i ∈ P.bandSet β₀ α₀ a₁, P.w i = 0 →
            ∑ i ∈ P.bandSet β₀ α₀ aLo, P.w i ≠ 0 → ∑ i ∈ P.bandSet β₀ α₀ aHi, P.w i ≠ 0 → IsMultiloopOperator P.output
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

/-! ### Preisach operator (4) -/

/--
info: @IntegralPreisach.area : ∀ {I : SimplePeriodicInput} (P : IntegralPreisach) {tp : ℝ},
  IsHysteresisLoop P.output I tp → loopArea P.output I = P.areaOf I.umin I.umax
-/
#guard_msgs in
#check @IntegralPreisach.area

/--
info: IntegralPreisach.theorem3_3 : ∀ (P : IntegralPreisach) {β₁ α₁ : ℝ},
  β₁ < α₁ →
    Filter.Tendsto (fun M ↦ P.areaOf β₁ M) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun m ↦ P.areaOf m α₁) Filter.atBot Filter.atBot →
        (∀ (m M : ℝ), m ≤ β₁ → α₁ ≤ M → ∃ υ ∈ Set.Icc m M, P.omegaWeight m M υ ≠ 0) → IsButterflyOperator P.output
-/
#guard_msgs in
#check @IntegralPreisach.theorem3_3

/--
info: IntegralPreisach.theorem3_3_moments : ∀ (P : IntegralPreisach) {β₁ α₁ s : ℝ},
  β₁ < α₁ →
    s ≠ 0 →
      (∀ (p : ℝ × ℝ), β₁ < p.2 → α₁ ≤ p.1 → 0 ≤ s * P.μ p) →
        (∀ (p : ℝ × ℝ), p.2 ≤ β₁ → p.1 < α₁ → s * P.μ p ≤ 0) →
          ¬MeasureTheory.IntegrableOn (fun p ↦ P.μ p * (p.1 - p.2)) {p | β₁ < p.2 ∧ α₁ ≤ p.1} MeasureTheory.volume →
            ¬MeasureTheory.IntegrableOn (fun p ↦ P.μ p * (p.1 - p.2)) {p | p.2 ≤ β₁ ∧ p.1 < α₁} MeasureTheory.volume →
              (∀ (m M : ℝ), m ≤ β₁ → α₁ ≤ M → ∃ υ ∈ Set.Icc m M, P.omegaWeight m M υ ≠ 0) → IsButterflyOperator P.output
-/
#guard_msgs in
#check @IntegralPreisach.theorem3_3_moments

/--
info: IntegralPreisach.corollary3_4 : ∀ (P : IntegralPreisach) (κ : ℝ),
  (∀ (p : ℝ × ℝ), P.μ (ButterflyCharacterization.Domain.Model.refl κ p) = -P.μ p) →
    ∀ {I : SimplePeriodicInput} {tp : ℝ}, IsHysteresisLoop P.output I tp → I.umin + I.umax = κ → loopArea P.output I = 0
-/
#guard_msgs in
#check @IntegralPreisach.corollary3_4

/-- info: ButterflyCharacterization.Domain.Model.antisymWitness_isButterfly : IsButterflyOperator antisymWitness.output -/
#guard_msgs in
#check antisymWitness_isButterfly

/-- info: ButterflyCharacterization.Domain.Model.butterflyWitness_isButterfly : IsButterflyOperator butterflyWitness.output -/
#guard_msgs in
#check butterflyWitness_isButterfly

/-! ### Non-vacuity -/

/-- One positive relay `(1/2, −1/2)`. -/
noncomputable def singleRelay : FinitePreisach 1 :=
  ⟨![1 / 2], ![-1 / 2], fun _ => by norm_num, ![1], ![1]⟩

/-- F1/F2: the loop area is computed, not chosen: a single positive relay has area `2`. -/
theorem singleRelay_area : loopArea singleRelay.output unitCosine = 2 := by
  classical
  rw [FinitePreisach.area_of_late _ _ unitCosine_late, FinitePreisach.switching,
    unitCosine_umin, unitCosine_umax, Finset.sum_filter, Fin.sum_univ_one]
  norm_num [singleRelay]

/-- Lemma 4.4 without `AllSwitch`: a relay that never switches (`(2, −2)` on `[−1, 1]`) adds a
constant to both branches and no crossover condition. -/
noncomputable def withFrozen : FinitePreisach 2 :=
  ⟨![1 / 2, 2], ![-1 / 2, -2], fun i => by fin_cases i <;> norm_num, ![1, 5], ![1, 1]⟩

theorem withFrozen_isLoop : IsHysteresisLoop withFrozen.output unitCosine unitCosine.t₁ := by
  classical
  refine FinitePreisach.isHysteresisLoop (υ := 0) unitCosine_late
    (by rw [unitCosine_umin, unitCosine_umax]; norm_num) ?_
  rw [FinitePreisach.omega, Finset.sum_filter, Fin.sum_univ_two, unitCosine_umin, unitCosine_umax]
  norm_num [withFrozen]

example : ¬ IsCrossoverPoint unitCosine (withFrozen.output unitCosine.u) (0, withFrozen.yUp unitCosine 0) := by
  classical
  rw [FinitePreisach.lemma4_4 withFrozen_isLoop]
  rintro ⟨-, -, h⟩
  rw [FinitePreisach.omega, Finset.sum_filter, Fin.sum_univ_two, unitCosine_umin,
    unitCosine_umax] at h
  norm_num [withFrozen] at h

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

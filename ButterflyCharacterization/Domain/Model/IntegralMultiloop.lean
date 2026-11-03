import ButterflyCharacterization.Domain.Model.Theorem33

/-!
# Integral crossovers and multiloops

This module lifts the finite results in `Branches.lean` and `Multiloop.lean` to the integral
Preisach operator (4). The abstraction boundary is the branch gap already proved in
`Theorem33.lean`:

`y⁺(υ) - y⁻(υ) = -2 ∬_{Ω_υ} μ`.

Consequently, a crossover is precisely a zero of the switching-band integral. Theorem 4.7 then
uses one zero between two nonzero neighboring levels to construct the connected component
required by Definition 4.3.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

namespace IntegralPreisach

variable (P : IntegralPreisach) (I : SimplePeriodicInput)

/-- **Lemma 4.4** for operator (4), once the periodic regime starts before the input minimum. -/
theorem lemma4_4_late (hT : I.T ≤ I.t₁) {υ γ : ℝ} :
    IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = P.yUp I.umin I.umax υ ∧
        P.omegaWeight I.umin I.umax υ = 0 := by
  rw [(P.branchForm hT).crossover_iff]
  show _ ∧ _ ∧ P.yUp I.umin I.umax υ = P.yDown I.umin I.umax υ ↔ _
  refine and_congr_right fun hυ => and_congr_right fun _ => ?_
  have gap := P.yUp_sub_yDown (I := I) hυ
  constructor <;> intro h <;> linarith

/-- Shifting by one period preserves the integral ascending branch. -/
theorem yUp_shift :
    P.yUp I.shift.umin I.shift.umax = P.yUp I.umin I.umax := by
  simp only [FinitePreisach.shift_umin, FinitePreisach.shift_umax]

/-- Shifting by one period preserves the integral switching-band integral. -/
theorem omegaWeight_shift (υ : ℝ) :
    P.omegaWeight I.shift.umin I.shift.umax υ = P.omegaWeight I.umin I.umax υ := by
  simp only [FinitePreisach.shift_umin, FinitePreisach.shift_umax]

/-- **Lemma 4.4** for the integral Preisach operator (4). On any hysteresis loop, a point at
input level `υ` is a crossover precisely when the weight integral over its switching band is zero. -/
theorem lemma4_4 {tp : ℝ} (hl : IsHysteresisLoop P.output I tp) {υ γ : ℝ} :
    IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = P.yUp I.umin I.umax υ ∧
        P.omegaWeight I.umin I.umax υ = 0 := by
  have hT : I.shift.T ≤ I.shift.t₁ := by
    show I.T ≤ I.t₁ + I.T
    linarith [I.start_nonneg]
  have key := P.lemma4_4_late I.shift hT (υ := υ) (γ := γ)
  unfold IsCrossoverPoint at key ⊢
  change (υ, γ) ∈ I.shift.ascending (P.output I.u) ∩ I.shift.descending (P.output I.u) ↔ _ at key
  rwa [FinitePreisach.ascending_shift hl, FinitePreisach.descending_shift hl,
    FinitePreisach.shift_umin, FinitePreisach.shift_umax] at key

/-- **Theorem 4.7** for an explicitly supplied periodic input. If the switching-band integral
is zero at an interior level and nonzero at neighboring levels, then the integral Preisach
operator is a multiloop hysteresis operator. -/
theorem theorem4_7_of_input (hT : I.T ≤ I.t₁) {aLo a₁ aHi : ℝ}
    (hlo : I.umin < aLo) (hlo₁ : aLo < a₁) (h₁hi : a₁ < aHi) (hhi : aHi < I.umax)
    (hΩ₁ : P.omegaWeight I.umin I.umax a₁ = 0)
    (hΩlo : P.omegaWeight I.umin I.umax aLo ≠ 0)
    (hΩhi : P.omegaWeight I.umin I.umax aHi ≠ 0) :
    IsMultiloopOperator P.output := by
  set F := I.ascending (P.output I.u) ∩ I.descending (P.output I.u)
  have hrange : ∀ {a}, I.umin < a → a < I.umax → a ∈ Icc I.umin I.umax :=
    fun h1 h2 => ⟨h1.le, h2.le⟩
  have hloop := P.isHysteresisLoop hT (hrange hlo (by linarith)) hΩlo
  have hp : ((a₁, P.yUp I.umin I.umax a₁) : ℝ × ℝ) ∈ F :=
    (P.lemma4_4 I hloop).mpr ⟨hrange (by linarith) (by linarith), rfl, hΩ₁⟩
  have hno : ∀ q ∈ F, q.1 ≠ aLo ∧ q.1 ≠ aHi := by
    rintro ⟨υ, γ⟩ hq
    have h := ((P.lemma4_4 I hloop).mp hq).2.2
    exact ⟨fun e => hΩlo (e ▸ h), fun e => hΩhi (e ▸ h)⟩
  set U : Set (ℝ × ℝ) := {q | q.1 < aLo} ∪ {q | aHi < q.1}
  set V : Set (ℝ × ℝ) := {q | aLo < q.1 ∧ q.1 < aHi}
  have hU : IsOpen U := (isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_const continuous_fst)
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro q (hq | hq) ⟨h1, h2⟩
    · exact absurd (hq.trans h1) (lt_irrefl _)
    · exact absurd (h2.trans hq) (lt_irrefl _)
  have hcover : connectedComponentIn F (a₁, P.yUp I.umin I.umax a₁) ⊆ U ∪ V := fun q hq => by
    obtain ⟨h1, h2⟩ := hno q (connectedComponentIn_subset F _ hq)
    rcases lt_trichotomy q.1 aLo with l | l | l
    · exact Or.inl (Or.inl l)
    · exact absurd l h1
    · rcases lt_trichotomy q.1 aHi with m | m | m
      · exact Or.inr ⟨l, m⟩
      · exact absurd m h2
      · exact Or.inl (Or.inr m)
  rcases isPreconnected_connectedComponentIn.subset_or_subset hU hV hUV hcover with hsub | hsub
  · exfalso
    rcases hsub (mem_connectedComponentIn hp) with h' | h'
    · exact absurd (h'.trans hlo₁) (lt_irrefl _)
    · exact absurd (h'.trans h₁hi) (lt_irrefl _)
  · refine ⟨P.output_hysteresis, I, I.t₁, hloop, _, hp, fun q hq => ?_⟩
    obtain ⟨h1, h2⟩ := hsub hq
    exact ⟨by intro e; rw [e] at h1; linarith, by intro e; rw [e] at h2; linarith⟩

/-- **Theorem 4.7** for operator (4), using the cosine input with extremes `β₀ < α₀`. -/
theorem theorem4_7 {β₀ aLo a₁ aHi α₀ : ℝ}
    (hlo : β₀ < aLo) (hlo₁ : aLo < a₁) (h₁hi : a₁ < aHi) (hhi : aHi < α₀)
    (hΩ₁ : P.omegaWeight β₀ α₀ a₁ = 0)
    (hΩlo : P.omegaWeight β₀ α₀ aLo ≠ 0)
    (hΩhi : P.omegaWeight β₀ α₀ aHi ≠ 0) : IsMultiloopOperator P.output := by
  have h : β₀ < α₀ := by linarith
  refine P.theorem4_7_of_input (cosineInput β₀ α₀ h) (le_refl _) (aLo := aLo) (a₁ := a₁)
    (aHi := aHi) ?_ hlo₁ h₁hi ?_ ?_ ?_ ?_
  · rw [cosineInput_umin]
    exact hlo
  · rw [cosineInput_umax]
    exact hhi
  · rwa [cosineInput_umin, cosineInput_umax]
  · rwa [cosineInput_umin, cosineInput_umax]
  · rwa [cosineInput_umin, cosineInput_umax]

end IntegralPreisach

end ButterflyCharacterization.Domain.Model

import ButterflyCharacterization.Domain.Model.Butterfly

/-!
# Theorem 4.7 (finite form): a multiloop operator

Theorem 4.7 asks for a point `(α₀, β₀)` with `α₀ > β₀` and levels `α₁₋ < α₁ < α₁₊` with
`β₀ < α₁₋`, `α₁₊ < α₀`, such that the crossover condition (12) holds on `Ω_{α₁}` and fails on
`Ω_{α₁₋}` and `Ω_{α₁₊}`; its proof uses a periodic input with `u_max = α₀`, `u_min = β₀`.
Under the input `(β₀ + α₀)/2 − (α₀ − β₀)/2 · cos t`, the finite form of `Ω_a` is
`bandSet β₀ α₀ a = {i | β₀ < βᵢ, αᵢ < α₀, βᵢ ≤ a ≤ αᵢ}` (`Branches.lean`, Lemma 4.4).

* `theorem4_7_of_input`: for any simple periodic input with `T ≤ t₁`;
* `theorem4_7`: the paper's form, hypotheses on the relays and weights only.
-/

open Set Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

namespace FinitePreisach

variable {n : ℕ} {P : FinitePreisach n}

/-- Theorem 4.7 for a given input. -/
theorem theorem4_7_of_input {I : SimplePeriodicInput} (hT : I.T ≤ I.t₁) {aLo a₁ aHi : ℝ}
    (hlo : I.umin < aLo) (hlo₁ : aLo < a₁) (h₁hi : a₁ < aHi) (hhi : aHi < I.umax)
    (hΩ₁ : ∑ i ∈ P.omega I a₁, P.w i = 0)
    (hΩlo : ∑ i ∈ P.omega I aLo, P.w i ≠ 0) (hΩhi : ∑ i ∈ P.omega I aHi, P.w i ≠ 0) :
    IsMultiloopOperator P.output := by
  set F := I.ascending (P.output I.u) ∩ I.descending (P.output I.u)
  have hrange : ∀ {a}, I.umin < a → a < I.umax → a ∈ Icc I.umin I.umax :=
    fun h1 h2 => ⟨h1.le, h2.le⟩
  have hloop := isHysteresisLoop hT (hrange hlo (by linarith)) hΩlo
  have hp : ((a₁, P.yUp I a₁) : ℝ × ℝ) ∈ F :=
    (lemma4_4 hloop).mpr ⟨hrange (by linarith) (by linarith), rfl, hΩ₁⟩
  have hno : ∀ q ∈ F, q.1 ≠ aLo ∧ q.1 ≠ aHi := by
    rintro ⟨υ, γ⟩ hq
    have := ((lemma4_4 hloop).mp hq).2.2
    exact ⟨fun e => hΩlo (e ▸ this), fun e => hΩhi (e ▸ this)⟩
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
  have hcover : connectedComponentIn F (a₁, P.yUp I a₁) ⊆ U ∪ V := fun q hq => by
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

variable (P)

/-- Finite form of `Ω_a` for the extremes `β₀ < α₀`: relays with `β₀ < βᵢ`, `αᵢ < α₀` and
`βᵢ ≤ a ≤ αᵢ`. -/
noncomputable def bandSet (β₀ α₀ a : ℝ) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => β₀ < P.β i ∧ P.α i < α₀ ∧ P.β i ≤ a ∧ a ≤ P.α i

theorem omega_cosine {β₀ α₀ : ℝ} (h : β₀ < α₀) (a : ℝ) :
    P.omega (cosineInput β₀ α₀ h) a = P.bandSet β₀ α₀ a := by
  simp only [omega, bandSet, cosineInput_umin, cosineInput_umax]

variable {P}

/-- **Theorem 4.7** (finite form). If `β₀ < α₁₋ < α₁ < α₁₊ < α₀`, the weights on
`bandSet β₀ α₀ α₁` sum to zero and those on `bandSet β₀ α₀ α₁₋`, `bandSet β₀ α₀ α₁₊` do not,
then the finite Preisach operator is a multiloop hysteresis operator. -/
theorem theorem4_7 {β₀ aLo a₁ aHi α₀ : ℝ} (hlo : β₀ < aLo) (hlo₁ : aLo < a₁) (h₁hi : a₁ < aHi)
    (hhi : aHi < α₀) (hΩ₁ : ∑ i ∈ P.bandSet β₀ α₀ a₁, P.w i = 0)
    (hΩlo : ∑ i ∈ P.bandSet β₀ α₀ aLo, P.w i ≠ 0)
    (hΩhi : ∑ i ∈ P.bandSet β₀ α₀ aHi, P.w i ≠ 0) : IsMultiloopOperator P.output := by
  have h : β₀ < α₀ := by linarith
  refine theorem4_7_of_input (I := cosineInput β₀ α₀ h) (le_refl _) (aLo := aLo) (a₁ := a₁)
    (aHi := aHi) ?_ hlo₁ h₁hi ?_ ?_ ?_ ?_
  · rw [cosineInput_umin]; exact hlo
  · rw [cosineInput_umax]; exact hhi
  · rwa [omega_cosine]
  · rwa [omega_cosine]
  · rwa [omega_cosine]

end FinitePreisach

/-- The butterfly operator `twoRelay` is also a multiloop operator, as §IV notes every
butterfly operator is: crossovers at level `0`, none at `−9/20` and `11/20`. -/
theorem twoRelay_isMultiloop : IsMultiloopOperator twoRelay.output := by
  classical
  refine FinitePreisach.theorem4_7 (β₀ := -1) (aLo := -9 / 20) (a₁ := 0) (aHi := 11 / 20)
    (α₀ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ <;>
  · rw [FinitePreisach.bandSet, Finset.sum_filter, Fin.sum_univ_two]
    norm_num [twoRelay]

end ButterflyCharacterization.Domain.Model

import ButterflyCharacterization.Domain.Model.Butterfly

/-!
# Theorem 4.7 (finite form): a multiloop operator

Theorem 4.7 asks for levels `α₁₋ < α₁ < α₁₊` strictly inside the input range such that the
crossover condition (12) holds at `α₁` and fails at `α₁₋` and `α₁₊`. Then the crossover
point at `α₁` lies in a maximal connected subset of `H⁺ ∩ H⁻` that stays strictly between
`α₁₋` and `α₁₊`, so it contains no point with `u_c = u_min` or `u_c = u_max`
(Definition 4.3). The finite form of (12) is `Σ_{Ω_υ} wᵢ = 0` (Lemma 4.4, finite form).
-/

open Set Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

namespace FinitePreisach

variable {n : ℕ} {P : FinitePreisach n} {I : SimplePeriodicInput}

/-- **Theorem 4.7** (finite form). -/
theorem theorem4_7 (h : P.AllSwitch I) {aLo a₁ aHi : ℝ} (hlo : I.umin < aLo) (hlo₁ : aLo < a₁)
    (h₁hi : a₁ < aHi) (hhi : aHi < I.umax) (hΩ₁ : ∑ i ∈ P.omega a₁, P.w i = 0)
    (hΩlo : ∑ i ∈ P.omega aLo, P.w i ≠ 0) (hΩhi : ∑ i ∈ P.omega aHi, P.w i ≠ 0) :
    IsMultiloopOperator P.output := by
  set F := I.ascending (P.output I.u) ∩ I.descending (P.output I.u)
  have hrange : ∀ {a}, I.umin < a → a < I.umax → a ∈ Icc I.umin I.umax :=
    fun h1 h2 => ⟨h1.le, h2.le⟩
  have hloop := isHysteresisLoop h (hrange hlo (by linarith)) hΩlo
  have hp : ((a₁, P.yUp a₁) : ℝ × ℝ) ∈ F :=
    (lemma4_4 h).mpr ⟨hrange (by linarith) (by linarith), rfl, hΩ₁⟩
  have hno : ∀ q ∈ F, q.1 ≠ aLo ∧ q.1 ≠ aHi := by
    rintro ⟨υ, γ⟩ hq
    have := ((lemma4_4 h).mp hq).2.2
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
  have hcover : connectedComponentIn F (a₁, P.yUp a₁) ⊆ U ∪ V := fun q hq => by
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

end FinitePreisach

/-- The butterfly operator `twoRelay` is also a multiloop operator, as §IV notes every
butterfly operator is: crossovers at `υ = 0`, none at `−9/20` and `11/20`. -/
theorem twoRelay_isMultiloop : IsMultiloopOperator twoRelay.output := by
  classical
  have hm : unitCosine.umin = -1 := cosineInput_umin _ _ _
  have hM : unitCosine.umax = 1 := cosineInput_umax _ _ _
  refine FinitePreisach.theorem4_7 (aLo := -9 / 20) (a₁ := 0) (aHi := 11 / 20)
    twoRelay_allSwitch (by rw [hm]; norm_num) (by norm_num) (by norm_num) (by rw [hM]; norm_num)
    ?_ ?_ (by rw [twoRelay_omega]; norm_num)
  · rw [FinitePreisach.omega, Finset.sum_filter, Fin.sum_univ_two]
    norm_num [twoRelay]
  · rw [FinitePreisach.omega, Finset.sum_filter, Fin.sum_univ_two]
    norm_num [twoRelay]

end ButterflyCharacterization.Domain.Model

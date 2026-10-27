import ButterflyCharacterization.Domain.Model.Preisach

/-!
# Branches, crossovers (Lemma 4.4) and hysteresis loops of finite Preisach operators

Throughout, every relay switches under the input: `u_min < βᵢ` and `αᵢ < u_max` (the relays
lie in the triangle `P₁` of the paper's proofs). Then on the ascending branch the output at
input level `υ` is `y⁺(υ) = Σ wᵢ (αᵢ < υ ? 1 : −1)`, and on the descending branch
`y⁻(υ) = Σ wᵢ (υ < βᵢ ? −1 : 1)`. Consequences:

* **Lemma 4.4** (finite form): `(υ, y⁺(υ))` is a crossover point iff `Σ_{Ω_υ} wᵢ = 0`, where
  `Ω_υ = {i | βᵢ ≤ υ ≤ αᵢ}`;
* the orbit from `t₁` is `H⁺ ∪ H⁻`, the output is periodic from `t₁`, and `(u, y)` is a
  hysteresis loop (Definition 2.5) as soon as `Σ_{Ω_υ} wᵢ ≠ 0` for one level `υ`.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

namespace FinitePreisach

variable {n : ℕ} (P : FinitePreisach n) (I : SimplePeriodicInput)

/-- All relays switch under the input `I`. -/
def AllSwitch : Prop := ∀ i, I.umin < P.β i ∧ P.α i < I.umax

/-- Output on the ascending branch at input level `υ`. -/
noncomputable def yUp (υ : ℝ) : ℝ := ∑ i, P.w i * (if P.α i < υ then 1 else -1)

/-- Output on the descending branch at input level `υ`. -/
noncomputable def yDown (υ : ℝ) : ℝ := ∑ i, P.w i * (if υ < P.β i then -1 else 1)

/-- `Ω_υ`: the relays whose band `[βᵢ, αᵢ]` contains `υ`. -/
noncomputable def omega (υ : ℝ) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => P.β i ≤ υ ∧ υ ≤ P.α i

variable {P I}

theorem output_rising (h : P.AllSwitch I) {x : ℝ} (hx : x ∈ Icc I.t₁ I.t₂) :
    P.output I.u x = P.yUp (I.u x) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx0 : 0 ≤ x := I.start_nonneg.trans hx.1
  congr 1
  split_ifs with hα
  · exact ccwRelay_of_gt (P.ordered i) hx0 hα
  · have hd : SwitchedDown (P.α i) (P.β i) I.u x := ⟨I.t₁, ⟨I.start_nonneg, hx.1⟩, (h i).1,
      fun r hr => (I.rising ⟨hr.1, hr.2.trans hx.2⟩ hx hr.2).trans (not_lt.mp hα)⟩
    have hn : ¬ SwitchedUp (P.α i) (P.β i) I.u x := fun hu => not_up_and_down ⟨hu, hd⟩
    simp [relay, ccwRelay, hd, hn]

theorem output_falling (h : P.AllSwitch I) {x : ℝ} (hx : x ∈ Icc I.t₂ (I.t₁ + I.T)) :
    P.output I.u x = P.yDown (I.u x) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx0 : 0 ≤ x := I.start_nonneg.trans (I.t₁_lt_t₂.le.trans hx.1)
  congr 1
  split_ifs with hβ
  · exact ccwRelay_of_lt (P.ordered i) hx0 hβ
  · have hu : SwitchedUp (P.α i) (P.β i) I.u x :=
      ⟨I.t₂, ⟨I.start_nonneg.trans I.t₁_lt_t₂.le, hx.1⟩, (h i).2,
        fun r hr => (not_lt.mp hβ).trans (I.falling ⟨hr.1, hr.2.trans hx.2⟩ hx hr.2)⟩
    simp [relay, ccwRelay, hu]

/-- Every level between `u_min` and `u_max` is reached on the ascending branch. -/
theorem exists_rising {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₁ I.t₂, I.u x = υ :=
  intermediate_value_Icc I.t₁_lt_t₂.le I.continuous.continuousOn hυ

/-- Every level between `u_min` and `u_max` is reached on the descending branch. -/
theorem exists_falling {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₂ (I.t₁ + I.T), I.u x = υ := by
  have hυ' : υ ∈ Icc (I.u (I.t₁ + I.T)) (I.u I.t₂) := by rw [I.end_eq]; exact hυ
  exact intermediate_value_Icc' I.t₂_lt.le I.continuous.continuousOn hυ'

theorem mem_ascending (h : P.AllSwitch I) {p : ℝ × ℝ} :
    p ∈ I.ascending (P.output I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = P.yUp p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, output_rising h hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := exists_rising hυ
    exact ⟨x, hx, Prod.ext hux (by show P.output I.u x = p.2; rw [output_rising h hx, hux, h2])⟩

theorem mem_descending (h : P.AllSwitch I) {p : ℝ × ℝ} :
    p ∈ I.descending (P.output I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = P.yDown p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, output_falling h hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := exists_falling hυ
    exact ⟨x, hx, Prod.ext hux (by show P.output I.u x = p.2; rw [output_falling h hx, hux, h2])⟩

/-- The branch gap: `y⁺(υ) − y⁻(υ) = −2 Σ_{Ω_υ} wᵢ`. -/
theorem yUp_sub_yDown (υ : ℝ) : P.yUp υ - P.yDown υ = -2 * ∑ i ∈ P.omega υ, P.w i := by
  classical
  rw [yUp, yDown, ← Finset.sum_sub_distrib, omega, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := P.ordered i
  by_cases h1 : P.α i < υ
  · have h2 : ¬ υ < P.β i := fun h => by linarith
    have h3 : ¬ (P.β i ≤ υ ∧ υ ≤ P.α i) := fun h => by linarith [h.2]
    simp [h1, h2, h3]
  · by_cases h2 : υ < P.β i
    · have h3 : ¬ (P.β i ≤ υ ∧ υ ≤ P.α i) := fun h => by linarith [h.1]
      simp [h1, h2, h3]
    · have h3 : P.β i ≤ υ ∧ υ ≤ P.α i := ⟨not_lt.mp h2, not_lt.mp h1⟩
      simp [h1, h2, h3]
      ring

/-- **Lemma 4.4** (finite form). A point of the loop at input level `υ` is a crossover point
iff the weights of the relays whose band contains `υ` sum to zero. -/
theorem lemma4_4 (h : P.AllSwitch I) {υ γ : ℝ} :
    IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = P.yUp υ ∧ ∑ i ∈ P.omega υ, P.w i = 0 := by
  unfold IsCrossoverPoint
  rw [mem_inter_iff, mem_ascending h, mem_descending h]
  have gap := P.yUp_sub_yDown υ
  constructor
  · rintro ⟨⟨hυ, hup⟩, -, hdn⟩
    refine ⟨hυ, hup, ?_⟩
    simp only at hup hdn
    linarith
  · rintro ⟨hυ, hup, hΩ⟩
    refine ⟨⟨hυ, hup⟩, hυ, ?_⟩
    simp only at hup ⊢
    rw [hΩ] at gap
    linarith

/-! ### The orbit and Definition 2.5 -/

theorem output_periodic (h : P.AllSwitch I) {t : ℝ} (ht : I.t₁ ≤ t) :
    P.output I.u (t + I.T) = P.output I.u t :=
  Finset.sum_congr rfl fun i _ => by
    rw [relay, ccwRelay_periodic I.period_pos.le I.periodic I.start_nonneg (h i).1 ht]

theorem output_periodic_nat (h : P.AllSwitch I) {t : ℝ} (ht : I.t₁ ≤ t) (k : ℕ) :
    P.output I.u (t + k * I.T) = P.output I.u t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc,
      output_periodic h (by nlinarith [I.period_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]), ih]

/-- From `t₁` on, the orbit is the union of the two branches of one period. -/
theorem orbit_eq (h : P.AllSwitch I) :
    I.orbit (P.output I.u) I.t₁ = I.ascending (P.output I.u) ∪ I.descending (P.output I.u) := by
  have hT := I.period_pos
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    set k := ⌊(t - I.t₁) / I.T⌋₊
    have hk1 : (k : ℝ) * I.T ≤ t - I.t₁ := by
      have := Nat.floor_le (div_nonneg (sub_nonneg.mpr ht) hT.le)
      rwa [le_div_iff₀ hT] at this
    have hk2 : t - I.t₁ < (k + 1) * I.T := by
      have := Nat.lt_floor_add_one ((t - I.t₁) / I.T)
      rwa [div_lt_iff₀ hT] at this
    set x := t - k * I.T
    have hx : x ∈ Icc I.t₁ (I.t₁ + I.T) := ⟨by linarith, by linarith⟩
    have hux : I.u t = I.u x := by
      rw [show t = x + k * I.T by ring]
      exact I.periodic.nat_mul k x
    have hyx : P.output I.u t = P.output I.u x := by
      rw [show t = x + k * I.T by ring]
      exact output_periodic_nat h hx.1 k
    show (I.u t, P.output I.u t) ∈ _
    rw [hux, hyx]
    rcases le_total x I.t₂ with h2 | h2
    · exact Or.inl ⟨x, ⟨hx.1, h2⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨h2, hx.2⟩, rfl⟩
  · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ht.1, rfl⟩
    · exact ⟨t, mem_Ici.mpr (I.t₁_lt_t₂.le.trans ht.1), rfl⟩

/-- The vertical line at `υ` meets the orbit exactly in `(υ, y⁺(υ))` and `(υ, y⁻(υ))`. -/
theorem orbit_slice (h : P.AllSwitch I) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    {p ∈ I.orbit (P.output I.u) I.t₁ | p.1 = υ} = {(υ, P.yUp υ), (υ, P.yDown υ)} := by
  ext ⟨a, b⟩
  simp only [orbit_eq h, mem_ofPred_eq, mem_union, mem_insert_iff, mem_singleton_iff,
    Prod.mk.injEq, mem_ascending h, mem_descending h]
  constructor
  · rintro ⟨(⟨-, hb⟩ | ⟨-, hb⟩), rfl⟩
    · exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr ⟨rfl, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl ⟨hυ, rfl⟩, rfl⟩
    · exact ⟨Or.inr ⟨hυ, rfl⟩, rfl⟩

/-- **Definition 2.5** holds from `t_p = t₁` as soon as one level `υ` has `Σ_{Ω_υ} wᵢ ≠ 0`. -/
theorem isHysteresisLoop (h : P.AllSwitch I) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax)
    (hΩ : ∑ i ∈ P.omega υ, P.w i ≠ 0) : IsHysteresisLoop P.output I I.t₁ := by
  refine ⟨I.start_nonneg, le_rfl, fun t ht => output_periodic h ht, υ, ?_⟩
  rw [orbit_slice h hυ, ncard_pair]
  intro heq
  have gap := P.yUp_sub_yDown υ
  have : P.yUp υ = P.yDown υ := (Prod.mk.injEq _ _ _ _ ▸ heq).2
  exact hΩ (by linarith)

/-- With every relay switching, the loop area is `2 Σᵢ wᵢ (αᵢ − βᵢ)`. -/
theorem area_allSwitch (h : P.AllSwitch I) {tp : ℝ} (hl : IsHysteresisLoop P.output I tp) :
    loopArea P.output I = 2 * ∑ i, P.w i * (P.α i - P.β i) := by
  classical
  rw [P.area I hl, switching, Finset.filter_true_of_mem fun i _ => h i]

end FinitePreisach

end ButterflyCharacterization.Domain.Model

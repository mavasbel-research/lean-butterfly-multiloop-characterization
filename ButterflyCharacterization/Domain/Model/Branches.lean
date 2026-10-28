import ButterflyCharacterization.Domain.Model.Preisach
import ButterflyCharacterization.Domain.Model.RelayPeriod

/-!
# Branches, crossovers (Lemma 4.4) and hysteresis loops of finite Preisach operators

No restriction on which relays switch. For a period with `T ≤ t₁` the output at input level
`υ` is `y⁺(υ) = Σ wᵢ relayUpᵢ(υ)` on the ascending branch and `y⁻(υ) = Σ wᵢ relayDownᵢ(υ)`
on the descending branch (`RelayPeriod.lean`). The branch gap only involves the switching
relays whose band contains `υ`:

`y⁺(υ) − y⁻(υ) = −2 Σ_{Ω_υ} wᵢ`, `Ω_υ = {i | u_min < βᵢ, αᵢ < u_max, βᵢ ≤ υ ≤ αᵢ}`.

Consequences:

* **Lemma 4.4** (finite form): on any hysteresis loop (Definition 2.5), `(υ, γ)` is a
  crossover point iff `υ ∈ [u_min, u_max]`, `γ = y⁺(υ)` and `Σ_{Ω_υ} wᵢ = 0`;
* the output is periodic from `t₁`, the orbit from `t₁` is `H⁺ ∪ H⁻`, and `(u, y)` is a
  hysteresis loop as soon as `Σ_{Ω_υ} wᵢ ≠ 0` for one level `υ`.

`Ω_υ` uses closed bands `βᵢ ≤ υ ≤ αᵢ`: with the strict switching of eq. (2) a relay with
`αᵢ = υ` is still `−1` on the ascending branch at level `υ`. The paper's region `Ω_c` in (12)
is written with strict inequalities; for the integral operator (4) the two differ by a set of
measure zero, for a finite operator they do not.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

namespace FinitePreisach

variable {n : ℕ} (P : FinitePreisach n) (I : SimplePeriodicInput)

/-- Output on the ascending branch at input level `υ`. -/
noncomputable def yUp (υ : ℝ) : ℝ := ∑ i, P.w i * relayUp I (P.α i) (P.β i) (P.r₀ i) υ

/-- Output on the descending branch at input level `υ`. -/
noncomputable def yDown (υ : ℝ) : ℝ := ∑ i, P.w i * relayDown I (P.α i) (P.β i) (P.r₀ i) υ

/-- `Ω_υ`: the switching relays whose band `[βᵢ, αᵢ]` contains `υ`. -/
noncomputable def omega (υ : ℝ) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i =>
    I.umin < P.β i ∧ P.α i < I.umax ∧ P.β i ≤ υ ∧ υ ≤ P.α i

variable {P I}

theorem output_rising (hT : I.T ≤ I.t₁) {x : ℝ} (hx : x ∈ Icc I.t₁ I.t₂) :
    P.output I.u x = P.yUp I (I.u x) :=
  Finset.sum_congr rfl fun i _ => by rw [relay, relay_rising (P.ordered i) hT hx]

theorem output_falling {x : ℝ} (hx : x ∈ Icc I.t₂ (I.t₁ + I.T)) :
    P.output I.u x = P.yDown I (I.u x) :=
  Finset.sum_congr rfl fun i _ => by rw [relay, relay_falling (P.ordered i) hx]

/-- Every level between `u_min` and `u_max` is reached on the ascending branch. -/
theorem exists_rising {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₁ I.t₂, I.u x = υ :=
  intermediate_value_Icc I.t₁_lt_t₂.le I.continuous.continuousOn hυ

/-- Every level between `u_min` and `u_max` is reached on the descending branch. -/
theorem exists_falling {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₂ (I.t₁ + I.T), I.u x = υ := by
  have hυ' : υ ∈ Icc (I.u (I.t₁ + I.T)) (I.u I.t₂) := by rw [I.end_eq]; exact hυ
  exact intermediate_value_Icc' I.t₂_lt.le I.continuous.continuousOn hυ'

theorem mem_ascending (hT : I.T ≤ I.t₁) {p : ℝ × ℝ} :
    p ∈ I.ascending (P.output I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = P.yUp I p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, output_rising hT hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := exists_rising hυ
    exact ⟨x, hx, Prod.ext hux (by show P.output I.u x = p.2; rw [output_rising hT hx, hux, h2])⟩

theorem mem_descending {p : ℝ × ℝ} :
    p ∈ I.descending (P.output I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = P.yDown I p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, output_falling hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := exists_falling hυ
    exact ⟨x, hx, Prod.ext hux (by show P.output I.u x = p.2; rw [output_falling hx, hux, h2])⟩

/-- The branch gap: `y⁺(υ) − y⁻(υ) = −2 Σ_{Ω_υ} wᵢ`. -/
theorem yUp_sub_yDown {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    P.yUp I υ - P.yDown I υ = -2 * ∑ i ∈ P.omega I υ, P.w i := by
  classical
  rw [yUp, yDown, ← Finset.sum_sub_distrib, omega, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, relayUp_sub_relayDown (P.ordered i) hυ]
  split_ifs <;> ring

/-- Lemma 4.4 on a period with `T ≤ t₁`. -/
theorem lemma4_4_late (hT : I.T ≤ I.t₁) {υ γ : ℝ} :
    IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = P.yUp I υ ∧ ∑ i ∈ P.omega I υ, P.w i = 0 := by
  unfold IsCrossoverPoint
  rw [mem_inter_iff, mem_ascending hT, mem_descending]
  constructor
  · rintro ⟨⟨hυ, hup⟩, -, hdn⟩
    have gap := P.yUp_sub_yDown hυ
    refine ⟨hυ, hup, ?_⟩
    simp only at hup hdn
    linarith
  · rintro ⟨hυ, hup, hΩ⟩
    have gap := P.yUp_sub_yDown hυ
    refine ⟨⟨hυ, hup⟩, hυ, ?_⟩
    simp only at hup ⊢
    rw [hΩ] at gap
    linarith

/-! ### Moving the period on a hysteresis loop -/

theorem ascending_shift {Φ : SignalOperator} {tp : ℝ} (h : IsHysteresisLoop Φ I tp) :
    I.shift.ascending (Φ I.u) = I.ascending (Φ I.u) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : I.t₁ + I.T ≤ x := hx.1
    have hx2 : x ≤ I.t₂ + I.T := hx.2
    refine ⟨x - I.T, ⟨by linarith, by linarith⟩, ?_⟩
    have hy := h.2.2.1 (x - I.T) (by linarith [h.2.1])
    simp only [sub_add_cancel] at hy
    show (I.u (x - I.T), Φ I.u (x - I.T)) = (I.u x, Φ I.u x)
    rw [I.periodic.sub_eq, hy]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + I.T, ⟨by show I.t₁ + I.T ≤ x + I.T; linarith [hx.1],
      by show x + I.T ≤ I.t₂ + I.T; linarith [hx.2]⟩, ?_⟩
    show (I.u (x + I.T), Φ I.u (x + I.T)) = (I.u x, Φ I.u x)
    rw [I.periodic x, h.2.2.1 x (h.2.1.trans hx.1)]

theorem descending_shift {Φ : SignalOperator} {tp : ℝ} (h : IsHysteresisLoop Φ I tp) :
    I.shift.descending (Φ I.u) = I.descending (Φ I.u) := by
  have h12 := I.t₁_lt_t₂
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : I.t₂ + I.T ≤ x := hx.1
    have hx2 : x ≤ I.t₁ + I.T + I.T := hx.2
    refine ⟨x - I.T, ⟨by linarith, by linarith⟩, ?_⟩
    have hy := h.2.2.1 (x - I.T) (by linarith [h.2.1])
    simp only [sub_add_cancel] at hy
    show (I.u (x - I.T), Φ I.u (x - I.T)) = (I.u x, Φ I.u x)
    rw [I.periodic.sub_eq, hy]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + I.T, ⟨by show I.t₂ + I.T ≤ x + I.T; linarith [hx.1],
      by show x + I.T ≤ I.t₁ + I.T + I.T; linarith [hx.2]⟩, ?_⟩
    show (I.u (x + I.T), Φ I.u (x + I.T)) = (I.u x, Φ I.u x)
    rw [I.periodic x, h.2.2.1 x (h.2.1.trans (h12.le.trans hx.1))]

theorem relayUp_shift (α β r₀ : ℝ) : relayUp I.shift α β r₀ = relayUp I α β r₀ := by
  funext υ
  simp only [relayUp, shift_umin, shift_umax]
  rfl

theorem omega_shift (υ : ℝ) : P.omega I.shift υ = P.omega I υ := by
  simp only [omega, shift_umin, shift_umax]

theorem yUp_shift : P.yUp I.shift = P.yUp I := by
  funext υ
  simp only [yUp, relayUp_shift]

/-- **Lemma 4.4** (finite form). On any hysteresis loop of a finite Preisach operator, a point
at input level `υ` is a crossover point iff the weights of the switching relays whose band
contains `υ` sum to zero. -/
theorem lemma4_4 {tp : ℝ} (hl : IsHysteresisLoop P.output I tp) {υ γ : ℝ} :
    IsCrossoverPoint I (P.output I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = P.yUp I υ ∧ ∑ i ∈ P.omega I υ, P.w i = 0 := by
  have hT : I.shift.T ≤ I.shift.t₁ := by
    show I.T ≤ I.t₁ + I.T
    linarith [I.start_nonneg]
  have key := lemma4_4_late (P := P) hT (υ := υ) (γ := γ)
  unfold IsCrossoverPoint at key ⊢
  change (υ, γ) ∈ I.shift.ascending (P.output I.u) ∩ I.shift.descending (P.output I.u) ↔ _ at key
  rwa [ascending_shift hl, descending_shift hl, shift_umin, shift_umax, yUp_shift,
    omega_shift] at key

/-! ### The orbit and Definition 2.5 -/

theorem output_periodic (hT : I.T ≤ I.t₁) {t : ℝ} (ht : I.t₁ ≤ t) :
    P.output I.u (t + I.T) = P.output I.u t :=
  Finset.sum_congr rfl fun i _ => by rw [relay, relay_periodic hT ht]

theorem output_periodic_nat (hT : I.T ≤ I.t₁) {t : ℝ} (ht : I.t₁ ≤ t) (k : ℕ) :
    P.output I.u (t + k * I.T) = P.output I.u t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc,
      output_periodic hT (by nlinarith [I.period_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]), ih]

/-- From `t₁` on, the orbit is the union of the two branches of one period. -/
theorem orbit_eq (hT : I.T ≤ I.t₁) :
    I.orbit (P.output I.u) I.t₁ = I.ascending (P.output I.u) ∪ I.descending (P.output I.u) := by
  have hTp := I.period_pos
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    set k := ⌊(t - I.t₁) / I.T⌋₊
    have hk1 : (k : ℝ) * I.T ≤ t - I.t₁ := by
      have := Nat.floor_le (div_nonneg (sub_nonneg.mpr ht) hTp.le)
      rwa [le_div_iff₀ hTp] at this
    have hk2 : t - I.t₁ < (k + 1) * I.T := by
      have := Nat.lt_floor_add_one ((t - I.t₁) / I.T)
      rwa [div_lt_iff₀ hTp] at this
    set x := t - k * I.T
    have hx : x ∈ Icc I.t₁ (I.t₁ + I.T) := ⟨by linarith, by linarith⟩
    have hux : I.u t = I.u x := by
      rw [show t = x + k * I.T by ring]
      exact I.periodic.nat_mul k x
    have hyx : P.output I.u t = P.output I.u x := by
      rw [show t = x + k * I.T by ring]
      exact output_periodic_nat hT hx.1 k
    show (I.u t, P.output I.u t) ∈ _
    rw [hux, hyx]
    rcases le_total x I.t₂ with h2 | h2
    · exact Or.inl ⟨x, ⟨hx.1, h2⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨h2, hx.2⟩, rfl⟩
  · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ht.1, rfl⟩
    · exact ⟨t, mem_Ici.mpr (I.t₁_lt_t₂.le.trans ht.1), rfl⟩

/-- The vertical line at `υ` meets the orbit exactly in `(υ, y⁺(υ))` and `(υ, y⁻(υ))`. -/
theorem orbit_slice (hT : I.T ≤ I.t₁) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    {p ∈ I.orbit (P.output I.u) I.t₁ | p.1 = υ} = {(υ, P.yUp I υ), (υ, P.yDown I υ)} := by
  ext ⟨a, b⟩
  simp only [orbit_eq hT, mem_ofPred_eq, mem_union, mem_insert_iff, mem_singleton_iff,
    Prod.mk.injEq, mem_ascending hT, mem_descending]
  constructor
  · rintro ⟨(⟨-, hb⟩ | ⟨-, hb⟩), rfl⟩
    · exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr ⟨rfl, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl ⟨hυ, rfl⟩, rfl⟩
    · exact ⟨Or.inr ⟨hυ, rfl⟩, rfl⟩

/-- **Definition 2.5** holds from `t_p = t₁` (with `T ≤ t₁`) as soon as one level `υ` has
`Σ_{Ω_υ} wᵢ ≠ 0`. -/
theorem isHysteresisLoop (hT : I.T ≤ I.t₁) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax)
    (hΩ : ∑ i ∈ P.omega I υ, P.w i ≠ 0) : IsHysteresisLoop P.output I I.t₁ := by
  refine ⟨I.start_nonneg, le_rfl, fun t ht => output_periodic hT ht, υ, ?_⟩
  rw [orbit_slice hT hυ, ncard_pair]
  intro heq
  have gap := P.yUp_sub_yDown hυ
  have : P.yUp I υ = P.yDown I υ := (Prod.mk.injEq _ _ _ _ ▸ heq).2
  exact hΩ (by linarith)

end FinitePreisach

end ButterflyCharacterization.Domain.Model

import ButterflyCharacterization.Domain.Model.BranchForm
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

theorem output_periodic (hT : I.T ≤ I.t₁) {t : ℝ} (ht : I.t₁ ≤ t) :
    P.output I.u (t + I.T) = P.output I.u t :=
  Finset.sum_congr rfl fun i _ => by rw [relay, relay_periodic hT ht]

variable (P) in
/-- The branch form of a finite Preisach operator on a period with `T ≤ t₁`. -/
noncomputable def branchForm (hT : I.T ≤ I.t₁) : BranchForm P.output I where
  yUp := P.yUp I
  yDown := P.yDown I
  rising _ hx := output_rising hT hx
  falling _ hx := output_falling hx
  periodic _ ht := output_periodic hT ht

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
  rw [(P.branchForm hT).crossover_iff]
  show _ ∧ _ ∧ P.yUp I υ = P.yDown I υ ↔ _
  refine and_congr_right fun hυ => and_congr_right fun _ => ?_
  have gap := P.yUp_sub_yDown hυ
  constructor <;> intro h <;> linarith

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

/-- **Definition 2.5** holds from `t_p = t₁` (with `T ≤ t₁`) as soon as one level `υ` has
`Σ_{Ω_υ} wᵢ ≠ 0`. -/
theorem isHysteresisLoop (hT : I.T ≤ I.t₁) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax)
    (hΩ : ∑ i ∈ P.omega I υ, P.w i ≠ 0) : IsHysteresisLoop P.output I I.t₁ :=
  (P.branchForm hT).isHysteresisLoop hυ fun h => hΩ (by
    have gap := P.yUp_sub_yDown hυ
    have h' : P.yUp I υ = P.yDown I υ := h
    linarith)

end FinitePreisach

end ButterflyCharacterization.Domain.Model

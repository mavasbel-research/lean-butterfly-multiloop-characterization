import ButterflyCharacterization.Domain.Model.Preisach

/-!
# Operators with a branch form

An operator `Φ` has a *branch form* on a simple periodic input `I` when, from `t₁` on, its
output is `T`-periodic, equals `y⁺(u(t))` on the ascending part `[t₁, t₂]` and `y⁻(u(t))` on
the descending part `[t₂, t₁ + T]`. Finite and integral Preisach operators both have one
(for `T ≤ t₁`). From a branch form alone:

* the branches (10)–(11) are the graphs of `y⁺`, `y⁻` over `[u_min, u_max]`;
* the orbit from `t₁` is `H⁺ ∪ H⁻`, and each vertical line meets it in `(υ, y⁺(υ))`,
  `(υ, y⁻(υ))`;
* Definition 2.5 holds as soon as `y⁺(υ) ≠ y⁻(υ)` at one level;
* crossover points are the levels with `y⁺(υ) = y⁻(υ)`.
-/

open Set
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- A branch form of `Φ` on `I`. -/
structure BranchForm (Φ : SignalOperator) (I : SimplePeriodicInput) where
  yUp : ℝ → ℝ
  yDown : ℝ → ℝ
  rising : ∀ x ∈ Icc I.t₁ I.t₂, Φ I.u x = yUp (I.u x)
  falling : ∀ x ∈ Icc I.t₂ (I.t₁ + I.T), Φ I.u x = yDown (I.u x)
  periodic : ∀ t, I.t₁ ≤ t → Φ I.u (t + I.T) = Φ I.u t

namespace BranchForm

variable {Φ : SignalOperator} {I : SimplePeriodicInput} (B : BranchForm Φ I)

/-- Every level between `u_min` and `u_max` is reached on the ascending part. -/
theorem _root_.ButterflyCharacterization.Domain.Abstractions.SimplePeriodicInput.exists_rising
    (I : SimplePeriodicInput) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₁ I.t₂, I.u x = υ :=
  intermediate_value_Icc I.t₁_lt_t₂.le I.continuous.continuousOn hυ

/-- Every level between `u_min` and `u_max` is reached on the descending part. -/
theorem _root_.ButterflyCharacterization.Domain.Abstractions.SimplePeriodicInput.exists_falling
    (I : SimplePeriodicInput) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    ∃ x ∈ Icc I.t₂ (I.t₁ + I.T), I.u x = υ := by
  have hυ' : υ ∈ Icc (I.u (I.t₁ + I.T)) (I.u I.t₂) := by rw [I.end_eq]; exact hυ
  exact intermediate_value_Icc' I.t₂_lt.le I.continuous.continuousOn hυ'

theorem mem_ascending {p : ℝ × ℝ} :
    p ∈ I.ascending (Φ I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = B.yUp p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, B.rising x hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := I.exists_rising hυ
    exact ⟨x, hx, Prod.ext hux (by show Φ I.u x = p.2; rw [B.rising x hx, hux, h2])⟩

theorem mem_descending {p : ℝ × ℝ} :
    p ∈ I.descending (Φ I.u) ↔ p.1 ∈ Icc I.umin I.umax ∧ p.2 = B.yDown p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.bounds x, B.falling x hx⟩
  · rintro ⟨hυ, h2⟩
    obtain ⟨x, hx, hux⟩ := I.exists_falling hυ
    exact ⟨x, hx, Prod.ext hux (by show Φ I.u x = p.2; rw [B.falling x hx, hux, h2])⟩

/-- Crossover points (Definition 4.1) are the levels where the branches meet. -/
theorem crossover_iff {υ γ : ℝ} :
    IsCrossoverPoint I (Φ I.u) (υ, γ) ↔
      υ ∈ Icc I.umin I.umax ∧ γ = B.yUp υ ∧ B.yUp υ = B.yDown υ := by
  unfold IsCrossoverPoint
  rw [mem_inter_iff, B.mem_ascending, B.mem_descending]
  constructor
  · rintro ⟨⟨hυ, hup⟩, -, hdn⟩
    exact ⟨hυ, hup, hup.symm.trans hdn⟩
  · rintro ⟨hυ, hup, heq⟩
    exact ⟨⟨hυ, hup⟩, hυ, hup.trans heq⟩

theorem periodic_nat (B : BranchForm Φ I) {t : ℝ} (ht : I.t₁ ≤ t) (k : ℕ) : Φ I.u (t + k * I.T) = Φ I.u t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc,
      B.periodic _ (by nlinarith [I.period_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]), ih]

/-- From `t₁` on, the orbit is the union of the two branches of one period. -/
theorem orbit_eq (B : BranchForm Φ I) : I.orbit (Φ I.u) I.t₁ = I.ascending (Φ I.u) ∪ I.descending (Φ I.u) := by
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
    have hyx : Φ I.u t = Φ I.u x := by
      rw [show t = x + k * I.T by ring]
      exact B.periodic_nat hx.1 k
    show (I.u t, Φ I.u t) ∈ _
    rw [hux, hyx]
    rcases le_total x I.t₂ with h2 | h2
    · exact Or.inl ⟨x, ⟨hx.1, h2⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨h2, hx.2⟩, rfl⟩
  · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ht.1, rfl⟩
    · exact ⟨t, mem_Ici.mpr (I.t₁_lt_t₂.le.trans ht.1), rfl⟩

/-- The vertical line at `υ` meets the orbit exactly in `(υ, y⁺(υ))` and `(υ, y⁻(υ))`. -/
theorem orbit_slice (B : BranchForm Φ I) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    {p ∈ I.orbit (Φ I.u) I.t₁ | p.1 = υ} = {(υ, B.yUp υ), (υ, B.yDown υ)} := by
  ext ⟨a, b⟩
  simp only [B.orbit_eq, mem_ofPred_eq, mem_union, mem_insert_iff, mem_singleton_iff,
    Prod.mk.injEq, B.mem_ascending, B.mem_descending]
  constructor
  · rintro ⟨(⟨-, hb⟩ | ⟨-, hb⟩), rfl⟩
    · exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr ⟨rfl, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl ⟨hυ, rfl⟩, rfl⟩
    · exact ⟨Or.inr ⟨hυ, rfl⟩, rfl⟩

/-- **Definition 2.5** holds from `t_p = t₁` as soon as the branches differ at one level. -/
theorem isHysteresisLoop {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) (hne : B.yUp υ ≠ B.yDown υ) :
    IsHysteresisLoop Φ I I.t₁ := by
  refine ⟨I.start_nonneg, le_rfl, B.periodic, υ, ?_⟩
  rw [B.orbit_slice hυ, ncard_pair]
  intro heq
  exact hne (Prod.mk.injEq _ _ _ _ ▸ heq).2

end BranchForm

end ButterflyCharacterization.Domain.Model

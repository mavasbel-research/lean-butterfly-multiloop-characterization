import ButterflyCharacterization.Domain.Abstractions.Operator

/-!
# Hysteresis loops, signed area, butterfly and multiloop operators

TAC 2022: eq. (1), Definitions 2.5 and 2.7, the clockwise/counterclockwise notions of §II-A,
eqs. (10)–(11), Definitions 4.1 and 4.3.
-/

open Set

namespace ButterflyCharacterization.Domain.Abstractions

/-- **Eq. (1)**, signed area of `(u, y)` on `[t₁, t₂]`, written `−∫ y u̇`. On a closed `C¹`
curve this equals `½ ∫ (u ẏ − y u̇)` (`Model.SignedArea.signedArea_eq_green`); unlike
`½ ∫ (u ẏ − y u̇)` with `ẏ = deriv y`, it is also the correct (Stieltjes) area when `y` jumps,
as relay outputs do. -/
noncomputable def signedArea (u y : ℝ → ℝ) (t₁ t₂ : ℝ) : ℝ := -∫ τ in t₁..t₂, y τ * deriv u τ

/-- The input of Definition 2.5: `T`-periodic, with one minimum (at `t₁`) and one maximum
(at `t₂`) per period, nondecreasing on `[t₁, t₂]` and nonincreasing on `[t₂, t₁ + T]`.
Narrower than the paper in one respect: `u` is `C¹` (paper: absolutely continuous). -/
structure SimplePeriodicInput where
  u : ℝ → ℝ
  u' : ℝ → ℝ
  T : ℝ
  t₁ : ℝ
  t₂ : ℝ
  period_pos : 0 < T
  periodic : Function.Periodic u T
  hasDerivAt : ∀ x, HasDerivAt u (u' x) x
  continuous_deriv : Continuous u'
  start_nonneg : 0 ≤ t₁
  t₁_lt_t₂ : t₁ < t₂
  t₂_lt : t₂ < t₁ + T
  rising : MonotoneOn u (Icc t₁ t₂)
  falling : AntitoneOn u (Icc t₂ (t₁ + T))

namespace SimplePeriodicInput

variable (I : SimplePeriodicInput)

/-- `u_min`. -/
def umin : ℝ := I.u I.t₁

/-- `u_max`. -/
def umax : ℝ := I.u I.t₂

/-- The orbit `H_{u,y} = {(u(t), y(t)) | t ∈ [t_p, ∞)}`. -/
def orbit (y : ℝ → ℝ) (tp : ℝ) : Set (ℝ × ℝ) := (fun t => (I.u t, y t)) '' Ici tp

/-- **Eq. (10)**, the ascending branch `H⁺ = {(u(t), y(t)) | t ∈ [t₁, t₂]}`. -/
def ascending (y : ℝ → ℝ) : Set (ℝ × ℝ) := (fun t => (I.u t, y t)) '' Icc I.t₁ I.t₂

/-- **Eq. (11)**, the descending branch `H⁻ = {(u(t), y(t)) | t ∈ [t₂, t₁ + T]}`. -/
def descending (y : ℝ → ℝ) : Set (ℝ × ℝ) := (fun t => (I.u t, y t)) '' Icc I.t₂ (I.t₁ + I.T)

end SimplePeriodicInput

/-- **Definition 2.5.** `(u, Φ(u))` forms a hysteresis loop from `t_p`: the output is
periodic on `[t_p, ∞)`, and some vertical line meets the orbit in exactly two points. We
also require `t_p ≤ t₁`, so that the period `[t₁, t₁ + T]` used for the area lies in the
periodic regime (Definition 2.7 uses `t₁ ≥ t_p`). -/
def IsHysteresisLoop (Φ : SignalOperator) (I : SimplePeriodicInput) (tp : ℝ) : Prop :=
  0 ≤ tp ∧ tp ≤ I.t₁ ∧ (∀ t, tp ≤ t → Φ I.u (t + I.T) = Φ I.u t) ∧
    ∃ υ : ℝ, {p ∈ I.orbit (Φ I.u) tp | p.1 = υ}.ncard = 2

/-- Loop area `A` of Definition 2.7: eq. (1) over `[t₁, t₁ + T]`. -/
noncomputable def loopArea (Φ : SignalOperator) (I : SimplePeriodicInput) : ℝ :=
  signedArea I.u (Φ I.u) I.t₁ (I.t₁ + I.T)

/-- §II-A: `Φ` exhibits counterclockwise behaviour if some hysteresis loop has `A > 0`. -/
def ExhibitsCounterclockwise (Φ : SignalOperator) : Prop :=
  ∃ I tp, IsHysteresisLoop Φ I tp ∧ 0 < loopArea Φ I

/-- §II-A: `Φ` exhibits clockwise behaviour if some hysteresis loop has `A < 0`. -/
def ExhibitsClockwise (Φ : SignalOperator) : Prop :=
  ∃ I tp, IsHysteresisLoop Φ I tp ∧ loopArea Φ I < 0

/-- **Definition 2.7.** A butterfly hysteresis operator: a hysteresis operator with a
hysteresis loop of zero signed area. -/
def IsButterflyOperator (Φ : SignalOperator) : Prop :=
  IsHysteresisOperator Φ ∧ ∃ I tp, IsHysteresisLoop Φ I tp ∧ loopArea Φ I = 0

/-- **Definition 4.1.** A crossover point lies on both branches. -/
def IsCrossoverPoint (I : SimplePeriodicInput) (y : ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  p ∈ I.ascending y ∩ I.descending y

/-- **Definition 4.3.** A multiloop hysteresis operator: a hysteresis operator with a
hysteresis loop having a maximal connected subset of `H⁺ ∩ H⁻` that contains no point with
`u_c = u_min` or `u_c = u_max`. Maximal connected subsets are the connected components
`connectedComponentIn (H⁺ ∩ H⁻) p` of its points. -/
def IsMultiloopOperator (Φ : SignalOperator) : Prop :=
  IsHysteresisOperator Φ ∧ ∃ I tp, IsHysteresisLoop Φ I tp ∧
    ∃ p ∈ I.ascending (Φ I.u) ∩ I.descending (Φ I.u),
      ∀ q ∈ connectedComponentIn (I.ascending (Φ I.u) ∩ I.descending (Φ I.u)) p,
        q.1 ≠ I.umin ∧ q.1 ≠ I.umax

end ButterflyCharacterization.Domain.Abstractions

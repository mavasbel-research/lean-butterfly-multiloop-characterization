# lean-butterfly-multiloop-characterization

A Lean 4 / Mathlib formalization of

> M. A. Vasquez-Beltran, B. Jayawardhana, R. Peletier, "On the Characterization of Butterfly
> and Multiloop Hysteresis Behavior", *IEEE Transactions on Automatic Control*, vol. 67,
> no. 7, pp. 3494–3506, July 2022. DOI: [10.1109/TAC.2021.3109533](https://doi.org/10.1109/TAC.2021.3109533)

* Toolchain: `leanprover/lean4:v4.35.0` (`/home/mavasbel/Dev/repos/research/lean-butterfly-multiloop-characterization/lean-toolchain`)
* Mathlib: `v4.35.0` (`/home/mavasbel/Dev/repos/research/lean-butterfly-multiloop-characterization/lake-manifest.json`)
* Plan of this version: `/home/mavasbel/Dev/docs/plans/2026-10-26-23-42-phase-3-faithful-rework-butterfly-multiloop-plan.md`

## 1. What is proved

Every theorem below is checked by the Lean kernel and, by the axiom audit
(`tests/unit/AxiomAudit.lean`), uses only `propext`, `Classical.choice` and `Quot.sound`:
no `sorry`, no added axiom, no `native_decide`. Statements are pinned verbatim in
`tests/unit/TestStatements.lean`.

**Models.** Signals are functions `ℝ → ℝ` read on `[0, ∞)`. The relay is eq. (2) itself, in
closed form (`ccwRelay`). Inputs are `C¹` simple periodic inputs (`SimplePeriodicInput`:
`T`-periodic, nondecreasing from the minimum at `t₁` to the maximum at `t₂`, nonincreasing
back). Two Preisach operators: the finite one `Σᵢ wᵢ R_{αᵢ,βᵢ}` (`FinitePreisach`) and the
integral operator (4) (`IntegralPreisach`: Lebesgue-integrable weight `μ` vanishing off
`α > β`, measurable initial states in `[−1, 1]`).

| Paper | Lean | Status |
|---|---|---|
| Def. 2.1 time transformation | `TimeTransformation` (continuous, nondecreasing, `φ 0 = 0`, `φ → ∞`) | as in the paper |
| Def. 2.2 rate independence, Def. 2.3 causality, Def. 2.4 hysteresis operator | `IsRateIndependent`, `IsCausal`, `IsHysteresisOperator` | as in the paper, for all inputs `ℝ → ℝ` (paper: AC) |
| eq. (2) counterclockwise relay, α > β | `ccwRelay`; `ccwRelay_of_gt`, `ccwRelay_of_lt`, `ccwRelay_zero`, `ccwRelay_left_limit` (each line of (2)) | proved; left-limit line for continuous `u` |
| relay is a hysteresis operator | `ccwRelay_causal`, `ccwRelay_rateIndependent`, `ccwRelay_hysteresis` | proved |
| eq. (3) clockwise relay | `cwRelay := −ccwRelay` | as §II-B states |
| eq. (1) signed area | `signedArea u y t₁ t₂ := −∫ y u̇`; `signedArea_eq_green`: equals `½∫(u ẏ − y u̇)` on closed `C¹` curves | proved |
| Def. 2.5 hysteresis loop (incl. `card = 2` condition) | `IsHysteresisLoop` | as in the paper, plus `t_p ≤ t₁` |
| Def. 2.7 butterfly operator | `IsButterflyOperator` | as in the paper |
| Def. 4.1 crossover point, (10)–(11) branches | `IsCrossoverPoint`, `ascending`, `descending` | as in the paper |
| Def. 4.3 multiloop operator (maximal connected subsets) | `IsMultiloopOperator` via `connectedComponentIn` | as in the paper |
| **Lemma 3.1** | `lemma3_1` | **proved** for `C¹` inputs, period `[t₁, t₁+T]` with `t₁ ≥ T` |
| **Remark 3.2** | `remark3_2` | **proved** |
| finite Preisach is a hysteresis operator | `FinitePreisach.output_hysteresis` | proved |
| area `A = 2∑_{switching} wᵢ(αᵢ − βᵢ)` (finite form of the area formula in the proof of Thm. 3.3) | `FinitePreisach.area` | proved, on any hysteresis loop |
| §III: μ ≥ 0 ⇒ no clockwise loop; μ ≤ 0 ⇒ no counterclockwise loop | `not_clockwise_of_nonneg`, `not_counterclockwise_of_nonpos` | proved, finite form |
| eq. (4) is a hysteresis operator | `IntegralPreisach.output_hysteresis` | proved |
| area of a loop of (4): `A = ∬ μ(α,β)·2(α−β)` over `u_min < β, α < u_max` | `IntegralPreisach.area` (Fubini + Lemma 3.1) | proved, on any hysteresis loop |
| **Thm. 3.3** | `IntegralPreisach.theorem3_3` (integral operator); `theorem3_3_step_max/min` (finite) | **proved, with the limits as hypotheses**: the paper derives `A(β₁, M) → +∞` and `A(m, α₁) → −∞` from the two-sided sign and (5)–(6); that derivation is not formalized. The area is proved continuous in `u_max` and `u_min` (dominated convergence) and the IVT gives the zero-area loop |
| **Cor. 3.4** | `IntegralPreisach.corollary3_4` (integral), `FinitePreisach.corollary3_4` (finite) | **proved**, with the reflection about `B` and the input condition `u_min + u_max = κ` (see §2) |
| Cor. 3.4 is satisfiable | `antisymWitness_isButterfly`: `μ = 𝟙_{(0,1)×(−1,0)} − 𝟙_{(1,2)×(0,1)}` | an integral operator that is a butterfly operator |
| **Lemma 4.4** | `FinitePreisach.lemma4_4` | **proved, finite form**, on any hysteresis loop; `Ω_υ` = switching relays with `βᵢ ≤ υ ≤ αᵢ` (closed bands, see `Branches.lean`) |
| **Thm. 4.7** | `FinitePreisach.theorem4_7` | **proved, finite form**, hypotheses on relays and weights only, as in the paper |
| every relay over one period | `relay_rising`, `relay_falling`, `relay_periodic` (`RelayPeriod.lean`) | proved for switching, down-only, up-only and frozen relays |
| Definitions satisfiable | `twoRelay_isButterfly`, `twoRelay_isMultiloop` | a 2-relay operator that is both |
| Cor. 5.1 (Lur'e) | — | not formalized (needs LaSalle's invariance principle) |

## 2. Findings about the paper's text

Both are proved in Lean, in `ButterflyCharacterization/Domain/Model/Butterfly.lean`.

1. **Cor. 3.4 antisymmetry.** The paper writes "μ antisymmetric with respect to B, i.e.,
   μ(α, β) = −μ(−α, −β)". For `(α, β)` in the Preisach plane (`α > β`), `(−α, −β)` has
   `−α < −β`, so it is not in the plane; and the map ignores `κ`. The reflection about
   `B = {α = −β + κ}` that maps the plane to itself is `(α, β) ↦ (κ − β, κ − α)`; the Lean
   statement uses it.
2. **Cor. 3.4 input.** The paper says "it suffices to have a periodic input signal u whose
   maximum and minimum satisfy u_max = −u_min + 2κ". `corollary3_4_paper_input_counterexample`:
   relays `(1, −1)` with weight `1` and `(2, 0)` with weight `−1` are antisymmetric about
   `α + β = 1` (`κ = 1`); the input `u_min = −1/2`, `u_max = 5/2` satisfies the paper's rule,
   and the loop area is `−4`. With `u_min + u_max = κ` the area is `0`
   (`corollary3_4_symmetric_input`, `FinitePreisach.corollary3_4`).

## 3. Layout

```text
/home/mavasbel/Dev/repos/research/lean-butterfly-multiloop-characterization
├── ButterflyCharacterization.lean             # root: imports every module
├── ButterflyCharacterization/
│   ├── Domain/
│   │   ├── Abstractions/
│   │   │   ├── Operator.lean     # Defs. 2.1–2.4
│   │   │   ├── Loop.lean         # eq. (1), Def. 2.5, 2.7, (10)–(11), Def. 4.1, 4.3
│   │   │   └── Ports.lean        # inbound LoopAnalysisPort; outbound EnsembleSourcePort, TelemetryPort
│   │   ├── Model/                # theorems over ℝ
│   │   │   ├── Relay.lean        # eq. (2), (3); hysteresis operator; periodicity
│   │   │   ├── SignedArea.lean   # eq. (1) ↔ Green form; piecewise integrals
│   │   │   ├── RelayLoop.lean    # Lemma 3.1, Remark 3.2
│   │   │   ├── RelayPeriod.lean  # every relay over one period, periodicity
│   │   │   ├── Preisach.lean     # finite Preisach; area formula; §III signs
│   │   │   ├── Branches.lean     # branches, Lemma 4.4, Def. 2.5 for finite Preisach
│   │   │   ├── CosineInput.lean  # a concrete simple periodic input
│   │   │   ├── BranchForm.lean   # branch form of an operator: orbit, Def. 2.5, crossovers
│   │   │   ├── IntegralPreisach.lean  # eq. (4); hysteresis operator; area by Fubini
│   │   │   ├── Theorem33.lean    # branches of (4); area continuous in u_min/u_max; Thm. 3.3
│   │   │   ├── Corollary34.lean  # Cor. 3.4 for (4); antisymmetric witness
│   │   │   ├── Butterfly.lean    # Thm. 3.3 step, Cor. 3.4 (finite), findings, butterfly witness
│   │   │   └── Multiloop.lean    # Thm. 4.7, multiloop witness
│   │   └── Services/
│   │       └── LoopAnalysisService.lean   # Float simulation + closed forms; use case runAnalysis
│   ├── Adapters/
│   │   ├── Inbound/CliController.lean     # butterfly_cli
│   │   └── Outbound/{BuiltinEnsembles,ConsoleTelemetry}.lean
│   └── Main.lean
├── tests/
│   ├── unit/       # build time: AxiomAudit, TestStatements (pinned statements, non-vacuity), TestService
│   ├── component/  # TestAdapters: adapters through their ports
│   ├── live/       # TestCli: the built executable as a subprocess
│   ├── e2e/        # TestParity: use case through all ports; Float vs. the values proved in Lean
│   ├── support/AxiomAuditCore.lean
│   └── Main.lean   # run-time runner
└── lakefile.lean   # targets: ButterflyCharacterization (default), Tests, run_tests, butterfly_cli
```

## 4. Commands

```bash
cd /home/mavasbel/Dev/repos/research/lean-butterfly-multiloop-characterization
lake exe cache get                      # Mathlib prebuilt files (once)
lake build                              # all theorems
lake build Tests                        # unit tier: axiom audit, pinned statements, service
lake build butterfly_cli run_tests      # executables
lake exe run_tests                      # component, live, e2e tiers (needs butterfly_cli built)
```

`butterfly_cli list` prints the built-in ensembles;
`butterfly_cli <ensemble> <u_min> <u_max> [samples]` (default 1000 samples per period,
minimum 4) simulates two periods of `(m + M)/2 − (M − m)/2 · cos t` and prints the area from
the proved formula and the simulated shoelace area of the second period. Exit codes: `0`
success, `1` bad arguments or unknown ensemble.

```text
$ lake exe butterfly_cli two-relay -1 1
ensemble         : two-relay
input            : u_min = -1.000000, u_max = 1.000000, 1000 samples/period
switching relays : 2
area, formula    : 0.000000   (2 Σ_switching w (α − β), FinitePreisach.area)
area, simulated  : 0.002728   (shoelace over the 2nd period)
crossover levels : 900 sampled interior levels with Σ_Ω w = 0

$ lake exe butterfly_cli reflected-pair -0.5 2.5
...
area, formula    : -4.000000   (2 Σ_switching w (α − β), FinitePreisach.area)
area, simulated  : -4.010092   (shoelace over the 2nd period)

$ lake exe butterfly_cli positive -1 1
...
area, formula    : 2.000000   (2 Σ_switching w (α − β), FinitePreisach.area)
area, simulated  : 2.003617   (shoelace over the 2nd period)
```

## 5. Verification (measured 2026-10-27)

| Tier | Command | Result |
|---|---|---|
| unit | `lake build Tests` | axiom audit: **459 declarations in 21 modules, all standard**; 14 statements pinned; 4 non-vacuity checks; 5 service outputs pinned |
| component | `lake exe run_tests` | 4/4 PASS |
| live | `lake exe run_tests` | 8/8 PASS (CLI output and exit codes) |
| e2e | `lake exe run_tests` | 10/10 PASS: the Float formula equals the Lean-proved area in 4 cases; simulated error falls from 100 to 1000 samples (e.g. two-relay 0.016048 → 0.002728) |

Mutation checks run on 2026-10-27, then reverted: adding `theorem mutant : (1 : ℝ) = 2 := sorry`
makes the axiom audit fail (`[(…mutant, [sorryAx])]`); changing the simulated relay to switch
at `u ≥ α` makes `tests/unit/TestService.lean` fail.

Lean has no line-coverage tool; the axiom audit's count covers every declaration of every
module by construction.

## 6. Known gaps

* Thm. 3.3: the step from the sign of `μ` and (5)–(6) to the two area limits is not
  formalized (the limits are hypotheses). Interfaces `𝓘` are represented by the initial
  states `r₀` only.
* Lemma 4.4 and Thm. 4.7 are proved for finite ensembles only.
* Inputs are `C¹` (paper: absolutely continuous).
* The `Float` simulation is not proved correct; the e2e tier compares it with the proved values.
* Cor. 5.1 is not formalized.

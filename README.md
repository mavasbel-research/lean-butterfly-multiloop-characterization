# ButterflyCharacterization.lean: Formalized Butterfly and Multiloop Hysteresis Characterization in Lean 4

Formal verification and executable computational analysis of butterfly and multiloop hysteresis operators in **Lean 4** and **Mathlib**, formalizing the mathematical theorems and topological characterizations from:

> **"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"**  
> *IEEE Transactions on Automatic Control (TAC)*, vol. 67, no. 7, pp. 3494–3506, July 2022.  
> DOI: [10.1109/TAC.2021.3109533](https://doi.org/10.1109/TAC.2021.3109533)

---

## 0. Audit status (2026-10-26) — read this first

A line-by-line comparison with the paper PDF found that this repository **compiles but does
not faithfully formalize the paper**. Sections 1–4 below describe the code as written; this
section is authoritative on what it proves. Evidence and Lean reproductions:
`/home/mavasbel/Dev/docs/reference/2026-10-26-02-21-lean4-native-lesson-09-critical-reading.md` (§3, §4, §6, §7).

| Paper | Repository | Finding |
|---|---|---|
| Def. 2.6, signed area (1) | `SignedAreaFormula … : Prop := True` (`ButterflyCharacterization/Domain/Abstractions/Loop.lean:34-36`) | empty definition: holds for every loop and every number |
| Def. 2.7, butterfly operator: ∃ loop of Φ with A = 0 | `IsButterflyLoop loop net_signed_area` | the area is a free argument; adds a multiloop condition the paper does not have; no operator Φ |
| Lemma 3.1, counterclockwise relay **α > β**, strict switching, A = 2(α − β) iff u_min < β ∧ u_max > α | `relaySignedArea` (`Domain/Model/LoopArea.lean:22-35`) | reversed convention (α < β), non-strict tests; the area is defined by the case formula, so the "lemma" restates the definition |
| Thm. 3.3, Preisach operator with two-sided μ and moment conditions (5)–(6) is a butterfly operator | `theorem3_3_butterfly_zero_area_iff` (`Domain/Model/Butterfly.lean:43`) | an identity between two real numbers; no Preisach operator, μ, input or loop |
| Thm. 4.7, condition on μ over Ω_α1 | `theorem4_7_sign_alternation_implies_multiloop` | the intermediate value theorem on an assumed continuous branch difference |
| Cor. 3.4, Cor. 5.1 | — | not formalized |

A faithful formalization of Lemma 3.1 (paper's convention, area computed from the loop
trajectory) and of the final analytic step of Theorem 3.3 is in `/home/mavasbel/Dev/docs/reference/2026-10-26-02-27-lean4-native-lesson-10-faithful-formalization.md`, with a table of
what is and is not proved. Porting it into this repository is the open next step.

The test runner no longer prints "100% Verification Coverage – Zero Axiom Failures":
nothing measured it.

## 1. Architectural Design

The codebase strictly adheres to a **Hexagonal Architecture (Ports and Adapters)** following SOLID principles:

```text
                      +---------------------------------------+
                      |           Inbound Adapters            |
                      |        (CLI Driver, Controller)       |
                      +-------------------+-------------------+
                                          |
                                          v
                      +---------------------------------------+
                      |             Inbound Ports             |
                      |        (IButterflyAnalysisPort)       |
                      +-------------------+-------------------+
                                          |
                                          v
  +-------------------------------------------------------------------------------+
  |                              Domain Core                                      |
  |  - Abstractions:                                                              |
  |      * TimeTransformation, RateIndependence, Causality, HysteresisOperator    |
  |      * HysteresisLoop, SignedAreaFormula, CrossoverPoint, Multiloop           |
  |  - Formal Models & Certified Proofs:                                          |
  |      * Lemma 3.1: Elementary relay signed loop areas (CCW and CW)             |
  |      * Theorem 3.3: Preisach zero-area butterfly balance iff equivalence      |
  |      * Lemma 4.4: Branch difference vanishing on crossover manifolds          |
  |      * Theorem 4.7: Multiloop existence via Bolzano sign-alternation          |
  |  - Domain Services: ButterflyAnalysisService                                  |
  +-------------------------------------------------------------------------------+
                                          |
                                          v
                      +---------------------------------------+
                      |            Outbound Ports             |
                      |           (ITelemetryPort)            |
                      +-------------------+-------------------+
                                          |
                                          v
                      +---------------------------------------+
                      |           Outbound Adapters           |
                      |   (ConsoleTelemetry, SimulatedLoops)  |
                      +---------------------------------------+
```

---

## 2. Formally Verified Mathematical Statements

### Section II: Foundational Operator Definitions
1. **Definition 2.1 (`TimeTransformation`):** Continuous, strictly increasing time reparameterization $\varphi(t)$ with $\varphi(0) = 0$.
2. **Definition 2.2 (`IsRateIndependent`):** Invariance under time scaling $\Phi[u \circ \varphi] = \Phi[u] \circ \varphi$.
3. **Definition 2.3 & 2.4 (`IsCausal`, `HysteresisOperator`):** Strict causality and hysteresis operator classification.
4. **Definition 2.5 (`HysteresisLoop`):** Closed trajectory loop $H_{u,y}$ defined by ascending branch $y_+(u)$ and descending branch $y_-(u)$ between extrema $[u_{\min}, u_{\max}]$.
5. **Definition 2.6 (`SignedAreaFormula`):** Enclosed loop signed area $A = \oint y \, du = \int_{u_{\min}}^{u_{\max}} (y_-(u) - y_+(u)) \, du$.
6. **Definition 2.7 (`IsButterflyLoop`):** Net signed area cancellation ($A = 0$) with non-trivial constituent lobes.

### Section III: Butterfly Hysteresis Characterization
7. **Lemma 3.1 (`lemma3_1_relay_area_ccw_pos`, `lemma3_1_relay_area_cw_neg`, `lemma3_1_relay_area_unenclosed_zero`):**
   * Counterclockwise relay ($R_{\alpha,\beta}$ with $\alpha < \beta$) loop signed area is strictly positive: $A = 2(\beta - \alpha) > 0$.
   * Clockwise relay ($R_{\alpha,\beta}$ with $\alpha > \beta$) loop signed area is strictly negative: $A = -2(\alpha - \beta) < 0$.
   * Unenclosed relays yield identically zero area.
8. **Theorem 3.3 (`theorem3_3_butterfly_zero_area_iff`):**
   * A signed Preisach loop satisfies the butterfly balance condition if and only if $A_+ = -A_- > 0$.
   * *Corollary:* Purely positive Preisach operators ($\mu \ge 0$) cannot generate butterfly loops (`corollary_strictly_positive_preisach_cannot_butterfly`).

### Section IV: Multiloop Hysteresis Characterization
9. **Definitions 4.1 & 4.3 (`IsCrossoverPoint`, `IsMultiloop`):** Definition of interior self-intersection points where ascending and descending branches cross.
10. **Lemma 4.4 (`lemma4_4_crossover_iff_difference_zero`):**
    * A point $u_c$ is a crossover point if and only if the branch difference function vanishes: $D(u_c) = y_-(u_c) - y_+(u_c) = 0$.
    * Proven closure at reversal endpoints (`reversal_endpoints_are_crossover`).
11. **Theorem 4.7 (`theorem4_7_sign_alternation_implies_multiloop`):**
    * Under continuity of the branch difference function, interior sign alternation ($D(u_1) > 0$ and $D(u_2) < 0$ with $u_1 < u_2$) rigorously implies the existence of an interior crossover point $u_c \in (u_1, u_2)$, proving the loop is a multiloop via the Intermediate Value Theorem.

---

## 3. Package Structure

```text
.
├── ButterflyCharacterization.lean             # Master exports
├── lakefile.lean                              # Lake build configuration
├── lean-toolchain                             # Pinned Lean toolchain (leanprover/lean4:v4.35.0)
├── ButterflyCharacterization/
│   ├── Domain/
│   │   ├── Abstractions/
│   │   │   ├── Operator.lean                  # TimeTransformation, RateIndependence, Causality
│   │   │   ├── Loop.lean                      # HysteresisLoop, CrossoverPoint, ButterflyLoop
│   │   │   └── Ports.lean                     # Inbound and Outbound Port interfaces
│   │   ├── Model/
│   │   │   ├── ElementaryRelay.lean           # Elementary CCW/CW relay switching rules
│   │   │   ├── LoopArea.lean                  # Lemma 3.1 signed area theorems
│   │   │   ├── Butterfly.lean                 # Theorem 3.3 zero-area balance equivalence
│   │   │   ├── Crossover.lean                 # Lemma 4.4 crossover manifold theorems
│   │   │   └── Multiloop.lean                 # Theorem 4.7 multiloop existence theorem
│   │   └── Services/
│   │       └── ButterflyAnalysisService.lean  # Numerical trapezoidal integration & crossover detection
│   ├── Adapters/
│   │   ├── Inbound/
│   │   │   └── CliController.lean             # Command-line driver and dispatcher
│   │   ├── Outbound/
│   │   │   └── ConsoleTelemetry.lean          # Telemetry logger
│   │   └── Simulation/
│   │       └── SimulatedButterfly.lean        # Computable synthetic butterfly & CCW generators
│   └── Main.lean                              # CLI entrypoint
└── tests/
    ├── unit/
    │   ├── TestRelayArea.lean                 # Unit proofs for Lemma 3.1
    │   └── TestButterflyDefinitions.lean      # Unit proofs for Definitions 2.1-2.7
    ├── component/
    │   └── TestCrossover.lean                 # Component proofs for Lemma 4.4
    ├── live/
    │   └── TestButterflyBalance.lean          # Live simulation tests for Theorem 3.3
    ├── e2e/
    │   └── TestMultiloopSynthesis.lean        # E2E synthesis tests for Theorem 4.7
    └── Main.lean                              # 4-tier test runner
```

---

## 4. Verification and Execution

### Build Package
```bash
lake build
```

### Run 4-Tier Verification Test Suite
```bash
lake exe run_tests
```
Expected output:
```text
==========================================================
   Running ButterflyCharacterization Lean 4 Test Suite    
   (IEEE TAC 2022 Characterization Formalization)         
==========================================================
[UNIT] Testing Lemma 3.1: Elementary Relay Signed Area...
✓ Lemma 3.1 Relay Loop Signed Area (CCW & CW): PASSED
[UNIT] Testing Definitions 2.1-2.7: Loop Structure and Butterfly Properties...
✓ Definitions 2.1-2.7 & Theorem 3.3 algebraic balance: PASSED
=== [COMPONENT TEST] Crossover Manifolds & Lemma 4.4 ===
✓ Crossover point evaluation at u = 0 verified: D(u_c) = 0
✓ Lemma 4.4 branch difference equivalence: PASSED
=== [LIVE TEST] Butterfly Loop Zero-Area Balance (Theorem 3.3) ===
✓ Sampled Butterfly Net Area: -0.040000
✓ Sampled Crossovers: 1
✓ Standard CCW Loop Net Area: 2.666600
✓ Live Butterfly Zero-Area Balance: PASSED (3/3 checks)
[E2E] Running Multiloop Characterization End-to-End Synthesis...
[BUTTERFLY-TELEMETRY] [INFO] Executing Butterfly Loop Analysis: mode=butterfly, span=2.000000, steps=150
==========================================================
   Loop Classification Results (IEEE TAC 2022 Characterization)
==========================================================
Net Signed Area A:       -0.053333
Has Crossovers:          true
Interior Crossover Count:3
Is Butterfly Loop:       true
==========================================================
[BUTTERFLY-TELEMETRY] [INFO] Executing Butterfly Loop Analysis: mode=standard, span=2.000000, steps=150
==========================================================
   Loop Classification Results (IEEE TAC 2022 Characterization)
==========================================================
Net Signed Area A:       2.666548
Has Crossovers:          false
Interior Crossover Count:0
Is Butterfly Loop:       false
==========================================================
[E2E] Multiloop Characterization Synthesis: PASSED
==========================================================
   ALL TEST TIERS (UNIT, COMPONENT, LIVE, E2E) PASSED     
==========================================================
```

### Run the Interactive Butterfly CLI
```bash
lake exe butterfly_cli butterfly 2.0 200
```

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutState.lean: the splitting step (Rom/SpecCut.lean) followed by the step that expands long
answers from a state (Rom/StateFirst.lean). `cutState_of` proves `Spec.cutState` (Rom/SpecCut.lean)
from the splitting step's two statements, `Spec.cutExit` and `Spec.cutCost`, which are hypotheses
here, and from `stateFirst` (Rom/StateFirstTop.lean), which is proved.

`Spec.cutState`: C1 says which oracles of a family are split, C2 which oracles of the split family
are chain oracles (their answers are expanded from a state; the others are unchanged, `Link.plain`).
If the scheme meets `NeedOKCut`, the extractor reads only entries at oracles that are not split
(`WholeOnly`), and the hypotheses of the expansion step hold of the scheme after the splitting, then
completeness, index binding and index privacy (ZKCP/Gen.lean) carry over to
`stateFirstArg C2 (cutArg C1 nC nP nV A)`, with `extSt C2 (extCut C1 E)`, `simSt C2 (simCut C1 Sim)`
and the expansion step's three bounds. (The three bounds: the head of Rom/StateFirst.lean.) The
numbers kC, kP, kV in the added error terms are counted before the splitting, in the weight
`wCut C1 need (wCh C2)`: a typed query counts 1 for each of its two oracles that is queried and is a
chain oracle. So a query whose second part is not queried (for instance a failed proof-of-work
attempt) counts 0 if the first parts are unchanged oracles (`wCut_zero`, Rom/CutKit.lean).

Notation:
  `C1 o`: `OCut (S.Rng o)` (Rom/SpecCut.lean): how an oracle with answers in R is treated: `whole`,
    or `cut` with `e : R ≃ A × B`
  `C2 x`: `Link lam ((cutSpec S C1).Rng x)` (Rom/StateFirst.lean): how an oracle with answers in R
    is treated: `plain`, or `chain K e` with `e : R ≃ (Fin K → Dg lam) × Dg lam × Dg lam`
  `lam`: `ℕ`; `Dg lam`: `Fin lam → Bool` (Rom/NeedA.lean): a hash block
  `nC`, `nP`, `nV`: `NeedCut C1` (Rom/SpecCut.lean): a rule for each algorithm (doc comment of
    `cutArg`)
  `kC`, `kP`, `kV`: `ℕ`: in `Spec.cutState` (Rom/SpecCut.lean):
    `(A.C i).CostBoundV (wCut C1 nC (wCh C2)) kC`, and so for `A.P k b` with `b.length ≤ B` and kP,
    and for `A.V v x π` and kV
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `α`; `ε`, `ζ`: `ℝ≥0∞`; `ℕ → ℕ → ℝ≥0∞`: the last arguments of `Gen.HasCompletenessError R A B α`,
    `Gen.HasIndexBindingWith R A E ε`, `Gen.HasIndexPrivacyWith R A B Sim ζ` (ZKCP/Gen.lean), the
    three fields of `Gen.IsZKCPArgWith R A B E Sim α ε ζ`
  `collP lam n m`: `(n * m) / 2 ^ (2 * lam)`; `hitP lam t h`: `(t * h) / 2 ^ lam`
    (Rom/StateFirst.lean)
  `wCut C1 need u o q r`: `ℕ` (Rom/SpecCut.lean): what a typed query costs over the second family
    (`cutSpec S C1`), if a query there costs u
  `wCh C2 x q`: `ℕ` (Rom/StateFirst.lean): the weight of a query: 1 at a chain oracle, 0 at an
    unchanged one

Limits: the splitting step is not proved here (`cutExit`: Rom/CutTop.lean; `cutCost`:
Rom/CutRun.lean; in Rom/CutTop.lean `cutState` is proved without the two hypotheses). `PlainOnly`
and `HidFree` are required of the scheme after the splitting and of its extractor; they follow,
under the hypotheses of `plainOnly_extCut` and `factorsBy_cut` (Rom/CutKit.lean), from facts on the
scheme before it. Nothing is said on any scheme. What the heads of Rom/SpecCut.lean and
Rom/StateFirst.lean list as not said is not said here either.
-/
import Rom.SpecCut
import Rom.StateFirstTop

set_option autoImplicit false

noncomputable section

namespace Rom
open ZKCP
open scoped ENNReal

theorem cutState_of (h1 : Spec.cutExit) (h2 : Spec.cutCost) : Spec.cutState :=
  fun S C1 lam C2 I X W PP IVK ISK Pf R A B E Sim α ε ζ nC nP nV kC kP kV hN hE cC cP cV hP hH h =>
    stateFirst (cutSpec S C1) lam C2 I X W PP IVK ISK Pf R (cutArg C1 nC nP nV A) B (extCut C1 E)
      (simCut C1 Sim) α ε ζ kC kP kV (fun i => h2 S C1 _ nC (wCh C2) _ kC (cC i))
      (fun k b hb => h2 S C1 _ nP (wCh C2) _ kP (cP k b hb))
      (fun v x π => h2 S C1 _ nV (wCh C2) _ kV (cV v x π)) hP hH
      (h1 S C1 I X W PP IVK ISK Pf R A B E Sim α ε ζ nC nP nV hN hE h)

end Rom

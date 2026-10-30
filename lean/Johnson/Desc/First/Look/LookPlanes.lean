-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookPlanes.lean: the lookup's three claims that read the planes, and the
rounds of a batched sumcheck, as plain functions on data. Definitions with code. No theorem.

`Forest.planesAt`, `planeClaims`, `planeLins` (OnBytes/Model/Look.lean) take the caller's `bit` and
`pin`: how the caller reads the planes' matrix in its own tables. `stackRounds` runs the rounds of a
batched sumcheck: a helper of the sub-proofs that the program keeps in the same file. Here they
stand over the carrier `Fl` (OnBytes/K/Kc/Flat.lean), typed after the program's text line by line;
the pure functions of Look.lean and of `Fork` (OnBytes/Model/Hide.lean), and `Fl.pscRow` and
`Fl.roundsIn`, are called by name. No routine that runs in a context is called.

Main names: `stackRoundsF`; `planesAtF`, `planeClaimsF`, `planeLinsF`.

Limits: that a step returns what the program's routine returns is tried by tests
(TestLookClaims.lean [not in this library]) and by runs, not shown. The names of refusals are left out, as in `Fl`. The
callers' `bit` and `pin` are letters. THE LIST OF GUARDS, for this file's steps and for those of
LookClaims.lean, stands at the foot.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.LookClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- `stackRounds` (Look.lean:102-104). -/
def stackRoundsF (st : Stack) : Fl Stack := do
  let (r, p) ← Fl.roundsIn .sum2 st.p (List.replicate st.lam (zeroE, 0))
  pure { st with rs := r.reverse, p := p }

/-- `Forest.planesAt` (Look.lean:474-483). -/
def planesAtF (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Fl Aff) : Fl Aff := do
  let h := g.shape
  let w := h.kT + 5 - lm
  let ec := eqTab ((g.zb e).extract h.kT (h.kT + h.cK))
  let et := eqTab ((g.zb e).extract 0 w)
  (List.range (h.NC * 2 ^ w)).foldlM
    (fun (f : Aff) col => do
      let x ← bit e col
      pure (Aff.addMul f x (mulE (ec.getD (col / 2 ^ w) zeroE) (et.getD (col % 2 ^ w) zeroE))))
    (Aff.ofConst zeroE)

/-- `Forest.planeClaims` (Look.lean:496-506). -/
def planeClaimsF (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff) (pin : Nat → Fl Aff) :
    Fl (Array Aff) := do
  let h := g.shape
  Fl.must (Forest.planeCols h lm).toBool
  let at0 ← planesAtF g lm 0 bit
  let at1 ← planesAtF g lm 1 bit
  let count ← (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldlM
    (fun (f : Aff) col => do pure (f + (← pin col)))
    (Aff.ofConst (negE (ofF (2 ^ h.v - h.padding).toUInt64)))
  let (leavesRow, _) ← Fl.pscRow g.leaves oneE (Aff.scale at0 g.leavesA)
  pure #[leavesRow, Aff.slot g.sBit - at1, count]

/-- `Forest.planeLins` (Look.lean:509-512). -/
def planeLinsF (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff) (pin : Nat → Fl Aff) :
    Fl Unit := do
  (← planeClaimsF g lm bit pin).forM linF
  planesAddedF g

/-! ### THE LIST: guard · the program's file:line · the step

 1. internal-L-row: the array has a column, and the row's number fits 32 bits · Look.lean:60 ·
    `uEntF`.
 2. a round of the batched sumcheck: what `roundIn` refuses · Look.lean:103 → :86 →
    Psc.lean:142-144, :129-131 · `stackRoundsF`: `Fl.roundsIn` by name.
 3. a claim is added: what `Fork.lin` refuses (the door is shut; theta is not drawn; the claim's
    number is no free claim of the plan; the form names an entry or a slot that is not there) ·
    Look.lean:426, :511 → Hide.lean:366-367 (kap :348-349 · kapTake :335-341 · kapAt :330-331 ·
    push :310-320 · pushEnt :295-300 · pushSlot :304-305) · `objectsF`, `objectsOn`, `planeLinsF`:
    `Fork.lin` by name.
 4. internal-forest-padding-places: the two counts of padding are one · Look.lean:448 ·
    `paddingLaidF`.
 5. internal-forest-join: one key form and one weight for each call · Look.lean:457 · `joinF`.
 6. the planes' matrix: what `Forest.planeCols` refuses; nameless · Look.lean:499 · `planeClaimsF`.
 7. the leaves' sumcheck's claim is made once, on a sumcheck that was begun and has a challenge for
    each variable, and its slots are free · Look.lean:505 → Psc.lean:198-199 → Hide.lean:256 ·
    `planeClaimsF`: `Fl.pscRow` by name.
 8. the callers' own (`bit`, `pin`) · Look.lean:481, :503 · `planesAtF`, `planeClaimsF`: letters.
NO GUARD: the three marks (Look.lean:427, :431, :435 → Hide.lean:356-357): where the list of owed
claims has no entry of that number nothing is marked and nothing is refused, as in the program. -/

end VerifiableInference.Desc.First.Look

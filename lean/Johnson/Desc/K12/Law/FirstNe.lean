-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FirstOk
/-
Johnson/Desc/K12/Law/FirstNe.lean: a test on the plan of a proximity test (the kind K12): no tree of the plan's list for the first stage is the first fold's own mask's. Definitions with code alone and no theorem, so that the test can be compiled and run. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
Why. The block's test on the plan (fixedOk) lets a member of p.nums.first with the source «own», number free, by: that tree is fixed in front of the first fold's draw. But a law in a game asks that the members' trees stand in front of the test (FirstBelow.lean).
Main names:
  firstNe p: no tree of p.nums.first has the source «own», number p.nums.free.
  spoilFirst p: the control's place: such a tree is laid at the end of p.nums.first.
  firstNeLines: two lines of text: the test, with the sources; the control, which is due false.
Limits: ASKED BY NO RUNNING TEXT; EVALUATED NOWHERE. Evaluated is not proved. Where the first fold sends no mask of its own the law does not ask this test.
-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- No tree of the plan's list for the first stage is the first fold's own mask's. -/
def firstNe (p : P12) : Bool := p.nums.first.all fun o => decide (o.2 ≠ .own p.nums.free)

/-- The control's place. -/
def spoilFirst (p : P12) : P12 :=
  { p with nums := { p.nums with first := p.nums.first ++ [(⟨0, 0, false, 0⟩, .own p.nums.free)] } }

/-- The lines for a print. -/
def firstNeLines (tagS : String) (p : P12) : List String :=
  [s!"{tagS}.FIRSTNE\tfirstNe {firstNe p}\townMask {p.nums.ownMask} · free {p.nums.free} · the sources of nums.first, in turn: {repr (p.nums.first.map (·.2))}",
   s!"{tagS}.FIRSTNE.control\ta tree with the source own free laid at the end of nums.first\t{firstNe (spoilFirst p)}"]

end H2K.Made

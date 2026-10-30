-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Side.lean: THE SMALLNESS TEST: THE KIND's SIDE AT A PLACE, in the
frame's form (Johnson/Desc/ProofFile/Honest/Side.lean: `Side`): the description's own member at the
place, and a row of one part with the term that stands beside it. DEFINITIONS ALONE. NO LAW IS
STATED HERE, AND NONE OF THE LIBRARY's GOALS.
One empty round is simulated by a term that yields, for that round, no item and no column. This is
not to be quoted as "the range check is simulated exactly": what the range check can tell goes
through the second stop.

  `smallPlace p`     the place of the kind's block, of the place's numbers
  `smallSims P`      the terms beside the half's parts, one for each: the frame's `quietSim`
                      (Honest/ForKinds.lean) at the part's address. WHAT THE TERM YIELDS: for the
                      one round, no item and no column. It takes no coin and reads none of its
                      arguments
  `smallRow cells P`   the half's parts (Honest/K8/Part.lean: `smallHalf`), each with its term
  `smallSide bs cells P fs`   the side: the first member of the list bs at the place, with that row
                      and the falls of fs at the place; nothing if no member stands there
Limits. Definitions: nothing is said of them. The kind's own place has no fall: the two tests of the
verifier that this kind's claims can fail stand at two later members of the segment
(Honest/K8/Share.lean). `smallRow` zips the half's parts with a list of ONE term: a second part
would fall in silence. The half's parts are a written list of one, at every P, by its make
(`smallHalf`, Johnson/Desc/ProofFile/Honest/K8/Part.lean); which part that is, where the seat's test
`smallFits` passes, says `small_parts` (Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean).
-/
import Johnson.Desc.ProofFile.Honest.K8.Part
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First.K8 (Par)

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- The place of the kind's block. -/
def smallPlace (p : Par) : Place := ⟨1, some p.link, p.piece, .K8⟩

/-- The terms beside the half's parts: for the one round, no item and no column. -/
def smallSims : KindSim (Par × List (Nat × String × Nat)) Pb :=
  fun P => [quietSim ⟨smallPlace P.1, 0⟩]

/-- The half's parts, each with its term. -/
def smallRow (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb) :=
  (smallHalf cells P).parts.zip (smallSims P)

/-- **The kind's side at a place**, its member taken off a description's own list. -/
def smallSide (bs : List (Block S Cl)) (cells : Tr → Cells)
    (P : Par × List (Nat × String × Nat)) (fs : List (Fall S) := []) :
    Option (Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) :=
  Side.seated bs (smallPlace P.1) (smallRow cells P) fs

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.smallPlace
#print axioms ProofFile.Honest.K8.smallSims
#print axioms ProofFile.Honest.K8.smallRow
#print axioms ProofFile.Honest.K8.smallSide

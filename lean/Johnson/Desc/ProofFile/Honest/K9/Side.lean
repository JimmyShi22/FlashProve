-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Side.lean: beside K9's honest part (Honest/K9/Part.lean): a
simulator in the frame's form, and the side (Honest/Side.lean). Definitions with code; no theorem.
In a file of its own, so that the part's file hangs, of the frame's files, on Honest/Frame.lean alone.

  `batSim`    a simulator beside the part: it takes no coin, reads nothing of what it is handed, and yields one round in
              which nothing is shown. Data: nothing is said of it. It has the body of the frame's `quietSim` at one
              round, written a second time; no lemma ties the two
  `batRow`    the row of the one pair
  `batSide`   the side: that row beside the description's own member at the batching's place, taken off its list
              (`Side.seated`): as the description's makers have wrapped it. Its fall never answers (`Side.seated` at its
              default, no fall)

Limits. Nothing is said of `Good` at this side. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.Part
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9

variable {V W X Pb : Type}

/-- A simulator beside the part, at the same address. -/
def batSim (p : VerifiableInference.Desc.K9.Where) : Sim Pb :=
  { addr := ⟨⟨p.chain, some p.link, p.piece, .K9⟩, 0⟩, takes := ⟨0, 0⟩
    tell := fun _ _ _ _ _ => some [⟨[], []⟩] }

/-- The row: the part with its simulator. -/
def batRow (p : VerifiableInference.Desc.K9.Where) : List (Part V W X × Sim Pb) :=
  [(batPart, batSim p)]

/-- **The side**: the row beside the member of a description's first chain that stands at the
batching's place; `none` if none does. bs: that chain's list (`Chain.blocksInOrder`). -/
def batSide {S Cl : Type} (bs : List (VerifiableInference.Desc.Block S Cl))
    (p : VerifiableInference.Desc.K9.Where) : Option (Side S Cl V W X Pb) :=
  Side.seated bs ⟨p.chain, some p.link, p.piece, .K9⟩ (batRow p)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batSim
#print axioms ProofFile.Honest.K9.batRow
#print axioms ProofFile.Honest.K9.batSide

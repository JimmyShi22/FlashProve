-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Side.lean: beside each of the eight parts of the honest side of the
sub-protocol "the output head's own rounds" (Honest/K6/Part.lean) the form of a simulator, and the
side, in the form of Honest/Side.lean. Definitions with code; no theorem.

  `headSims`    the eight simulators, in the row's order: each takes coins of its own, sends them as
                they are, and reads, of what it is handed, these coins alone. How many each takes is
                written here (none; 9; 7; by the job's shape): that this is as many as its part's
                rounds send scalars is stated by no theorem here
  `headSided`   the row: each part with its simulator
  `headSide`    the side: the row beside the member of a chain's list that stands at the place

None of the three forms is written here: `quietSim` and `scalarsSim` stand in Honest/ForKinds.lean,
`sumSim` in Honest/Sum.lean. No fall is handed to `Side.seated`: the sub-protocol's own member
has none. "Member" in this file: a block of a chain's list, in the sense of the library's
`K6MemberIs` (Johnson/Desc/Kinds/Law/K6WayUp.lean): not the frame's `Member` (Honest/Side.lean).

Limits. The simulators are data: nothing is said of what they are good for. In `headSide` nothing
ties the public numbers p to the list bs. Honest/K6/Cut.lean holds the simulators' counts of coins
and their addresses against the sub-protocol's own rounds at three sizes; Honest/K6/Toy.lean tries
`headSide` at its small list of blocks (it fits at the place; there is none at the piece beside it)
and the simulators' counts there. Nothing else is tried. Honest/K6/Toy.lean is not in the
library; Honest/K6/Cut.lean is, and is another file than Honest/Small/Cut.lean.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.ProofFile.Honest.K6.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Kinds (Head.Par)

variable {X Pb W₀ Rc Tr : Type}

/-- The eight simulators, in the row's order. The counts 9 and 7, and the one round of each quiet
term, are written here: nothing in the code ties them to the parts'. -/
def headSims (p : Head.Par) (at_ : Place) : List (Sim Pb) :=
  [quietSim ⟨at_, 0⟩, scalarsSim ⟨at_, 1⟩ 9, sumSim ⟨at_, 2⟩ (headSquaresJob p).shape,
   quietSim ⟨at_, 3⟩, scalarsSim ⟨at_, 4⟩ 7, sumSim ⟨at_, 5⟩ (headProductsJob p).shape,
   sumSim ⟨at_, 6⟩ (headNormedJob p).shape, sumSim ⟨at_, 7⟩ (headLogitsJob p).shape]

/-- The row: each part with its simulator. -/
def headSided (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    List (Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × Sim Inst) :=
  (headRow wit p at_).zip (headSims p at_)

/-- **The side**: the row beside the member of the list bs that stands at the place; `none` if none
does. bs is meant for the list of a description's first chain (the place's own chain number is 1):
nothing checks that it is. -/
def headSide {S Cl : Type} (bs : List (Block S Cl)) (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (p : Head.Par) (link piece : Nat) :
    Option (Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) :=
  Side.seated bs (headPlace link piece) (headSided wit p (headPlace link piece))

end ProofFile.Honest.K6

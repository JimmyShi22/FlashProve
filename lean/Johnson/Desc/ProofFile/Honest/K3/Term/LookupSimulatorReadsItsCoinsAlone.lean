-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorReadsItsCoinsAlone.lean: AT ANY FILLING. The
kind "lookup" (K3): no simulator of a lookup's row reads anything but its own coins: not the input's
public field, not
`front`, not the challenges, not the positions. One definition; two theorems. General in the
filling. No premise on the description: the second theorem is conditional on the side being seated.

  `ReadsItsCoinsAlone sim`               at any two values of the four other arguments of `Sim.tell`
                                         (Honest/Frame.lean), at one value of its coins: one answer
  `lookupSimulatorReadsItsCoinsAlone`    of the simulator of every pair of every row of the lot
  `lookupMemberSimulatorReadsItsCoinsAlone`   of the simulator of every member of a seated side

Why. The rows' On is "true" (LookupSimulatorLot.lean). Honest/Side.lean warns that whatever On
allows in `front` reaches the simulator, private data included. Here nothing that reaches it is
read.

The sites of a public part (`lookSites`) are PLACES OF THE PROOF FILE ALONE (fifty under the
library's hypothesis at the full size): THE KEY FILE'S TWO LOOKUPS ARE NOT SPOKEN OF.

Limits. A sentence on the simulators' text alone: nothing on what a part shows. Nothing on any
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupMemberWrittenOut
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block)
open ProofFile.Honest.K3.Law

variable {S Cl V W X Pb : Type}

/-- **The simulator reads its own coins alone.** -/
def ReadsItsCoinsAlone (sim : Sim Pb) : Prop :=
  ∀ (pub pub' : Pb) (front front' : Before) (challenges challenges' : List Fmt.Drawn)
    (positions positions' : List (List (List Nat))) (coins : Cs sim.takes),
    sim.tell pub front challenges positions coins =
      sim.tell pub' front' challenges' positions' coins

/-- Of the simulator beside a stage, with a call or without. -/
theorem stageSimulatorReadsItsCoinsAlone (a : At) (stage : Stage) (number : Nat) :
    ReadsItsCoinsAlone (simOf (Pb := Pb) a stage number) := by
  unfold simOf
  cases stage.call a.face with
  | none => exact fun _ _ _ _ _ _ _ _ _ => rfl
  | some call => exact fun _ _ _ _ _ _ _ _ _ => rfl

/-- **NO SIMULATOR OF A ROW OF THE LOT READS ANYTHING BUT ITS OWN COINS.** No premise. -/
theorem lookupSimulatorReadsItsCoinsAlone (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) :
    ∀ pair ∈ row.row, ReadsItsCoinsAlone pair.2 := by
  obtain ⟨s, _, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  intro pair inRow
  have inSims : pair.2 ∈ lookSims (Pb := Pb) s.at_ := (List.of_mem_zip inRow).2
  obtain ⟨y, _, e⟩ := List.mem_map.1 inSims
  rw [← e]
  exact stageSimulatorReadsItsCoinsAlone s.at_ y.1 y.2

/-- **The same of every member of a seated side.** -/
theorem lookupMemberSimulatorReadsItsCoinsAlone (A : Fill W) (s : Site) (bs : List (Block S Cl))
    (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (seated : Side.seated bs s.at_.place (rowPairs A s) fs = some σ) :
    ∀ u ∈ σ.members, ReadsItsCoinsAlone u.sim := by
  intro u member
  obtain ⟨stage, _, _, _, hs⟩ := member_k3 A s bs fs σ seated u member
  rw [hs]
  exact stageSimulatorReadsItsCoinsAlone s.at_ stage u.number

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.ReadsItsCoinsAlone
#print axioms ProofFile.Honest.K3.Term.stageSimulatorReadsItsCoinsAlone
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorReadsItsCoinsAlone
#print axioms ProofFile.Honest.K3.Term.lookupMemberSimulatorReadsItsCoinsAlone

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ExactRows.lean: kind K14: THE ROWS OF THE TWO SENDINGS OF THE
BATCH's SHARED ROUNDS, in the frame's form of a row without the sentences in front and behind
(Unlettered, Honest/Thread/Rows.lean). One definition; no theorem is stated.

  sendingRows     the two rows: the place; the part, lifted, beside its simulator (sendingSim,
                  Honest/K14/ExactDefs.lean); at the part's entry pointApart; the count of positions
                  (budAt, Johnson/SendSim/At/Sim.lean)

The parts and the lift are those of proverSidesOfSharedSendings (Honest/K14/Sendings.lean).

Limits. A definition. That pointApart holds where a run stands in front of a sending, and that the
positions which a run reads are within the count (of one request's run; of a batch's requests
together: shown by nobody), is not shown in this file (the first, out of the frame's sentence on
where a run stands, which nothing shows to hold along a run: Honest/K14/OnSending.lean; of the
second, the count at the positions that the frame lays at one request's challenges, not at a run's:
Honest/K14/BudRows.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactDefs
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.SendSim.At (budAt)

variable {X Pb W₀ Rc Ky : Type}

/-- **The two sendings' rows**: the halves of proverSidesOfSharedSendings (Honest/K14/Sendings.lean), each part
beside its simulator, with the sentence at its entry and the count of positions. -/
def sendingRows (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    List (Unlettered Empty (Common W₀ Rc Ky) X Pb) :=
  [{ place := sendPlace 2
     row := [(liftSend (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩) (sendingPart (jobU A)),
       sendingSim (jobU A) ⟨sendPlace 2, 0⟩)]
     On := fun _ _ m _ => pointApart A m.st.heard
     bud := fun _ _ asks => budAt (jobU A).Q asks },
   { place := sendPlace 5
     row := [(liftSend (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩)
         (sendingPart (jobOmega A)),
       sendingSim (jobOmega A) ⟨sendPlace 5, 0⟩)]
     On := fun _ _ m _ => pointApart A m.st.heard
     bud := fun _ _ asks => budAt (jobOmega A).Q asks }]

end ProofFile.Honest.K14

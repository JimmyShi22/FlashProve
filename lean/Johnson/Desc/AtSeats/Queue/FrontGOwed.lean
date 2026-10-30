-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/Queue/FrontGOwed.lean: ONE SENTENCE THAT IS OWED,
fixed by def; NO THEOREM. The def's text is cut by program, sign for sign, out of
Johnson/Desc/K13/Law/OwedFrontG.lean [not in this library]; here it stands over fewer imports.
The three premises of openingZero_sentIs (Johnson/Desc/K13/Law/MadeAtOpeningSent.lean) on the
verifier's state in front of kind K1's first sending, at the data that is meant (sentDataAt,
Johnson/Desc/First/SentTerms.lean), out of seven plain facts on that state and the list of rounds.
What is not claimed. That the sentence holds. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.FrameAtFirst
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild.Queue
open VerifiableInference.Desc
open OnBytes OnBytes.Params OnBytes.Model
open Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.First.FillSent (sentDataAt baseAt)

/-- **The owed statement.** -/
def OwedFrontG (q : Params.First) (gp : GPar) (shape : Params.ReqShape) (N : Numbers)
    (links : List ModelPart) (ps : List Place) (built : Array Stages.LinkH) : Prop :=
  ∀ s : S, s.st.oracles.size = 0 → s.check.frame.shape = shape → s.check.frame.link = 0 →
    s.check.frame.groups = reqGroups s.check.frame.shape → s.check.frame.keptBefore = #[] →
    baseAt N links ps 0 = 0 →
    (s.check.frame.atMoment 0).length ≤ (K1.firstPar q gp).sent.size →
    (s.check.frame.groups.getD 0 {}).born = (sentDataAt shape N links ps built).born 0 ∧
      s.check.frame.keptBefore = (sentDataAt shape N links ps built).kept 0 ∧
      (K1.idsOf (K1.firstPar q gp) s.st.oracles.size).extract 0
        (s.check.frame.atMoment 0).length = (sentDataAt shape N links ps built).own 0

/-- At all letters. -/
def FrontGOwed : Prop := ∀ q gp shape N links ps built, OwedFrontG q gp shape N links ps built

end HashBuild.Queue

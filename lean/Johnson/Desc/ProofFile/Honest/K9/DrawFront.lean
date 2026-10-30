-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/DrawFront.lean: K9's DRAW AT THE HEAD's SEGMENT KEEPS WHAT THE OUTPUT HEAD's OWN KIND
HAS HEARD. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

The sealed `AlikeFront s s'` (Johnson/Desc/Kinds/Law/RunsFixedFront.lean) says of two states in the head's segment:
what the head's own rounds heard, the squares' sumcheck's state, the mark "opened", what the lookup heard, the reply
and the request are the same, and the ledger is later (`OnBytes.PscRun.Later`). Whoever carries a fact on K6's hearing
from K6's step to the gatherer's state owes it of every block and run between: K9's draw is one of these.
  `later_drawn`     the ledger behind the draw (`drawnPart`, Honest/K9/LedgerOf.lean) is later than the ledger in front
  **`draw_alikeFront`**   a yes of the draw at a state that stands in the head's segment: `AlikeFront` from the state
      in front to the state behind
`set_req`: laying K9's part into a state does not turn the request. No member (no toy of this folder stands in the
head's segment): `later_drawn` and `set_req` are called by `draw_alikeFront` alone, and that by no line.
WHAT IS NOT CLAIMED. `AlikeFront` of any other block or run. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.DrawSlots
import Johnson.Desc.ProofFile.Honest.K9.YesAtSeat
import Johnson.Desc.Kinds.Law.RunsFixedFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (atS Where drawAlone)

/-- The draw turns nothing under the slots: so the ledger behind is later. -/
theorem later_drawn (p : Where) (a : VerifiableInference.Desc.K9.Part) (x : E) :
    OnBytes.PscRun.Later a.F (drawnPart p a x).F :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem set_req (u : S) (q : VerifiableInference.Desc.K9.Part) : (atS.set u q).req = u.req := by
  cases hh : u.here with
  | head h0 => by_cases ho : h0.opened = true <;> simp [atS, S.putLink, S.putFork, hh, ho]
  | _ => simp [atS, S.putLink, S.putFork, hh]

/-- **K9's draw keeps `AlikeFront`.** -/
theorem draw_alikeFront (p : Where) (s t : S) (x : E) (h0 : HeadOwn) (hs : s.here = .head h0)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    VerifiableInference.Desc.Kinds.Head.Law.AlikeFront s t := by
  obtain ⟨a, ha, hF, ht⟩ := draw_head p s t x h0 hs h
  have e := draw_is p s t x a ha h
  refine ⟨h0, _, hs, ht, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [e, set_out]
  · rw [e, set_req]
  · rw [← hF]
    exact later_drawn p a x

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.later_drawn
#print axioms ProofFile.Honest.K9.set_req
#print axioms ProofFile.Honest.K9.draw_alikeFront

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K6RowScope.lean: THE ROW OF K6's LOT (K6RowAt.lean: k6_row_written) IN THE
GOALS' SCOPE, THE STOREY BETWEEN: seven premises in the place of twelve. THE END IS k6_row_scope6
(K6RowOwner.lean), which pays the seventh. A joining: calls alone; nothing is evaluated.
WHAT IT DOES NOT SHOW, FIRST. THAT ANY FILES MEET ITS PREMISES: not proved in this file; whether a
theorem elsewhere shows it was not examined for this file. NO EXAMPLE OF THE HEAD IS SHOWN IN THIS
FILE; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth. At the second hash function OnBytes.secondHashFunction alone. The
letter lay is tied to P's own field
lay by nothing (harmless: the laws that are called hold at every lay). Nothing on soundness.
THE GROUND. k6_row_written, which this calls, STANDS OVER THESE FILES:
five files on skeletons (Johnson/Desc/ProofFile/Law/Skel/) ·
K4SentAt, K4BlockPlan (Johnson/Road/K4/), Written (Johnson/AtFull/K4Sent/) · CutWrittenLit
(Johnson/AtFull/Cut/: hc speaks of Johnson.AtFull.Cut.cutWritten) · H1Row, ShapeTrees.

Main name (namespace Johnson.AtFull.Lots).
  k6_row_scope: lotSk G (P4.k6Lot Z) = k6LotW from: the goals' scope · the goals' reader's return ·
      the plain public part's return (ProofFile.pubPlain) · the blank letters' return (ProofFile.blankBy) · the
      written table of steps · the written entries · hO: the table arrayOf of the head's built
      segment books link 22 as the owner of that segment's one foreign array.

What is called, none at an opening, under a pin, or at a return of the chain:
IM.ground_publicK, ground_gets, ground_named (Johnson/IMR/PureJoin.lean) and ground_tails
(Johnson/IMR/K8Seat.lean: the built segment bears the plan's record; THAT FILE HOLDS LAWS AT AN
OPENING FURTHER DOWN: NONE IS CALLED) · numbers_in_scope, stream_in_scope
(Johnson/Goal/Meaning/HeadCondScope.lean), ReadsNamed.public_third, and public_H_ft (K6RowFt.lean:
the plan has one foreign array).

-/
import Johnson.AtFull.Desc.Lots.K6RowAt
import Johnson.AtFull.Desc.Lots.K6RowFt
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Lots

open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.K4Sent (esWritten)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (numbers_in_scope stream_in_scope)
open ProofFile.Sk (lotSk)

/-- **The row in the goals' scope.** -/
theorem k6_row_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten)
    (hO : ∀ X t, G.built[24]? = some X → X.tl.ix.FT.toList = [t] →
      ∃ nm, X.arrayOf[t]? = some (22, nm)) :
    lotSk G (P4.k6Lot Z) = k6LotW := by
  have hW := IM.ground_publicK hZ hG
  have hsz : G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  obtain ⟨hl, X, hX, -, nX⟩ := IM.ground_named hS hR hZ hG
  obtain ⟨Y, -, hY', -, -, nY, -⟩ := hl 11 (by decide)
  have hY : G.built[22]? = some Y := hY'
  obtain ⟨-, X', hX', eT, -⟩ := IM.ground_tails hS hR hZ hG
  obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
  obtain ⟨t, hFT⟩ : ∃ t, X.tl.ix.FT.toList = [t] := by
    rw [eT]
    exact public_H_ft hW
  obtain ⟨nm, hborn⟩ := hO X t hX hFT
  have hb : G.built.back? = some X := by
    rw [Array.back?_eq_getElem?, hsz]
    exact hX
  exact k6_row_written hsz
    (VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third hW)
    (numbers_in_scope hS hR hW) (stream_in_scope hS hR hW) hc he hb nX.name hFT hborn hY
    (by rw [nY.name]; rfl)

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.k6_row_scope

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4R/LotSteps.lean (a law about the lot of Johnson/Desc/ProofFile/Lot/K6K7.lean, no part of it): THE
DECISION OF THE OUTPUT HEAD's OWN BLOCK (K6), AS ITS LOT BRINGS IT, CARRIES: it leaves what the lookup was heard to
return, and leaves the link's ledger a later one with its sizes. Theorems.

Why. The road that pays "the lookup's run ran at a later record" asks, of every hearing block behind the lookup on
the calls: b.planOk = true -> b.Steps (CarriesFo S.fork? S.lookHeard?) (Johnson/Desc/First/LedgerAtFo.lean;
Johnson/Desc/Sound/FoldSteps.lean), of the lot's own block.

What is said.
  seated_steps   for all W, l, ms, b with Head.seatedClaims W l ms = some b:
                 b.Steps (CarriesFo S.fork? S.lookHeard?).
  **k6_lot_steps**   for all Z, G and EVERY b in (k6Lot Z).blocks G: the same; k6_lot_steps' has the premise
                 b.planOk = true in front, which is not used: the form in which it is asked.
How. The seated decision goes on only where the bare block's does (Law/SeatedBridge.lean: tested_decide); that
decision does not hang on the type of claims; of it three laws lie: it leaves S.lookHeard? (Law/RowPins.lean:
lookHeard_leaves); behind it the record holds a ledger (Law/TakesAt.lean: blockAt_fork); that ledger is later than
the one in front, in the library's order PscRun.Later (Law/KeepsAt.lean: blockAt_later). carriesFoOfLater joins them.

Letters under "there is" in the top statements: none.
What it does not give. Nothing on the block's four runs of claims (RunsStep) or on what stands behind the batching
(the block has no such run). Nothing on the guards that the driver and the seat lay over the lot's block. Where the lot
has no block the statement holds idly. Nothing on soundness.

-/
import Johnson.P4R.LotRuns
import Johnson.Desc.First.LedgerAtFo
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Kinds.Law.RowPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4
open ProofFile (Cl Pub Ground)
open VerifiableInference.Desc (Block Claim CarriesFo carriesFoOfLater)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (seatedClaims_some tested_decide blockAt_later blockAt_fork)

/-- **The seated block's decision carries.** -/
theorem seated_steps {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps (CarriesFo S.fork? S.lookHeard?) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  have hd1 : (blockAt W.hS iU3 ((OnBytes.Params.settingOf W.P.frame).workOf .field .request) l).decide
      s rs gs = .ok s' := ((tested_decide _ _ _ _ s s' rs gs).1 hd).1
  refine carriesFoOfLater _ _ s s' (fun g hg => ?_) (fun F hF => ?_)
  · have e : s'.lookHeard? = s.lookHeard? := Law.Came.lookHeard_leaves W.hS iU3 _ l s rs gs s' hd1
    rw [e]
    exact hg
  · obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 (blockAt_fork W.hS iU3 _ l s s' rs gs hd1)
    have L := blockAt_later W.hS iU3 _ l s s' rs gs hd1
    have e1 : (seatAt W.hS iU3).ledger s = F := by
      show s.fork?.getD {} = F
      rw [hF]; rfl
    have e2 : (seatAt W.hS iU3).ledger s' = G := by
      show s'.fork?.getD {} = G
      rw [hG]; rfl
    rw [e1, e2] at L
    exact ⟨G, hG, L⟩

/-- **Every block of K6's lot: its decision carries.** -/
theorem k6_lot_steps {Z : Pub} {G : Ground} {b : Block S Cl} (hb : b ∈ (k6Lot Z).blocks G) :
    b.Steps (CarriesFo S.fork? S.lookHeard?) := by
  obtain ⟨ms, _, h⟩ := k6_lot_block hb
  exact seated_steps h

/-- The same in the form in which it is asked. -/
theorem k6_lot_steps' {Z : Pub} {G : Ground} {b : Block S Cl} (hb : b ∈ (k6Lot Z).blocks G)
    (_ : b.planOk = true) : b.Steps (CarriesFo S.fork? S.lookHeard?) := k6_lot_steps hb

end P4

#print axioms P4.seated_steps
#print axioms P4.k6_lot_steps

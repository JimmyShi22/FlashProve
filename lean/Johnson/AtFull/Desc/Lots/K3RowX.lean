-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K3RowX.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): THE EIGHT HYPOTHESES
THAT ARE LEFT OF ITS TWO ROWS (`ReadsLeft Z`, K3RowScope.lean), PARTED BY WHAT THEY READ: two read
Z.first and fall to two equations with written values; six read Z.p.X alone. A joining, and one
light closed fact by the kernel.
  `links_full`: the written shape of a request has 25 segments. `links_full_control`: not 24 (no
    negative test: it follows from `links_full`).
  `ReadsX X`: the six hypotheses on the public data X alone: calls · digits · laid · key · quiet ·
    caller.
  `readsLeft_of`: **`ReadsLeft Z` from Z.first.codes = Johnson.G.proofCodesWritten, Z.first.shape =
    ReqLit.shapeFull and `ReadsX Z.p.X`** (before: `before_at`, K3Table.lean).
  `k3_row_x`, `k3_lists_x`: the lot's two rows under the four common premises, the two equations and
    `ReadsX Z.p.X`.
THE ONE STEP HERE THAT IS NO UNFOLDING: `before_at` (K3Table.lean, sha256 c72c2b93…): the kernel's,
at the written codes and shape. WHICH TIES A CALLER STILL NEEDS: these hypotheses stand at
Johnson.G.proofCodesWritten and ReqLit.shapeFull, at Z.first; other lots' rows stand at
Johnson.G.codesFull2 and proofSizedFull.request, at G.first: that these written values are one, and
that Z.first is G.first, is not said here.
Limits. The two equations and `ReadsX` are premises: shown of nothing here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RoundsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt)
open VerifiableInference.Desc.First.Look (lookAt beforeAt laidAt padKeyAt)
open ProofFile.Sk (skel)

theorem links_full : VerifiableInference.Desc.ReqLit.shapeFull.link.length = 25 := by
  decide +kernel

/-- Not 24. No negative test: it follows from `links_full`. -/
theorem links_full_control :
    decide (VerifiableInference.Desc.ReqLit.shapeFull.link.length = 24) = false := by
  decide +kernel

/-- **The six hypotheses on the public data alone.** -/
structure ReadsX (X : Verify.Public) : Prop where
  calls : ∀ i < 25, ∃ x, lookAt X i false = some x ∧ viewOf true x = viewW i false
  digits : ∀ i < 25, ∃ x, lookAt X i true = some x ∧ viewOf false x = viewW i true
  laid : ∀ i < 25, ∀ d, laidAt X i d = some (pubW (sortOf i) d)
  key : ∀ i < 25, ∀ d, padKeyAt X i d = some true
  quiet : ∀ i < 25, ∀ d, (quietAt X i d).isSome = quietW i d
  caller : ∀ i < 25, (K3Lot.readersAt X i).isSome = callerW i

theorem readsLeft_of {Z : ProofFile.Pub} (hc : Z.first.codes = Johnson.G.proofCodesWritten)
    (hs : Z.first.shape = VerifiableInference.Desc.ReqLit.shapeFull) (RX : ReadsX Z.p.X) :
    ReadsLeft Z :=
  { links := by rw [hs]; exact links_full
    calls := RX.calls, digits := RX.digits
    before := fun i hi d => by rw [hc, hs]; exact before_at hi d
    laid := RX.laid, key := RX.key, quiet := RX.quiet, caller := RX.caller }

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **THE FIRST ROW.** -/
theorem k3_row_x (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hc : Z.first.codes = Johnson.G.proofCodesWritten)
    (hs : Z.first.shape = VerifiableInference.Desc.ReqLit.shapeFull) (RX : ReadsX Z.p.X)
    (G : ProofFile.Ground) : ((K3Lot.lot Z).blocks G).map skel = k3RowsW :=
  k3_row_scope hS hR hZ hG (readsLeft_of hc hs RX) G

/-- **THE SECOND ROW.** -/
theorem k3_lists_x (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hc : Z.first.codes = Johnson.G.proofCodesWritten)
    (hs : Z.first.shape = VerifiableInference.Desc.ReqLit.shapeFull) (RX : ReadsX Z.p.X)
    (G : ProofFile.Ground) :
    ∀ b ∈ (K3Lot.lot Z).blocks G,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt (ProofFile.Sk.Full.nameW b.place) b.rounds :=
  k3_lists_scope hS hR hZ hG (readsLeft_of hc hs RX) G

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.links_full
#print axioms Johnson.AtFull.Lots.K3.links_full_control
#print axioms Johnson.AtFull.Lots.K3.readsLeft_of
#print axioms Johnson.AtFull.Lots.K3.k3_row_x
#print axioms Johnson.AtFull.Lots.K3.k3_lists_x

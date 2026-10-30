-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardFastVerify.lean: the guarded verdicts (`verifyGuard`,
OnBytes/Maker/Page/GuardVerify.lean; `runGuardFit`, `verifyGuardFit`,
OnBytes/Maker/Page/GuardFit.lean) with the test `okJF` (OnBytes/Maker/Page/GuardFast.lean) in the
place of `okJ`, and that they are the same.

Main names:
  `verifyGuardF`, `verifyGuardF_eq`: `verifyGuard` by `runGuardF`.
  `runGuardFitF`, `runGuardFitF_eq`, `verifyGuardFitF`, `verifyGuardFitF_eq`: the same with a second
    test on each query.
`verifyGuardF` and `verifyGuardFitF` take the page, the function O and the test LAST, behind the
verifier's thirteen arguments; `verifyGuard` and `verifyGuardFit` take them first.
No premise. No letter stands under "there is".

To be minded. What the heads of OnBytes/Maker/Page/Guard.lean and
OnBytes/Maker/Page/GuardVerify.lean give to be minded holds of these terms too. The test `okJ` asks,
at a chain's first call (head f1, f3 or f4), for a string of the tail's block alone: so a term here
is a verdict only where the rounds that are asked under these heads have one verifier's message.
Under the link's tag and at a chain that does not join each of them is the constant no; at a page
whose `leaf` and `leafX` write nothing each says no to every string that opens a leaf; at a page
whose `sR` is not the file's, to every typing of that file; where the carrier hands an instance on
in a later round (`late` is not none), under the proof file's tag, to every string.

What is not claimed. Any running time: "fast" speeds the test alone. The family is still `gJ P O`,
which makes a block's string and asks O when that block's answer is read, and the algorithm is
`verifyOneProtocol`'s own, with its walks over all leaves of a tree. Nothing on soundness.


-/
import OnBytes.Maker.Page.GuardFastLaws
import OnBytes.Maker.Page.GuardFit

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol ProtocolQueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The run with a second test on each query, by `okJF`. -/
def runGuardFitF {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) : OComp (typedOracleFamily 256 K L) α → Option α :=
  detG (S := typedOracleFamily 256 K L) (fun o q => okJF P o q && fit o q) (gJ P O)

theorem runGuardFitF_eq {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) (c : OComp (typedOracleFamily 256 K L) α) :
    runGuardFitF P O fit c = runGuardFit P O fit c := by
  have e : (fun o q => okJF P o q && fit o q :
      ∀ o : (typedOracleFamily 256 K L).ι, (typedOracleFamily 256 K L).Dom o → Bool) = okFitJ P fit := by
    funext o q
    show (okJF P o q && fit o q) = (okJ P o q && fit o q)
    rw [okJF_eq]
  exact congrArg (fun k => detG (S := typedOracleFamily 256 K L) k (gJ P O) c) e

section V
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout 256 K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
  (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q)

/-- `verifyGuard` by `runGuardF`. -/
def verifyGuardF (P : PageJ L K) (O : ByteArray → ByteArray) : Bool :=
  (runGuardF P O (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π)).getD false

theorem verifyGuardF_eq (P : PageJ L K) (O : ByteArray → ByteArray) :
    verifyGuardF sMT sFS t Q wq embS embP xin embE depthReq cms x π P O =
      verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyGuardF verifyGuard
  rw [runGuardF_eq]

/-- `verifyGuardFit` by `runGuardFitF`. -/
def verifyGuardFitF (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) : Bool :=
  (runGuardFitF P O fit
    (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π)).getD false

theorem verifyGuardFitF_eq (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) :
    verifyGuardFitF sMT sFS t Q wq embS embP xin embE depthReq cms x π P O fit =
      verifyGuardFit P O fit sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyGuardFitF verifyGuardFit
  rw [runGuardFitF_eq]

end V

end OnBytes.Maker.Page

#print axioms OnBytes.Maker.Page.runGuardFitF_eq
#print axioms OnBytes.Maker.Page.verifyGuardF_eq
#print axioms OnBytes.Maker.Page.verifyGuardFitF_eq

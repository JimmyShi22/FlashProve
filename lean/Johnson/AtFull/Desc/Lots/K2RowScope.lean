-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2RowScope.lean: THE CODE SWITCH's LOT's ROW
(Johnson/AtFull/Desc/Lots/K2RowAtBlank.lean) WITH THREE OF ITS HYPOTHESES PAID IN THE GOALS' SCOPE:
hX (the public parameters are publicOf's return), hN (twelve groups) and hq (attention is on).
Three theorems: calls. NO BLOCK IMPORTS THIS FILE.

What it says.
  `k2_row_scope`: for public files in the goals' scope (hS, hR), where the plain road's public part
    Zq is made at the second hash function (hZ) and the blank records G are made (hG): under the
    other hypotheses (hs, hz, u1, u2, t3, t4, t5, hK): `((k2Pure Zq).blocks G).map skel = k2SkelW`.
  `k2_lotW_scope`: the same premises: `lotW as ls (lotSk G (k2Pure Zq)) = ProofFile.Sk.Full.lot2`, at all
    as and ls.
  `public_at_blank`: the step between: `publicOf P.pol P.KL (some lay) = .ok Zq.p.X`.
  PAID: hX: `IM.ground_publicK` (Johnson/IMR/PureJoin.lean: the records' public
    parameters are publicOf's) with `ProofFile.Law.blankBy_W`
    (Johnson/Desc/ProofFile/Law/MakerPublic.lean: the records' parameters are Zq's) · hq and hN:
    `Meaning.NamedAsk.fullShaped_scope` and `full_parts` (Johnson/Goal/Meaning/NamedAskLaw.lean).

Limits. hs, hz, u1, u2, t3, t4, t5 AND hK STAY PREMISES, and so do hS, hR, hZ and hG: that any
public files meet them together is shown nowhere here. No law at an opening and none under the proof
file's pins is spent. At the second hash function `OnBytes.secondHashFunction` alone. The full size alone. The
limits of K2Row.lean, K2RowFull.lean, K2HeadOk.lean and K2RowAtBlank.lean hold here too: among them
that neither written list of skeletons is an independent witness. No soundness is claimed.

-/
import Johnson.AtFull.Desc.Lots.K2RowAtBlank
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.NamedAskLaw
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open OnBytes OnBytes.Model
open ProofFile (Pub Ground spotsOf)
open ProofFile.Sk (skel lotSk lotW)
open VerifiableInference.Desc (Place)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Desc (spotsWritten)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Zq : Pub} {G : Ground}

/-- Where the public part and the blank records are made, the public part's parameters are
publicOf's return at the same files. -/
theorem public_at_blank (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Zq)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G) :
    Verify.publicOf P.pol P.KL (some lay) = .ok Zq.p.X := by
  rw [← ProofFile.Law.blankBy_W hG]
  exact IM.ground_publicK hZ hG

/-- **THE ROW, with hX, hN and hq paid in the goals' scope.** -/
theorem k2_row_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Zq)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G) (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Zq.first.shape) (u2 : proofSizedFull.codes = Zq.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hK : Zq.p.X.owner.tl.kTX.back? = some (Verify.borderOf Zq.p.X.y).kxb) :
    ((ProofFile.k2Pure Zq).blocks G).map skel = k2SkelW :=
  have hX := public_at_blank hZ hG
  have hF := Meaning.NamedAsk.full_parts (Meaning.NamedAsk.fullShaped_scope hS hR hX)
  k2_row_at_blank hZ hG hX hs hz u1 u2 t3 t4 t5 hF.2 hF.1 hK

/-- The same, on the written skeletons of ProofFile.Sk.Full
(Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean). -/
theorem k2_lotW_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Zq)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G) (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Zq.first.shape) (u2 : proofSizedFull.codes = Zq.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hK : Zq.p.X.owner.tl.kTX.back? = some (Verify.borderOf Zq.p.X.y).kxb) (as : List Place)
    (ls : List Nat) : lotW as ls (lotSk G (ProofFile.k2Pure Zq)) = ProofFile.Sk.Full.lot2 :=
  have hX := public_at_blank hZ hG
  have hF := Meaning.NamedAsk.full_parts (Meaning.NamedAsk.fullShaped_scope hS hR hX)
  k2_lotW_at_blank hZ hG hX hs hz u1 u2 t3 t4 t5 hF.2 hF.1 hK as ls

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.public_at_blank
#print axioms Johnson.AtFull.Lots.K2.k2_row_scope
#print axioms Johnson.AtFull.Lots.K2.k2_lotW_scope

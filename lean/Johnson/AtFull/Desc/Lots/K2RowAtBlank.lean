-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2RowAtBlank.lean: THE CODE SWITCH's LOT's ROW AT A BLANK GROUND: THE
SMALL JOIN of Johnson/AtFull/Desc/Lots/K2Row.lean (the row, at eight hypotheses by field),
K2RowFull.lean (the row on the written skeletons of ProofFile.Sk.Full) and K2HeadOk.lean (the head's
half of the test on the plan at «H:2»): every hypothesis is on the public part Zq alone, or is
one of three returns; the ground G is named in «blankBy … = some G» and in the end only. A join:
every step a call, but for k2_lotW_at_blank's last, which unfolds lotW and lot2. NO BLOCK IMPORTS
THIS FILE.
  k2_row_at_blank    pubPlain's · blankBy's · publicOf's returns · hs (the places are the written
                     ones) · hz (the sizes) · u1 u2 (the sizes' shape and codes are Zq.first's) ·
                     t3 t4 t5 · hN hq (twelve groups; attention on) · hK (the owner's last table's
                     key is the border's) ⟹ ((k2Pure Zq).blocks G).map skel = k2SkelW
  k2_lotW_at_blank   the same ⟹ lotW as ls (lotSk G (k2Pure Zq)) = ProofFile.Sk.Full.lot2, at all as and
                     ls
BY: ProofFile.Law.blankBy_first (Johnson/Desc/K1/Law/FirstMakeFacts.lean: G.first =
Z.first) for the row's t1 and t2; hH_at_blank for its hH.
LIMITS. It pays none of its hypotheses. That any public part meets them together is shown nowhere
here. No opening, no pin «in scope» is spent. The full size alone. The hash o is a free letter:
K2RowScope.lean pays hX at OnBytes.secondHashFunction, and at another o no payer of hX is named here. The limits
of K2Row.lean, K2RowFull.lean and K2HeadOk.lean hold here too: among them that neither written list
of skeletons is an independent witness. No soundness is claimed.
-/
import Johnson.AtFull.Desc.Lots.K2RowFull
import Johnson.AtFull.Desc.Lots.K2HeadOk
import Johnson.Desc.K1.Law.FirstMakeFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open OnBytes OnBytes.Model
open ProofFile (Pub Ground spotsOf)
open ProofFile.Sk (skel lotSk lotW)
open VerifiableInference.Desc (Place)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Desc (spotsWritten)

theorem k2_row_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray}
    {layout : Option ByteArray} {Zq : Pub} {G : Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq) (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G)
    (hX : Verify.publicOf pol' KL' layout = .ok Zq.p.X)
    (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Zq.first.shape) (u2 : proofSizedFull.codes = Zq.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hN : Zq.p.X.NGr = 12)
    (hq : Zq.p.X.p4 = true)
    (hK : Zq.p.X.owner.tl.kTX.back? = some (Verify.borderOf Zq.p.X.y).kxb) :
    ((ProofFile.k2Pure Zq).blocks G).map skel = k2SkelW := by
  have e := ProofFile.Law.blankBy_first hG
  exact k2_row_spots hs hz (by rw [e]; exact u1) (by rw [e]; exact u2) t3 t4 t5
    (hH_at_blank hZ hG hN hq hX hK)

theorem k2_lotW_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray}
    {layout : Option ByteArray} {Zq : Pub} {G : Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq) (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G)
    (hX : Verify.publicOf pol' KL' layout = .ok Zq.p.X)
    (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Zq.first.shape) (u2 : proofSizedFull.codes = Zq.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hN : Zq.p.X.NGr = 12)
    (hq : Zq.p.X.p4 = true)
    (hK : Zq.p.X.owner.tl.kTX.back? = some (Verify.borderOf Zq.p.X.y).kxb) (as : List Place)
    (ls : List Nat) : lotW as ls (lotSk G (ProofFile.k2Pure Zq)) = ProofFile.Sk.Full.lot2 := by
  have e := ProofFile.Law.blankBy_first hG
  rw [k2_lotSk_spots hs hz (by rw [e]; exact u1) (by rw [e]; exact u2) t3 t4 t5
    (hH_at_blank hZ hG hN hq hX hK), k2SkelW_full]
  simp [lotW, ProofFile.Sk.Full.lot2, ProofFile.Sk.Full.lot2Batch]

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.k2_row_at_blank
#print axioms Johnson.AtFull.Lots.K2.k2_lotW_at_blank

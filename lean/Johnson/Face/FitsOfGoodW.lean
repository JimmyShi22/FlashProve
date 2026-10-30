-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/FitsOfGoodW.lean: from the compiled verifier's yes at what the whole-key scheme's
committer and prover hand out behind their coins, to `Fits` (Johnson/Prover/Print/FormBack.lean).

In plain words. At the letters S of one set of public files, fix the oracle functions and all coins.
Suppose the compiled verifier says yes at the key and the proof that the committer and the prover
hand out. Asked beside the yes: the public numbers' test `NumbersFit` · the drawn place holds the
copy · the lengths of the first table's salts · `DrawFit` · the named premises on bytes `GoodOwes` ·
`StratLaw` of the key file's strategy at every first seed and of the proof file's at every second
seed. Then the key and the proof are the parts of one typed proof `q` with no further tokens, and
`Fits S digestBytes q`. No accept of an interactive verifier is a premise: `ends_of_yes`
(Johnson/WholeKey/EndsOfYes.lean) reads the two that `fits_of_good` asks off the yes.

Main names.
  `Spec.fitsOfGoodW`, `fits_of_goodW`   the statement and its proof.
  `typed_of_parts`   the shape of its end, at nine letters.

Limits. Pointwise in the oracle functions: no probability, and no yes is shown: it is the premise.
Nothing here says that a premise is met, at any honest side or any coin. `GoodOwes` hands in what
`Fits` asks of the digest's length and of the six run values (none of them 32 zero bytes): these are
premises, not earned here. `digestBytes` is any byte string on which `GoodOwes` holds: it is tied to
no digest here. That the goals' parser reads `q` back from the printed form is `decodeD_formOf`
(Johnson/Prover/Print/FormBack.lean), not this file. Nothing on soundness. It states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.EndsOfYes
import Johnson.Prover.Print.FitsOfGood
import Johnson.Prover.Print.StratLaw
import Johnson.Prover.At.NumBack
import Johnson.Prover.At.ToldAt
import Johnson.Prover.At.StratsAt
import Johnson.Prover.At.Printed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print OnBytes.WholeKey

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- the told record at S -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading S c₀ m₀
/-- its ground input -/
local notation "ℜ" => R S c₀ m₀

/-- **The statement.** See the head of this file. -/
def Spec.fitsOfGoodW : Prop :=
  ∀ (reading : (𝔗).D) (_ : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP)
    (side : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) (oracles : Fam (typedOracleFamily 256 (ℜ).queryLayout.K (LC S c₀
                                                                         m₀)))
    (index : (ℜ).Index) (request : XF) (committerCoins : DrawC 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits side.KT
            side.KL)
    (copyCoins : DrawCopy 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits side.KL)
    (proverCoins : DrawP 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits side.KB)
    (_ : committerCoins.copies[proverCoins.j]? = some copyCoins)
    (digestBytes : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC S c₀ m₀))
    (_ : GoodOwes S c₀ m₀ digestBytes salt sL bcT bcL bcB side.capT side.capL side.capB index
        committerCoins.r
      (cutS (2 ^ (ℜ).queryLayout.depth) committerCoins.s) (drawOf (ℜ).queryLayout side committerCoins copyCoins
                    proverCoins))
    (_ : DrawFit (ℜ).queryLayout (ℜ).compilerParameters (drawOf (ℜ).queryLayout side committerCoins copyCoins proverCoins))
    (_ : ∀ j, j < (ℜ).protocol.wordLength → (cutS (2 ^ (ℜ).queryLayout.depth) committerCoins.s j).length = (ℜ).compilerParameters.sMT)
    (_ : ∀ e₁, StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty (side.st.T index committerCoins.r e₁ committerCoins.κ) bcT.run2 bcT.run3)
    (_ : ∀ e₂, StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty (side.st.B index copyCoins.r e₂ request (side.nm proverCoins.j)
          proverCoins.κ) bcB.run2 bcB.run3)
    (_ : (verifyW (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) (ℜ).fixedSample (ℜ).compilerParameters
      ((commitAt (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) side index committerCoins).det oracles).1
          request
      ((proveAt (ℜ).queryLayout ((𝔗).cA reading) (ℜ).fixedSample side
        ((commitAt (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) side index committerCoins).det
            oracles).2 request proverCoins).det oracles)).det oracles = true),
    ∃ q : Typed S, q.aux = [] ∧
      lowKey ((commitAt (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) side index committerCoins).det
          oracles).1 = ⟨q.cm, q.rcd⟩ ∧
      lowPrf ((commitAt (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) side index committerCoins).det
          oracles).1
        ((proveAt (ℜ).queryLayout ((𝔗).cA reading) (ℜ).fixedSample side
          ((commitAt (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) side index committerCoins).det
              oracles).2 request proverCoins).det oracles) =
        ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩ ∧
      Fits S digestBytes q

/-- The shape of the statement's end, at nine letters: so that no written part is compared. -/
theorem typed_of_parts (digestBytes : ByteArray) (cm : Dig 256) (rcd : RecFull) (copy : ℕ)
    (piT : OneProtocolProof 256 (QT S)) (cm' : Dig 256) (rcd' : RecFull) (piL : OneProtocolProof 256 (QL S))
    (piB : OneProtocolProof 256 (QB S)) (hF : Fits S digestBytes ⟨[], cm, rcd, copy, piT, cm', rcd', piL, piB⟩)
    (key : KeyRoot 256 (ℜ).protocol) (hk : key = ⟨cm, rcd⟩) (proof : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (hp : proof = ⟨copy, some piT, (cm', rcd', some piL), some piB⟩) :
    ∃ q : Typed S, q.aux = [] ∧ key = ⟨q.cm, q.rcd⟩ ∧
      proof = ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩ ∧ Fits S digestBytes q
          :=
  ⟨_, rfl, hk, hp, hF⟩

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

set_option maxRecDepth 20000 in
/-- **`Spec.fitsOfGoodW` holds.** -/
theorem fits_of_goodW : Spec.fitsOfGoodW S c₀ m₀ := by
  intro reading numbers side oracles index request committerCoins copyCoins proverCoins atPlace
      digestBytes salt sL bcT bcL bcB goodOwes drawFits saltLengths lawT lawB verifierSaysYes
  have wires := wiresFit_layoutsByPublicReading S c₀ m₀ reading numbers
  obtain ⟨π, e₁, e₂, τT, τL, τB, hπ, hk, hE, acceptT, acceptB, hn⟩ :=
    ends_of_yes (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) (ℜ).fixedSample (ℜ).compilerParameters side oracles wires index
        request committerCoins copyCoins proverCoins atPlace saltLengths drawFits verifierSaysYes
  obtain ⟨πT, πL, πB, hparts, hF⟩ := fits_of_good S c₀ m₀ ((𝔗).Sd reading) ((𝔗).cA reading) side.b₀
      side.st.joint
    side.capT side.capL side.capB oracles index committerCoins.r (cutS (2 ^ (ℜ).queryLayout.depth)
        committerCoins.s) request (drawOf (ℜ).queryLayout side committerCoins copyCoins proverCoins) π e₁ e₂
    τT τL τB digestBytes salt sL bcT bcL bcB hE wires acceptT acceptB goodOwes fun πT πL πB hparts
        =>
      have owes := stratsOwe_fullD (S.inputFieldsAtReadings c₀ m₀) ((𝔗).Sd reading) ((𝔗).cA reading) side.b₀
          side.st.joint side.capT
        side.capL side.capB oracles index committerCoins.r (cutS (2 ^ (ℜ).queryLayout.depth)
            committerCoins.s) request (drawOf (ℜ).queryLayout side committerCoins copyCoins proverCoins) π e₁
            e₂
        τT τL τB bcT bcB hE (lawT e₁) (lawB e₂) _ _ _ πT πL πB hparts
      ⟨owes.1, owes.2, copy_of_num_layoutsByPublicReading S c₀ m₀ reading _ πB (by
                          rw [plainsB_of_ends (ℜ).queryLayout ((𝔗).Sd reading) ((𝔗).cA reading) (ℜ).fixedSample side.b₀ side.st.joint
                              side.capT side.capL
                            side.capB oracles index committerCoins.r (cutS (2 ^ (ℜ).queryLayout.depth) committerCoins.s)
                                request (drawOf (ℜ).queryLayout side committerCoins copyCoins proverCoins) π e₁ e₂ τT τL τB
                            hE _ _ _ πB hparts]
                          exact hn)⟩
  exact typed_of_parts S c₀ m₀ digestBytes _ _ _ _ _ _ _ _ hF _ hk _ (hπ.symm.trans hparts)

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.typed_of_parts
#print axioms Johnson.Prover.Print.fits_of_goodW

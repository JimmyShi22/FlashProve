-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkVLA.lean: stagesW_yes (StrictLinkW.lean) LAID AT verifyLinkProof's OWN BODY: the compiled Link of
innerCompiledVerifier's entry arm (Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean:88-91), at the object with records LrG T whose Link is the written
link over letters (linkProtocolOfRoundData C ds a xs dec) and at the wiring that okla_sib speaks of (Johnson/EntryRec/OklaSib.lean:98-116):
wireOf2 with wSib T K chal as Link's wire and bodiesSib as the eight maps.
  batLC_is     batLC (LrG T) (allLo (SOf C ds)) is (linkSkeletonOfRoundData C ds a xs dec).up: by rfl: AT THE SAME LETTERS ON BOTH SIDES: it is the shipped
               batLC_sib (Johnson/Flat/ArmString.lean) said with linkSkeletonOfRoundData: no bridge between two sets of letters
  wqW_wSib, wqW_sibW   the wire wqW is wSib's and sibW's text: by rfl
  **vLA_stages**   at every family F, every p, roots, records and code cA of the answers: verifyLinkProof's value at F is «the fourteen
               lines all say yes behind a chain that returns», at the string that assembleW lays
What it would give: the entry's clause «(verifyLinkProof ..).det F = true» from a yes of the fourteen lines AT THAT F, cms, K, p.
What it does not give: a run at such letters: no family with code at this carrier is written here (the coding m is left to other
files); T, K, chal, p, cA and the wires of Test and the session are letters; that innerCompiledVerifier's input has this make is not
said here. IT STANDS AT ONE SET OF LETTERS: at the written letters of innerCompiledVerifier's object ((ckP .two) dsFull | dsSmall ..) the right side has
no code (frC | srC are noncomputable); these letters are the description's own, at which the runs stood, by
theorems (letters_full | letters_small, OnBytes/Flat/LinkSibAt.lean), not by unfolding; nothing here carries the strict verifier,
stagesW or the string along them. Nothing has been evaluated at verifyLinkProof's letters. Nothing on soundness.

-/
import Johnson.RunOne.StrictLinkW
import Johnson.EntryRec.OklaSib
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import OnBytes.K.Arm.SameSib

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.StrictW
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (wqX SOf)
open _root_.Run.PQ (View SgX CK XO)
open OnBytes.Flat (linkSkeletonOfRoundData linkProtocolOfRoundData)
open OnBytes.RunA (RestR LrG wSib bodiesSib)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wireOf2 typedOracleCarrier verifyLinkProof cmsLA)
open Johnson.RunOne.StrictB

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List PQ.RD} {xs : List XO}
  {dec : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- Link with its annotation is the skeleton's protocol. -/
theorem batLC_is :
    batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)) = (linkSkeletonOfRoundData C ds a xs dec).up := rfl

/-- The wire over letters is Link's wire record of the object, field for field. -/
theorem wqW_wSib : wSib T K chal = wqW C ds a xs dec K chal := rfl

/-- And the sibling's. -/
theorem wqW_sibW : OnBytes.K.Arm.sibW C ds a xs K chal dec = wqW C ds a xs dec K chal := rfl

variable {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT)) (wB : ProtocolQueryLayout 256 (K + 1) T.bat)
  (depthReq depthReqT depthReqL salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))

/-- The wiring of which okla_sib speaks. -/
abbrev WSib : QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) :=
  wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
    (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB)

/-- **verifyLinkProof's value is the fourteen lines' yes.** -/
theorem vLA_stages (cA : Ans → List (Dig 256)) (p : Params) (cm cm' : Dig 256)
    (rec rec' : Seed × Ans)
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1)
      (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))
    (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    (verifyLinkProof (WSib T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB) cA p cm cm'
        rec rec' π).det F =
      ((stagesW C ds a xs dec K chal
          (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) p.sMT p.sFS
          (TypedOracleCompiler.StringsList.embT salt C ds) id (fun _ => none)
          (TypedOracleCompiler.Run.PQ.bodyS a salt).embE depthReqL F
          (cmsLA (L := LrG T) cA cm cm' rec.2 rec'.2) (rec, rec') π tab tx).map
        OnBytes.Maker.Steps.yes).getD false :=
  (stagesW_yes C ds a xs dec K chal
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) p.sMT p.sFS
    (TypedOracleCompiler.StringsList.embT salt C ds) id (fun _ => none)
    (TypedOracleCompiler.Run.PQ.bodyS a salt).embE depthReqL F (cmsLA (L := LrG T) cA cm cm' rec.2 rec'.2) (rec, rec')
    cfg o tab tx π h).symm

end

end Johnson.RunOne.StrictW

#print axioms Johnson.RunOne.StrictW.batLC_is
#print axioms Johnson.RunOne.StrictW.wqW_wSib
#print axioms Johnson.RunOne.StrictW.wqW_sibW
#check @Johnson.RunOne.StrictW.vLA_stages
#print axioms Johnson.RunOne.StrictW.vLA_stages

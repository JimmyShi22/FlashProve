-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/Seed.lean: the out-of-domain (OOD) seed that the written committer reads at a
root by its two typed queries, spelled, is the format's draw from the table's name: the proposition
`Bind.Cpp.SpellsSeed` (Johnson/Bind/Cpp/Spells.lean), at all public files and every hash function,
from `SpellsC`. Statements with proofs. No definition: no goal is stated.
Why. See Johnson/Bind/Spell/Leaf.lean. This file spells the seed's two typed queries (`seedQ0`,
`seedQ1`, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) and what the wire makes of the answers.
The road, from letters up.
  `mFOneD_seed0`, `mFOneD_seed1`: at the coding `PV.MFull.mFOneD`, at letters: the string of the
    first query at the block of the chain value is the format's call 160 on the table's name; the
    string of the second query at every block is one half of a call 162 of the seeds' round. From
    `mF_codeD`, `code_seed` (CutCode.lean), `fbSeeds_q0` (OnBytes/TypedOracleCompiler/Run/SeedPoints.lean) and
    `fbSeeds_q1_wide` (SeedWide.lean).
  `mFOneD_seedDigs`, `mD_seedDigs`: so the digests that the second query reads out of a hash
    function are `OnBytes.K.seedDigsO` (OnBytes/K/SeedBytesG.lean) at that function read on byte
    strings.
  `slice_recordSeedsW`, `triple_back`: the text of `recordSeeds` with the Lean verifier's elements,
    `OnBytes.E` (OnBytes/Slice/RecordRead.lean), is `Fmt.recordSeedsW` (Fmt/RecordSeeds.lean),
    element by element.
  `seed_at`: at `T₀ Z`, AT EVERY d: the seed is the wire's `recSeedK` of these digests.
  **`spellsSeed_of`**: `SpellsSeed Z hash`, from `SpellsC Z hash`. Through `wire_recSeedK`
    (OnBytes/K/Left/SeedWire.lean), `seedsOfDigs_seedDigsG`, `recordSeeds_blocksG` (SeedBytesG.lean)
    and `spell_recordSeedsW` (OnBytes/K/IdSeedSpell.lean).
  `draw_some`: the format's draw returns something there, at every hash function: so the filler of
    `getD` in `SpellsSeed` is never met, and it is not the filler that makes the equation true.
    `draw_shaped`: what it returns is one seed with a point of 29 coordinates
    (`Fmt.recordSeedsW_shaped`, Fmt/RecordSeedsLaws.lean): the equation is not one between two empty
    lists.
Limits. Equations between values of this library's own terms: NOTHING ON ANY PROGRAM, and nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding. Nothing on how the seed is distributed. `SpellsC` is a
premise here and is not proved here (Closed.lean lays its theorem in). VALUES, NOT COUNTS: at the
first typed query the block of the chain value alone is spelled here; what stands at its other
blocks is not said here, and they are not read; the typed queries ask K + 1 strings each, the
format's text fewer. The six words of the table's shape in the name are constants on both sides (the
salt's 40 among them), whatever the plan at Z says. That `Fmt.recordSeedsW` is what the format's
page says, and that any program computes it, is not said here (Fmt/RecordSeeds.lean's own limits).
At the full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Cpp.Spells
import Johnson.Bind.Spell.CutCode
import Johnson.Bind.Spell.SeedWide
import OnBytes.K.SeedBytesG
import OnBytes.K.Left.SeedWire
import OnBytes.K.IdSeedSpell
import Fmt.RecordSeedsLaws
import Run.Toy1TieTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Spell

section AtLetters
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub OnBytes.Tie TypedOracleCompiler.Slice
open VerifiableInference.OnPublicFiles
open OnBytes.K.Arm
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open PV.OkOwn (okOwnF)
open PV.MFull

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (salt : ℕ) (K : ℕ)
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (it : ReqAt Inst.Model.ppref → ByteArray) (r₀ : RecFull)
  (c : ByteArray) (hc : c.size = 32) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
  (hK : K + 1 + 1 < 2 ^ 49)

/-- The string of the seed's first typed query, at the block of the chain value. -/
theorem mFOneD_seed0 (cm : Dig 256) :
    (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP
        hK).code
        (.fb .test) (SeedPoints.q0 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
          (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (SeedVals.cfgL c) pubShapeTopFull
              cm)
        (Fin.last (K + 1)) =
      bytesToBits (Fmt.oStr 0 160 0 Fmt.recordLabel Fmt.zero32
        (Fmt.firstBytes Fmt.zero32 (digToBytes cm ++ pubRestTopFull c) ByteArray.empty none)) := by
  rw [← mF_codeD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK
      hDP hK (.fb .test) (by decide)]
  refine code_seed _ _ _ _ _ ?_
  exact SeedPoints.fbSeeds_q0 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
    (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (SeedVals.cfgL c) pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (pubRestTopFull c) (K + 1) cm (SeedVals.rest_small c hc _ _ _ _ _ _)

/-- The string of the seed's second typed query, at every block. -/
theorem mFOneD_seed1 (v : Bits) (hv : v.length = 256) (j : Fin (K + 1 + 1)) :
    (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP
        hK).code
        (.fb .test) (SeedPoints.q1 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
          (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) v) j =
      bytesToBits (Fmt.oStr (UInt8.ofNat (blockNo 0 (K + 1) j % 2)) 162 Fmt.recordLabel 1
        (bitsToBytes v) (ByteArray.empty ++ Fmt.tail .seeds 0 0 (blockNo 0 (K + 1) j / 2))) := by
  rw [← mF_codeD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK
      hDP hK (.fb .test) (by decide)]
  refine code_seed _ _ _ _ _ ?_
  exact fbSeeds_q1_wide (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
    (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (SeedVals.cfgL c) pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD))
    (pubRestTopFull c) (K + 1) (by omega) v hv j

/-- The half's byte, written in two ways. -/
theorem half_byte (b : ℕ) : UInt8.ofNat (b % 2) = (if b % 2 = 0 then 0 else 1 : UInt8) := by
  rcases Nat.mod_two_eq_zero_or_one b with e | e
  · rw [e, if_pos rfl]
    rfl
  · rw [e, if_neg (by decide)]
    rfl

/-- **The digests that the seed's two typed queries at a root read out of a hash function** are the
blocks of the seeds' round at the table's name, at the hash function read on byte strings. -/
theorem mFOneD_seedDigs (g : Fam (rom 256)) (cm : Dig 256) :
    (readBlocks (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK
        dP hDK hDP hK) g
        (.fb .test) (SeedPoints.q1 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
          (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
          (TypedOracleCompiler.Compile.Batch.link (readBlocks (mFOneD DK DP runK runP dec rK rP depthReq
                      early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK) g
                    (.fb .test) (SeedPoints.q0 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
                        .test
                      (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (SeedVals.cfgL c)
                      pubShapeTopFull cm) : TypedOracleCompiler.Compile.Batch.FsAns 256 (K + 1)))) :
                  TypedOracleCompiler.Compile.Batch.FsAns 256 (K + 1)).1 =
      OnBytes.K.seedDigsO (_root_.Run.oB (g ())) (digToBytes cm ++ pubRestTopFull c) (K + 1) := by
  funext i
  have h0 : (readBlocks (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc
      sR pdL dK dP hDK hDP hK) g
      (.fb .test) (SeedPoints.q0 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) .test
        (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (SeedVals.cfgL c)
        pubShapeTopFull cm) : TypedOracleCompiler.Compile.Batch.FsAns 256 (K + 1)).2 =
      g () (bytesToBits (OnBytes.K.seedFirst (digToBytes cm ++ pubRestTopFull c))) := by
    rw [OnBytes.K.seedFirst, ← mFOneD_seed0 DK DP runK runP dec rK rP depthReq early salt K h₀ k c'
        it r₀ c hc sR pdL dK dP hDK hDP hK cm]
    rfl
  unfold TypedOracleCompiler.Compile.Batch.link
  rw [h0]
  show g () ((mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP
      hDK hDP hK).code
    (.fb .test) _ i.castSucc) = _
  rw [mFOneD_seed1 DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP
      hDK hDP hK _
    (List.length_ofFn) i.castSucc, SeedRound.blockNo_cast, half_byte]
  unfold OnBytes.K.seedDigsO OnBytes.K.seedBlockO OnBytes.K.seedStr _root_.Run.oB
  rw [_root_.Run.TieTree.bytes_dig]
  rfl

end AtLetters

section AtReading
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open OnBytes.K.Arm.Pub
open PV.EntryFive (dsF xsF)
open LPFD.Full

variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull)
  (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool)
  (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
  (hK : KF DK DP + 1 + 1 < 2 ^ 49)

/-- The digests of the seed's two typed queries at a root, under the run's coding at d. -/
theorem mD_seedDigs (d : D8) (g : Fam (rom 256)) (cm : Dig 256) :
    (readBlocks (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d) g (.fb .test)
        (TypedOracleCompiler.Run.SeedPoints.q1 (CsAtR A E G DK DP runK runP dec P) .test
          (PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec)
            PV.MFull.aLD)
          (TypedOracleCompiler.Compile.Batch.link
            (readBlocks (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d) g (.fb .test)
              (TypedOracleCompiler.Run.SeedPoints.q0 (CsAtR A E G DK DP runK runP dec P) .test
                (PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
                  (PV.MFull.lkD dec) PV.MFull.aLD)
                (TypedOracleCompiler.Run.SeedVals.cfgL (digToBytes d.1)) pubShapeTopFull cm) :
              TypedOracleCompiler.Compile.Batch.FsAns 256 (KF DK DP + 1)))) :
        TypedOracleCompiler.Compile.Batch.FsAns 256 (KF DK DP + 1)).1 =
      OnBytes.K.seedDigsO (_root_.Run.oB (g ())) (digToBytes cm ++ pubRestTopFull (digToBytes d.1))
        (KF DK DP + 1) := by
  unfold mD mOneAt
  exact mFOneD_seedDigs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g cm

end AtReading

noncomputable section
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.IdTable
open _root_.Iop (Dig)
open _root_.Run (bytesToBits digToBytes bytesToDig leafSalt)
open OnBytes.K.Arm.Pub (pubRestTopFull pubShapeTopFull)
open Bind.Cpp

/-- The text of `recordSeeds` with the Lean verifier's elements is the format's own draw, element by
element. At every plain hash. -/
theorem slice_recordSeedsW (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (f : Fmt.Fld)
    (name : ByteArray) (bits count : ℕ) :
    OnBytes.Slice.recordSeedsW (m := Id) h f name bits count =
      (Fmt.recordSeedsW (m := Id) h f name bits count).map fun l =>
        l.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2) := by
  have e := Fmt.recordSeedsW_run h f name bits count
  rw [OnBytes.Slice.recordSeedsW_pure, OnBytes.timesT_eq]
  show _ = (Id.run (Fmt.recordSeedsW h f name bits count)).map _
  rw [e, Option.map_map]
  rfl

/-- Back from the Lean verifier's elements to the format's. -/
theorem triple_back (l : List (List Fmt.Ext × Fmt.Ext)) :
    (l.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)).map
      (fun y => (y.1.map OnBytes.E.triple, y.2.triple)) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun y _ => ?_
  show ((y.1.map OnBytes.E.ofTriple).map OnBytes.E.triple, (OnBytes.E.ofTriple y.2).triple) = y
  rw [List.map_map]
  have e : (OnBytes.E.triple ∘ OnBytes.E.ofTriple) = id := funext fun t => OnBytes.E.triple_ofTriple
      t
  rw [e, List.map_id]
  rfl

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem
  LPFD.Full.mD

/-- The table's name at a root, at the bytes of the public reading's first answer. -/
theorem name_eq (c root : ByteArray) :
    Fmt.tableName root c 32 402653184 44040191 11 1 40 = root ++ pubRestTopFull c :=
  TypedOracleCompiler.Run.FirstName.tableName_eq root c 32 402653184 44040191 11 1 40

/-- **The OOD seed that the written committer reads at a root**, AT EVERY d: the wire's seed of the
blocks of the seeds' round at the table's name. -/
theorem seed_at (Z : PublicFiles) (d : (T₀ Z).D) (g : Fam (rom 256)) (root : Dig 256) :
    ((T₀ Z).Sd d).seed
      (readBlocks ((T₀ Z).m d) g (OracleName.fb ((T₀ Z).Sd d).t)
        (seedQ1 (R₀ Z).queryLayout ((T₀ Z).Sd d)
          (link (readBlocks ((T₀ Z).m d) g (OracleName.fb ((T₀ Z).Sd d).t)
            (seedQ0 (R₀ Z).queryLayout ((T₀ Z).Sd d) root) : FsAns 256 (R₀ Z).queryLayout.K))) :
        FsAns 256 (R₀ Z).queryLayout.K).1 =
      recSeedK recT recLg recS (R₀ Z).queryLayout.K ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).hK
        (OnBytes.K.seedDigsO (_root_.Run.oB (g ()))
          (digToBytes root ++ pubRestTopFull (digToBytes ((T₀ Z).part d))) (R₀ Z).queryLayout.K) :=
  congrArg (recSeedK recT recLg recS (R₀ Z).queryLayout.K ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).hK)
    (mD_seedDigs (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).G
      (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
      (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).P (dataAtFiles flashProveData Z).hStar (dataAtFiles flashProveData Z).it
      (dataAtFiles flashProveData Z).sR (dataAtFiles flashProveData Z).hDK (dataAtFiles flashProveData Z).hDP (dataAtFiles flashProveData Z).hK d g
          root)

/-- **`SpellsSeed Z hash`**, at all public files and every hash function, from `SpellsC Z hash`.
The format's draw returns something there: the filler of `getD` is not met (`draw_some`). -/
theorem spellsSeed_of (Z : PublicFiles) (hash : Hash) (hc : SpellsC Z hash) : SpellsSeed Z hash := by
  intro root
  have hO : ∀ s, (_root_.Run.oB hash s).size = 32 := fun s => _root_.Run.size_digToBytes _
  have hcB : digToBytes ((T₀ Z).part (dAt Z hash)) = Bind.Cpp.cAt Z hash := by
    unfold Bind.Cpp.cAt
    rw [hc]
  have hs : seedAtRoot Z hash root =
      TypedOracleCompiler.Slice.seedOfC 29 1 (OnBytes.K.seedsOfDigs .two 29 1
                (OnBytes.K.seedDigsO (_root_.Run.oB hash) (nameAt Z hash root) (R₀ Z).queryLayout.K)) := by
    have h1 := seed_at Z (dAt Z hash) (_root_.Run.famOne hash) root
    rw [hcB, ← name_eq] at h1
    exact h1.trans (OnBytes.K.Left.wire_recSeedK recT 29 1 (R₀ Z).queryLayout.K
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).hK _)
  have hl : OnBytes.Slice.recordSeedsW (m := Id) (Fmt.HO (_root_.Run.oB hash)) .two
      (nameAt Z hash root) 29 1 =
      some (OnBytes.K.seedsAtNameO (_root_.Run.oB hash) .two (nameAt Z hash root) 29 1) :=
    OnBytes.K.recordSeeds_blocksG (_root_.Run.oB hash) hO .two (nameAt Z hash root) 29 1
  rw [hs, OnBytes.K.seedsOfDigs_seedDigsG (_root_.Run.oB hash) hO .two (nameAt Z hash root) 29 1
    (R₀ Z).queryLayout.K (OnBytes.K.Left.room_recSeedK ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).hK),
    spell_recordSeedsW (Fmt.HO (_root_.Run.oB hash)) (nameAt Z hash root) 29 1 _ hl]
  have hH : hAt hash = Fmt.HO (_root_.Run.oB hash) := by
    funext a b c d e
    exact Fmt.HM_id _ a b c d e
  rw [slice_recordSeedsW] at hl
  obtain ⟨l, h1, h2⟩ := Option.map_eq_some_iff.1 hl
  rw [hH, h1, ← h2, triple_back]
  rfl

/-- The format's draw at the table's name returns something, at every hash function. -/
theorem draw_some (Z : PublicFiles) (hash : Hash) (root : Dig 256) :
    ∃ l, Fmt.recordSeedsW (m := Id) (hAt hash) .two (nameAt Z hash root) 29 1 = some l := by
  have hO : ∀ s, (_root_.Run.oB hash s).size = 32 := fun s => _root_.Run.size_digToBytes _
  have hl := OnBytes.K.recordSeeds_blocksG (_root_.Run.oB hash) hO .two (nameAt Z hash root) 29 1
  have hl' : OnBytes.Slice.recordSeedsW (m := Id) (Fmt.HO (_root_.Run.oB hash)) .two
      (nameAt Z hash root) 29 1 = some _ := hl
  have hH : hAt hash = Fmt.HO (_root_.Run.oB hash) := by
    funext a b c d e
    exact Fmt.HM_id _ a b c d e
  rw [slice_recordSeedsW] at hl'
  obtain ⟨l, h1, -⟩ := Option.map_eq_some_iff.1 hl'
  exact ⟨l, hH ▸ h1⟩

/-- And what it returns has the form of one seed with a point of 29 coordinates. -/
theorem draw_shaped (Z : PublicFiles) (hash : Hash) (root : Dig 256) :
    ∃ l, Fmt.recordSeedsW (m := Id) (hAt hash) .two (nameAt Z hash root) 29 1 = some l ∧
      Fmt.SeedsShaped .two 29 1 l := by
  obtain ⟨l, hl⟩ := draw_some Z hash root
  exact ⟨l, hl, Fmt.recordSeedsW_shaped (hAt hash) .two (nameAt Z hash root) 29 1 l hl⟩

end
end Bind.Spell

#print axioms Bind.Spell.mFOneD_seed0
#print axioms Bind.Spell.mFOneD_seed1
#print axioms Bind.Spell.half_byte
#print axioms Bind.Spell.mFOneD_seedDigs
#print axioms Bind.Spell.mD_seedDigs
#print axioms Bind.Spell.slice_recordSeedsW
#print axioms Bind.Spell.triple_back
#print axioms Bind.Spell.name_eq
#print axioms Bind.Spell.seed_at
#print axioms Bind.Spell.spellsSeed_of
#print axioms Bind.Spell.draw_some
#print axioms Bind.Spell.draw_shaped

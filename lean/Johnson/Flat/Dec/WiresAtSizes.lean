-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/WiresAtSizes.lean: A TWIN OF Johnson/Flat/WiresAtSizes.lean, WITH THE ENTRY FILE's THREE LETTERS FREE: ds (its rounds' data), xs (its openings of stored
tables), dec (its decision), in that order behind runP.

Why. The original's frame lays the entry file's protocol as the written link at written rounds' data, written openings and THE DECISION OF
`verify-on-bytes` (`fun rr => decFullX (recX rr)` | `decSmallX`). A verifier whose entry file's decision is another text is then no
member of the frame, and neither the tie from what runs nor the conditional soundness theorem can speak of it.
How it was made. Most declared names get a D or lose «WithFixedLink»; `ds xs dec` stand behind `runP` in every list of letters;
`linkSibFull` | `linkSibSmall` became `linkFullD ds xs dec` | `linkSmallD ds xs dec`; `dsFull` | `dsSmall` became ds, `frD.xs` | `srD.xs`
xs. All else is the original's text, docstrings too: WHERE A DOCSTRING SAYS «written» OR NAMES A FILE IT SPEAKS OF THE TEXT OF WHICH
THIS IS A TWIN. Left out: `depth_of_fit` (the original's is called) and the four controls at the makers' G. OTHER THAN THE ORIGINAL: `wiresOfFullD` | `…SmallD`: hk is asked at the two whole files' rounds alone (`kThree .two DK [] DP ≤ K`), and of ds four tests on numbers are premises: bL (no round has more than K blocks), wLk (none more than 64 bits of work), own (every number of a tree that a round opens is below 2 ^ 16), dL (no tree deeper than 63).
Limits: those of the original's head. Nothing on soundness is gained: in the conditional theorem
`entrySound` becomes a named hypothesis, in the place of the theorem on codes, from which
Johnson/Flat/TwoSizesAt.lean proves it for the written letters alone; and four tests on the numbers
of ds become premises, which the original proves of the written data.

-/
import Johnson.EntryRec.FilesLaws
import Johnson.EntryRec.AtConf
import Johnson.Flat.WireAt
import Johnson.Flat.WiresAtSizes
import Johnson.Flat.Dec.RestSib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm (linkProtocolWithWireOfRoundData)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

/-! ## The full size -/

/-- The entry file's part at the full size, with K blocks for a round's verifier message:
`linkProtocolWithWireOfRoundData` (Johnson/Top/EntrySib.lean), called at the written link's letters. -/
def linkProtocolWithWireAtFullSize (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (dec : RecFull × RecFull → PQ.View → Bool)
    (K salt : ℕ) : LinkProtocolWithLeafCodingAndQueryLayout RecFull frS.P.T.a 0 :=
  linkProtocolWithWireOfRoundData (ckP .two) ds xs dec salt 0 K (Nat.zero_le K)
    (chalP .two K)

/-- Its protocol, marks and two maps, taken at K := 0. That they are the same at every K is seen by
unfolding alone (`linkWireOK_sib` is spent so in `wiresOfFullD`); no lemma states it. -/
@[reducible] def linkProtocolAtFullSize (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (dec : RecFull × RecFull → PQ.View → Bool)
    (salt : ℕ) : LinkProtocolWithLeafCoding RecFull frS.P.T.a := (linkProtocolWithWireAtFullSize ds xs dec 0 salt).toLinkProtocolWithLeafCoding

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)

/-- **The three files' protocols at the full size, at any data of rounds and any two decisions**:
`filesAt`, called. -/
@[reducible] def threeProtocolsAtFullSize : Files (DecR.configurationOfStoredTable A R) :=
  filesAt A R .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none

/-- The three verifiers read their oracles at the declared positions alone. -/
theorem threeProtocolsAtFullSize_local :
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).key.IsLocal ∧
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).entry.IsLocal ∧
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).proof.IsLocal :=
  ⟨filesOf_keyLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) _
      early none,
    (linkW_local (ckP .two) ds frS.P.T.a xs dec),
    filesOf_proofLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (linkProtocolAtFullSize ds xs dec salt)
      _ early none⟩

/-- The two whole files' marks are coherent. -/
theorem threeProtocolsAtFullSize_coherent :
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT.Coherent ∧
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).ann.Coherent :=
  filesOf_coherent (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) _
    early none

/-- The entry file's marks are coherent. -/
theorem threeProtocolsAtFullSize_entryCoherent :
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

variable (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **The wiring, with K blocks for a round's verifier message**: `wireF`, called, with
the bodies `bodiesF`. -/
def wireOfFullD (K depthReqT : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
            (List Bool)
            (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT
            (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL) :=
  wireF .two K frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none P)
    (linkProtocolWithWireAtFullSize ds xs dec K salt).wL (List Bool) depthReq depthReqT 0
    (bodiesF .two frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none P)
      salt (embStored frS.P.T.a salt) (prjStored frS.P.T.a salt))

/-- **The four laws of the wires**, from tests on numbers: no round of the three files has more than
K blocks (hk); in neither whole file a round has more than 64 bits of work (wK, wP) or a tree deeper
than 63 (dK, dP). -/
theorem wiresOfFullD (K depthReqT : ℕ) (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) :
    Four (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) := by
  exact four_files .two K frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
    (join₀ rP) ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none P)
    (linkProtocolWithWireAtFullSize ds xs dec K salt).wL (List Bool) depthReq depthReqT 0 _
    (fun d hd => (kThree_key .two DK [] DP d hd).trans hk) ((WholeD.workFit_iff DK).1 wK)
    (linkWireOK_sib .two frS.P.T.a ds xs _ salt 0 K (Nat.zero_le _) bL wLk own)
    (fun d hd => (kThree_proof .two DK [] DP d hd).trans hk) ((WholeD.workFit_iff DP).1 wP) rfl
    (bodiesF_ok .two frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none P)
      salt (embStored frS.P.T.a salt) (prjStored frS.P.T.a salt)
      (prjStored_embStored frS.P.T.a salt) (depth_of_fit dK)
      (bodies_sib .two frS.P.T.a ds xs _ salt 0 0 (Nat.zero_le 0) dL)
      (depth_of_fit dP))

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restOfFullD :=
  restSibFullD A R (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt) P ds xs dec P.hL

/-- **The wiring in the text of Johnson/Flat/WireAt.lean** (`wireFullK`): `wireOf2` at the two whole
files' wire records, the written link's `wSib` and the bodies `bodiesSib`: by unfolding. -/
theorem wireOfFull_eq_sibD (K depthReqT : ℕ) :
    wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT =
      wireOf2 (L := LrG (restOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P))
        (aT := (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT)
        (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)) (K + 1)
        (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK)
        (wSib (restOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) K (chalP .two K))
        (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP)
        frS.P.T.a depthReq depthReqT 0
        (bodiesSib (restOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) salt
          (SCode.emb _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.emb _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))) := rfl

end

/-! ## The small size -/

/-- The entry file's part at the small size, with K blocks for a round's verifier message:
`linkProtocolWithWireOfRoundData` (Johnson/Top/EntrySib.lean), called at the written link's letters. -/
def entrySmallMD (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (dec : RecSmall × RecSmall → PQ.View → Bool)
    (K salt : ℕ) : LinkProtocolWithLeafCodingAndQueryLayout RecSmall srS.P.T.a 0 :=
  linkProtocolWithWireOfRoundData (ckP .two) ds xs dec salt 0 K (Nat.zero_le K)
    (chalP .two K)

/-- Its protocol, marks and two maps, taken at K := 0. That they are the same at every K is seen by
unfolding alone (`linkWireOK_sib` is spent so in `wiresOfSmallD`); no lemma states it. -/
@[reducible] def entrySmallQD (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (dec : RecSmall × RecSmall → PQ.View → Bool)
    (salt : ℕ) : LinkProtocolWithLeafCoding RecSmall srS.P.T.a := (entrySmallMD ds xs dec 0 salt).toLinkProtocolWithLeafCoding

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)

/-- **The three files' protocols at the small size, at any data of rounds and any two decisions**:
`filesAt`, called. -/
@[reducible] def threeProtocolsAtSmallSize : Files (DecR.configurationOfStoredTable A R) :=
  filesAt A R .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt) (2 ^ depthReq) early none

/-- The three verifiers read their oracles at the declared positions alone. -/
theorem threeProtocolsAtSmallSize_local :
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).key.IsLocal ∧
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).entry.IsLocal ∧
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).proof.IsLocal :=
  ⟨filesOf_keyLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQD ds xs dec salt) _
      early none,
    (linkW_local (ckP .two) ds srS.P.T.a xs dec),
    filesOf_proofLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQD ds xs dec salt)
      _ early none⟩

/-- The two whole files' marks are coherent. -/
theorem threeProtocolsAtSmallSize_coherent :
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT.Coherent ∧
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).ann.Coherent :=
  filesOf_coherent (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQD ds xs dec salt) _
    early none

/-- The entry file's marks are coherent. -/
theorem threeProtocolsAtSmallSize_entryCoherent :
    (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

variable (P : (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **The wiring, with K blocks for a round's verifier message**: `wireF`, called, with
the bodies `bodiesF`. -/
def wireOfSmallD (K depthReqT : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
            (List Bool)
            (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT
            (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL) :=
  wireF .two K srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt) (2 ^ depthReq) early none P)
    (entrySmallMD ds xs dec K salt).wL (List Bool) depthReq depthReqT 0
    (bodiesF .two srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt) (2 ^ depthReq) early none P)
      salt (embStored srS.P.T.a salt) (prjStored srS.P.T.a salt))

/-- **The four laws of the wires**, from tests on numbers: no round of the three files has more than
K blocks (hk); in neither whole file a round has more than 64 bits of work (wK, wP) or a tree deeper
than 63 (dK, dP). -/
theorem wiresOfSmallD (K depthReqT : ℕ) (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) :
    Four (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) := by
  exact four_files .two K srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
    (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt) (2 ^ depthReq) early none P)
    (entrySmallMD ds xs dec K salt).wL (List Bool) depthReq depthReqT 0 _
    (fun d hd => (kThree_key .two DK [] DP d hd).trans hk) ((WholeD.workFit_iff DK).1 wK)
    (linkWireOK_sib .two srS.P.T.a ds xs _ salt 0 K (Nat.zero_le _) bL wLk own)
    (fun d hd => (kThree_proof .two DK [] DP d hd).trans hk) ((WholeD.workFit_iff DP).1 wP) rfl
    (bodiesF_ok .two srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQD ds xs dec salt) (2 ^ depthReq) early none P)
      salt (embStored srS.P.T.a salt) (prjStored srS.P.T.a salt)
      (prjStored_embStored srS.P.T.a salt) (depth_of_fit dK)
      (bodies_sib .two srS.P.T.a ds xs _ salt 0 0 (Nat.zero_le 0) dL)
      (depth_of_fit dP))

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restOfSmallD :=
  restSibSmallD A R (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt) P ds xs dec P.hL

/-- **The wiring in the text of Johnson/Flat/WireAt.lean** (`wireSmallK`): `wireOf2` at the two
whole files' wire records, the written link's `wSib` and the bodies `bodiesSib`: by unfolding. -/
theorem wireOfSmall_eq_sibD (K depthReqT : ℕ) :
    wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT =
      wireOf2 (L := LrG (restOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P))
        (aT := (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT)
        (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)) (K + 1)
        (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK)
        (wSib (restOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) K (chalP .two K))
        (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP)
        srS.P.T.a depthReq depthReqT 0
        (bodiesSib (restOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) salt
          (SCode.emb _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.emb _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))) := rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_local
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_coherent
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_entryCoherent
#print axioms VerifiableInference.OnPublicFiles.wiresOfFullD
#print axioms VerifiableInference.OnPublicFiles.wireOfFull_eq_sibD
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtSmallSize_local
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtSmallSize_coherent
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsAtSmallSize_entryCoherent
#print axioms VerifiableInference.OnPublicFiles.wiresOfSmallD
#print axioms VerifiableInference.OnPublicFiles.wireOfSmall_eq_sibD

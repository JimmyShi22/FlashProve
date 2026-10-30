-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WiresAtSizes.lean: the three files' protocols at the two sizes of the default setting
with the rounds' data and the two decisions as letters, their wiring, and what the compiler's
theorems ask of both beside soundness.

Definitions by calls, statements and their proofs. OnBytes/Flat/FilesAt.lean lays the key file's and
the proof file's protocol by the makers of OnBytes/Maker/: the rounds' data are those of a dry run
of blocks of the verifier program's type, and the decision is that program's. The make itself lies
at letters: `filesAt` (Johnson/EntryRec/AtConf.lean), `wireF` (OkcFiles.lean), `bodiesF`
(BodiesAt.lean), `four_files` (AtMakerA.lean), `linkProtocolWithWireOfRoundData` (Johnson/Top/EntrySib.lean). Here these
are CALLED at the two sizes: the entry file's part is the written link (`linkSibFull`,
`linkSibSmall`, OnBytes/Flat/LinkSibAt.lean); the silent rounds' fixed messages and tests are those
of `threeProtocolsFromDryRunAtFullSize`, `threeProtocolsFromDryRunAtSmallSize`. The data DK, DP : `WholeD` and the decisions runK, runP on three views
stay letters. No new make is defined.

Main names (the small size alike):
  `entryFullM K salt`, `entryFullQ salt`: the entry's part: `linkProtocolWithWireOfRoundData` at the written link's
    letters.
  `threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt`: the three protocols: `filesAt`,
    called. rK, rP: the records whose answers stand as the silent rounds' fixed messages. Of the
    three protocols no field reads the letter salt: it stands in the entry's part's two maps; the
    wiring reads it (see "Limits"). early: the part of an instance that the queries hold: STILL A
    LETTER (see "Limits").
  `threeProtocolsFromDryRunAtFullSize_eq_withFixedLink`: A CONTROL: `threeProtocolsFromDryRunAtFullSize A R G` is `threeProtocolsWithFixedLinkAtFullSize` at the makers' own data and
    decisions, by unfolding.
  `threeProtocolsWithFixedLinkAtFullSize_local`, `threeProtocolsWithFixedLinkAtFullSize_coherent`, `threeProtocolsWithFixedLinkAtFullSize_entryCoherent`: no premise.
  `wireOfFull .. P K depthReqT`: the wiring with K blocks for a round's verifier message: `wireF`,
    called, with the bodies `bodiesF`.
  `wiresOfFull`: the four laws of the wires (`Four`: what `CompilerSoundnessConditionStatements.wires`, Johnson/Top/
    InnerCompiledVerifier.lean, unfolds to), from tests on numbers, each with code: no round of the three files
    has more than K blocks (hk: `kThree`, OnBytes/Flat/WireBlocks.lean); in neither whole file a
    round has more than 64 bits of work (wK, wP: `WholeD.workFit`) or a tree deeper than 63 (dK, dP:
    `WholeD.depthFit`, OnBytes/Maker/WholeOf.lean).
  `wireOfFull_eq_sib`: the wiring is Johnson/Flat/WireAt.lean's own text at these letters, by
    unfolding. `wireFullK_eq_of`: A CONTROL: `wireFullK` is `wireOfFull` at the makers' own data and
    decisions.
  `depth_of_fit`: from `depthFit` to the form in which the bodies' law asks it.

Limits: those of the heads of Johnson/EntryRec/OkcFiles.lean, BodiesAt.lean and AtMakerA.lean, whose
terms are called here; among them: ONE LETTER salt SERVES THE BODIES OF THE FILES' OWN TREES, OF THE
ENTRY's AND OF THE STORED TABLES (`bodiesF .. salt`, `embStored a salt`, `prjStored a salt`); the
format has two numbers (a plan's, and a stored table's own), and nothing here ties the letter to
either. NOTHING ON THE SOUNDNESS OF THE KEY FILE's OR THE PROOF FILE's PROTOCOL: at two decisions
that say yes to everything all that stands here holds. That the data are those of any file, and that
the tests on numbers pass at any data, is not shown here (at the written lists of the makers' dry
runs: Johnson/G/DryKeyTests.lean and its neighbours). THE ROUNDS DRAW HASH
BLOCKS: a decision that follows a typed protocol must make what that protocol draws from the blocks,
and its rounds' errors must be shown against blocks. WHAT THE FRONT ROUND, THE JOINING ROUND AND THE
SEAM SEND IN THE CLEAR IS READ BY NO TEST OF THIS MAKE BUT `silK`, `silP`
(OnBytes/Flat/FilesAt.lean), which compare the answers (and, at the key file, the copy's number)
alone: the joining round's run's value and the seam's bytes are read by nothing, and runK, runP do
not see them. The entry file's decision is the verifier program's `linkVerify`: the entry's part
stays so here; a mend that takes that program's run and the typed numbers out of it is to come
behind. ON early, what the heads of
OnBytes/Flat/FilesAt.lean and Johnson/Flat/TwoSizes.lean say holds here: nothing comes late, so to
bind the reply is a load of the hypothesis on the proof file's soundness; at an early that drops
more than the decision compares with a message of the prover that hypothesis fails; at early := id
the reply would be hashed first, which is not the programs' form. THE WIRING IS OF OUR OWN CHOICE:
that programs are wired so is not shown. Its field K is K + 1. depthReqT is the depth of the request
tree of the key file's calls; that of the entry file's calls is laid as 0. NO LAW OF A WIRE SPEAKS
OF THESE TWO DEPTHS: the four laws hold at any two numbers. The key file's depth is paid elsewhere:
`CompilerSoundnessConditionStatements.keySound` (Johnson/Top/InnerCompiledVerifier.lean) counts the error of a shared round of the key file
2 ^ depthReqT times. At the makers' wiring that depth is laid as `G.k.oneTime.binding.logLeaves`
(`wireFullK_eq_of`), a number that the program's test on a key's public values admits only as 0
(`Key.fixedOk`, OnBytes/Key/Fixed.lean); nothing here uses that. With one K a round that needs fewer
blocks has a typed answer with blocks that it does not read. OF THE MAKERS' EIGHT TESTS on three
lists of rounds (`okAt`, OnBytes/Maker/Files.lean) two are asked here (`workFit`, `depthFit`); the
other six are asked by nothing here, and NOTHING FAILS CLOSED: where a test says no, no law is said.
NO TERM HERE HAS CODE BY THIS FILE's WORD: `filesAt`, `wireF` are noncomputable, and runK, runP are
any functions. THE FOUR CONTROLS (`threeProtocolsFromDryRunAtFullSize_eq_withFixedLink`, `wireFullK_eq_of` and the small twins) STAND AT
THE MAKERS' G: the dry runs' data and the verifier program's decisions. Nothing calls them; they
fall with `threeProtocolsFromDryRunAtFullSize`, `wireFullK`, and are to move into a file of their own. Nothing on an honest
prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.EntryRec.FilesLaws
import Johnson.EntryRec.AtConf
import Johnson.Flat.WireAt

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

/-- No tree deeper than 63: twice its number of leaves is at most 2 ^ 64. -/
theorem depth_of_fit {D : WholeD} (h : D.depthFit = true) :
    ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64 := by
  intro d hd s hs
  have h63 : s.a ≤ 63 := (WholeD.depthFit_iff D).1 h d hd s hs
  calc 2 ^ s.a + 2 ^ s.a = 2 ^ (s.a + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## The full size -/

/-- The entry file's part at the full size, with K blocks for a round's verifier message: the
linkProtocolWithWireOfRoundData (Johnson/Top/EntrySib.lean), called at the written link's letters. -/
def entryFullM (K salt : ℕ) : LinkProtocolWithLeafCodingAndQueryLayout RecFull frS.P.T.a 0 :=
  linkProtocolWithWireOfRoundData (ckP .two) dsFull frD.xs (fun rr => decFullX (recX rr)) salt 0 K (Nat.zero_le K)
    (chalP .two K)

/-- Its protocol, marks and two maps, taken at K := 0. That they are the same at every K is seen by
unfolding alone (`linkWireOK_sib` is spent so in `wiresOfFull`); no lemma states it. -/
@[reducible] def entryFullQ (salt : ℕ) : LinkProtocolWithLeafCoding RecFull frS.P.T.a := (entryFullM 0 salt).toLinkProtocolWithLeafCoding

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)

/-- **The three files' protocols at the full size, at any data of rounds and any two decisions**:
the filesAt, called. -/
@[reducible] def threeProtocolsWithFixedLinkAtFullSize : Files (DecR.configurationOfStoredTable A R) :=
  filesAt A R .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq) early none

/-- **The control: the makers' three files are of this make.** -/
theorem threeProtocolsFromDryRunAtFullSize_eq_withFixedLink (G : FilesParameters X RecFull) :
    threeProtocolsFromDryRunAtFullSize A R G = threeProtocolsWithFixedLinkAtFullSize A R (dataKFull G) (dataPFull G) (runKFull G) (runPFull G) G.rec₀
      G.z₀.2 G.depthReq G.early salt := rfl

/-- The three verifiers read their oracles at the declared positions alone. -/
theorem threeProtocolsWithFixedLinkAtFullSize_local :
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).key.IsLocal ∧
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).entry.IsLocal ∧
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).proof.IsLocal :=
  ⟨filesOf_keyLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entryFullQ salt) _
      early none,
    linkSibFull_local,
    filesOf_proofLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entryFullQ salt)
      _ early none⟩

/-- The two whole files' marks are coherent. -/
theorem threeProtocolsWithFixedLinkAtFullSize_coherent :
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT.Coherent ∧
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).ann.Coherent :=
  filesOf_coherent (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entryFullQ salt) _
    early none

/-- The entry file's marks are coherent. -/
theorem threeProtocolsWithFixedLinkAtFullSize_entryCoherent :
    (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

variable (P : (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).Provers)

/-- **The wiring, with K blocks for a round's verifier message**: the wireF, called, with
the bodies bodiesF. -/
def wireOfFull (K depthReqT : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).withProvers P)
            (List Bool)
            (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT
            (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annL) :=
  wireF .two K frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entryFullQ salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq) early none P)
    (entryFullM K salt).wL (List Bool) depthReq depthReqT 0
    (bodiesF .two frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entryFullQ salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq) early none P)
      salt (embStored frS.P.T.a salt) (prjStored frS.P.T.a salt))

/-- **The four laws of the wires**, from tests on numbers: no round of the three files has more than
K blocks (hk); in neither whole file a round has more than 64 bits of work (wK, wP) or a tree deeper
than 63 (dK, dP). -/
theorem wiresOfFull (K depthReqT : ℕ) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) :
    Four (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT) := by
  have h := nums_ofLib .two K frRds (fun d hd => (kThree_entry .two DK frRds DP d hd).trans hk)
    fr_wire_work fr_wire_own fr_wire_depth
  rw [← dsFull_eq] at h
  exact four_files .two K frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
    (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq) early none P)
    (entryFullM K salt).wL (List Bool) depthReq depthReqT 0 _
    (fun d hd => (kThree_key .two DK frRds DP d hd).trans hk) ((WholeD.workFit_iff DK).1 wK)
    (linkWireOK_sib .two frS.P.T.a dsFull frD.xs _ salt 0 K (Nat.zero_le _) h.1 h.2.1 h.2.2.1)
    (fun d hd => (kThree_proof .two DK frRds DP d hd).trans hk) ((WholeD.workFit_iff DP).1 wP) rfl
    (bodiesF_ok .two frS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entryFullQ salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq) early none P)
      salt (embStored frS.P.T.a salt) (prjStored frS.P.T.a salt)
      (prjStored_embStored frS.P.T.a salt) (depth_of_fit dK)
      (bodies_sib .two frS.P.T.a dsFull frD.xs _ salt 0 0 (Nat.zero_le 0) h.2.2.2)
      (depth_of_fit dP))

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restOfFull :=
  restSibFull A R (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt) P P.hL

/-- **The wiring in the text of Johnson/Flat/WireAt.lean** (`wireFullK`): `wireOf2` at the two whole
files' wire records, the written link's `wSib` and the bodies `bodiesSib`: by unfolding. -/
theorem wireOfFull_eq_sib (K depthReqT : ℕ) :
    wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT =
      wireOf2 (L := LrG (restOfFull A R DK DP runK runP rK rP depthReq early salt P))
        (aT := (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT)
        (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)) (K + 1)
        (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK)
        (wSib (restOfFull A R DK DP runK runP rK rP depthReq early salt P) K (chalP .two K))
        (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP)
        frS.P.T.a depthReq depthReqT 0
        (bodiesSib (restOfFull A R DK DP runK runP rK rP depthReq early salt P) salt
          (SCode.emb _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.emb _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))) := rfl

end

/-- **A control: the makers' wiring is of this make.** By `wireOfFull_eq_sib` at the makers' data:
asked by unfolding at once, Lean did not decide it within 4,000,000 heartbeats. -/
theorem wireFullK_eq_of {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A)
    (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers) (K salt : ℕ) :
    wireFullK A E G P K salt = wireOfFull A (relationsAndEncodingOfClaims A E) (dataKFull G) (dataPFull G) (runKFull G)
      (runPFull G) G.rec₀ G.z₀.2 G.depthReq G.early salt P K G.k.oneTime.binding.logLeaves :=
  (wireOfFull_eq_sib A (relationsAndEncodingOfClaims A E) (dataKFull G) (dataPFull G) (runKFull G) (runPFull G) G.rec₀
    G.z₀.2 G.depthReq G.early salt P K G.k.oneTime.binding.logLeaves).symm

/-! ## The small size -/

/-- The entry file's part at the small size, with K blocks for a round's verifier message: the
linkProtocolWithWireOfRoundData (Johnson/Top/EntrySib.lean), called at the written link's letters. -/
def entrySmallM (K salt : ℕ) : LinkProtocolWithLeafCodingAndQueryLayout RecSmall srS.P.T.a 0 :=
  linkProtocolWithWireOfRoundData (ckP .two) dsSmall srD.xs (fun rr => decSmallX (recX rr)) salt 0 K (Nat.zero_le K)
    (chalP .two K)

/-- Its protocol, marks and two maps, taken at K := 0. That they are the same at every K is seen by
unfolding alone (`linkWireOK_sib` is spent so in `wiresOfSmall`); no lemma states it. -/
@[reducible] def entrySmallQ (salt : ℕ) : LinkProtocolWithLeafCoding RecSmall srS.P.T.a := (entrySmallM 0 salt).toLinkProtocolWithLeafCoding

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)

/-- **The three files' protocols at the small size, at any data of rounds and any two decisions**:
the filesAt, called. -/
@[reducible] def threeProtocolsWithFixedLinkAtSmallSize : Files (DecR.configurationOfStoredTable A R) :=
  filesAt A R .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq) early none

/-- **The control: the makers' three files are of this make.** -/
theorem threeProtocolsFromDryRunAtSmallSize_eq_withFixedLink (G : FilesParameters X RecSmall) :
    threeProtocolsFromDryRunAtSmallSize A R G = threeProtocolsWithFixedLinkAtSmallSize A R (dataKSmall G) (dataPSmall G) (runKSmall G) (runPSmall G)
      G.rec₀ G.z₀.2 G.depthReq G.early salt := rfl

/-- The three verifiers read their oracles at the declared positions alone. -/
theorem threeProtocolsWithFixedLinkAtSmallSize_local :
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).key.IsLocal ∧
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).entry.IsLocal ∧
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).proof.IsLocal :=
  ⟨filesOf_keyLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQ salt) _
      early none,
    linkSibSmall_local,
    filesOf_proofLocal (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQ salt)
      _ early none⟩

/-- The two whole files' marks are coherent. -/
theorem threeProtocolsWithFixedLinkAtSmallSize_coherent :
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).annT.Coherent ∧
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).ann.Coherent :=
  filesOf_coherent (lettersAt A R) .two DK DP _ _ _ _ _ _ silK runK silP runP (entrySmallQ salt) _
    early none

/-- The entry file's marks are coherent. -/
theorem threeProtocolsWithFixedLinkAtSmallSize_entryCoherent :
    (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).annL.Coherent := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)).Coherent
  rw [_root_.Run.Twin.allLo_eq]
  exact Iop.BatchOne.BAnn.allLocal_coherent _

variable (P : (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).Provers)

/-- **The wiring, with K blocks for a round's verifier message**: the wireF, called, with
the bodies bodiesF. -/
def wireOfSmall (K depthReqT : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).withProvers P)
            (List Bool)
            (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).annT
            (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).annL) :=
  wireF .two K srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
    ByteArray.empty silK runK silP runP (entrySmallQ salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq) early none P)
    (entrySmallM K salt).wL (List Bool) depthReq depthReqT 0
    (bodiesF .two srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entrySmallQ salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq) early none P)
      salt (embStored srS.P.T.a salt) (prjStored srS.P.T.a salt))

/-- **The four laws of the wires**, from tests on numbers: no round of the three files has more than
K blocks (hk); in neither whole file a round has more than 64 bits of work (wK, wP) or a tree deeper
than 63 (dK, dP). -/
theorem wiresOfSmall (K depthReqT : ℕ) (hk : kThree .two DK srRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) :
    Four (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT) := by
  have h := nums_ofLib .two K srRds (fun d hd => (kThree_entry .two DK srRds DP d hd).trans hk)
    sr_wire_work sr_wire_own sr_wire_depth
  rw [← dsSmall_eq] at h
  exact four_files .two K srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
    (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt)
    (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq) early none P)
    (entrySmallM K salt).wL (List Bool) depthReq depthReqT 0 _
    (fun d hd => (kThree_key .two DK srRds DP d hd).trans hk) ((WholeD.workFit_iff DK).1 wK)
    (linkWireOK_sib .two srS.P.T.a dsSmall srD.xs _ salt 0 K (Nat.zero_le _) h.1 h.2.1 h.2.2.1)
    (fun d hd => (kThree_proof .two DK srRds DP d hd).trans hk) ((WholeD.workFit_iff DP).1 wP) rfl
    (bodiesF_ok .two srS.P.T.a DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP runP (entrySmallQ salt)
      (lettersOf (lettersAt A R) .two DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq) early none P)
      salt (embStored srS.P.T.a salt) (prjStored srS.P.T.a salt)
      (prjStored_embStored srS.P.T.a salt) (depth_of_fit dK)
      (bodies_sib .two srS.P.T.a dsSmall srD.xs _ salt 0 0 (Nat.zero_le 0) h.2.2.2)
      (depth_of_fit dP))

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restOfSmall :=
  restSibSmall A R (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt) P P.hL

/-- **The wiring in the text of Johnson/Flat/WireAt.lean** (`wireSmallK`): `wireOf2` at the two
whole files' wire records, the written link's `wSib` and the bodies `bodiesSib`: by unfolding. -/
theorem wireOfSmall_eq_sib (K depthReqT : ℕ) :
    wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT =
      wireOf2 (L := LrG (restOfSmall A R DK DP runK runP rK rP depthReq early salt P))
        (aT := (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).annT)
        (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)) (K + 1)
        (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK)
        (wSib (restOfSmall A R DK DP runK runP rK rP depthReq early salt P) K (chalP .two K))
        (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP)
        srS.P.T.a depthReq depthReqT 0
        (bodiesSib (restOfSmall A R DK DP runK runP rK rP depthReq early salt P) salt
          (SCode.emb _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
            ByteArray.empty))
          (SCode.emb _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))
          (SCode.prj _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty))) := rfl

end

/-- **A control: the makers' wiring is of this make.** By `wireOfSmall_eq_sib` at the makers' data,
as at the full size. -/
theorem wireSmallK_eq_of {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A)
    (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers) (K salt : ℕ) :
    wireSmallK A E G P K salt = wireOfSmall A (relationsAndEncodingOfClaims A E) (dataKSmall G) (dataPSmall G)
      (runKSmall G) (runPSmall G) G.rec₀ G.z₀.2 G.depthReq G.early salt P K
      G.k.oneTime.binding.logLeaves :=
  (wireOfSmall_eq_sib A (relationsAndEncodingOfClaims A E) (dataKSmall G) (dataPSmall G) (runKSmall G) (runPSmall G)
    G.rec₀ G.z₀.2 G.depthReq G.early salt P K G.k.oneTime.binding.logLeaves).symm

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.threeProtocolsFromDryRunAtFullSize_eq_withFixedLink
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtFullSize_local
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtFullSize_coherent
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtFullSize_entryCoherent
#print axioms VerifiableInference.OnPublicFiles.wiresOfFull
#print axioms VerifiableInference.OnPublicFiles.wireOfFull_eq_sib
#print axioms VerifiableInference.OnPublicFiles.wireFullK_eq_of
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsFromDryRunAtSmallSize_eq_withFixedLink
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtSmallSize_local
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtSmallSize_coherent
#print axioms VerifiableInference.OnPublicFiles.threeProtocolsWithFixedLinkAtSmallSize_entryCoherent
#print axioms VerifiableInference.OnPublicFiles.wiresOfSmall
#print axioms VerifiableInference.OnPublicFiles.wireOfSmall_eq_sib
#print axioms VerifiableInference.OnPublicFiles.wireSmallK_eq_of

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WireAt.lean: the wiring of the three files' protocols at the two sizes of the default
setting (OnBytes/Flat/FilesAt.lean), written whole, and the laws of the wires at it.

Definitions, statements and their proofs. A wiring says how a hash function's answers are read as a
round's verifier message, where a symbol lies in a hash tree, and how a symbol is written into the
body of a leaf. The compiler's theorems ask four laws of it: of the whole, and of its parts for the
key file, the entry file and the proof file (`CompilerSoundnessConditionStatements.wires`, Johnson/Top/InnerCompiledVerifier.lean). Here the
two whole files' wire records are the makers' own (`wqWhole`, OnBytes/Maker/Wire.lean) at the
makers' own data of the rounds; the entry file's is `wSib` (Johnson/EntryRec/OklaSib.lean): the
written link's own; the body of a leaf is the leaf's own string of bits (`bodiesSib`, the same file;
`scWhole`, OnBytes/Flat/LeafBodies.lean).

Main names:
  `wires_of`: the four laws at `wireOf2` (Johnson/EntryRec/WiringOfTypedOracleCarrier.lean), for every object, from
    the three wire records' laws.
  `dataKFull`, `dataPFull`, `runKFull`, `runPFull`: the makers' own data and decisions. The small
    size alike.
  `KFullAt`, `KSmallAt`: ONE number of blocks for all three files: the greatest that a round of the
    three asks (`kThree`, OnBytes/Flat/WireBlocks.lean), at least the entry's description's own
    (`frD.K`, `srD.K`: `entryK_le_KFullAt`, `entryK_le_KSmallAt`), and enough for the record's seed:
    a maximum; no number is evaluated.
  `GuardsPassFull G`, `GuardsPassSmall G`: the makers' tests on the dry runs pass (`okAt`, the very
    test on which `dataAt` branches). Named. No proof of a clause on soundness draws on them:
    `soundThreeFull_guarded` (Johnson/Flat/ThreeAtFiles.lean) asks a test that
    decides the full one and states it beside its clause on soundness, whose proof does not use it.
    `dataKFull_empty`, `dataPFull_empty`, `runKFull_false`, `runPFull_false` and the small twins:
    where a test fails, that file's decision says no at every instance and all views, and its data
    are those of three empty lists. THE FOUR LEMMAS `run.._false` ARE CALLED BY NO FILE OF THIS
    LIBRARY: that the decision says no where a test fails is stated here and carried into no
    theorem. The four `data.._empty` are used in Johnson/Flat/BlocksAt.lean
    alone.
  `objFullAt`, `objSmallAt`: the object of the three files is `LrG` (Johnson/EntryRec/Defs.lean) at
    `restSibFull` | `restSibSmall` (Johnson/Flat/RestSib.lean), by unfolding. It says little: that
    rest is read off the files' own object, field by field, and its link is the files' entry.
  `wireFullK`, `wireSmallK`: the wiring in which K blocks give a round's verifier message; its own
    field `K` is K + 1 (one block more for the test bits of the work). `wiresFullK`, `wiresSmallK`:
    the four laws at it, at every K that is at least `kThree`. Beyond `wireFullAt` | `wiresFullAt`
    and the small twins below, no file calls `wiresFullK`, `wiresSmallK`.
  `wireFullAt`, `wireSmallAt`: the wiring: that at `KFullAt G` | `KSmallAt G`. Letter: the length of
    a salt. The depth of the request tree of the key file's calls is the depth of the binding tree
    in the key's chains' parameters (`G.k.oneTime.binding.logLeaves`); that of the entry file's
    calls is 0: one leaf; that of the proof file's is `G.depthReq` (`wireFullAt_depths`,
    `wireSmallAt_depths`).
  `wiresFullAt`, `wiresSmallAt`: the four laws at it, under no premise: of a wiring of our own
    choice; they hold also where a guard fails and the verifier accepts nothing. `seedKFull`,
    `seedKSmall`.

What gives what: blocks: `kThree_key`, `kThree_entry`, `kThree_proof`, then the premise `kThree ≤ K`
(at `KFullAt G`: `le_max_left`); work and depth of the two whole files: `dataAt_work`,
`dataAt_depth` (OnBytes/Maker/Files.lean); work, own trees' numbers and depth of the entry:
OnBytes/Slice/EntryWireNums.lean, EntryWireDepth.lean, carried to the written link's rounds' data by
`nums_ofLib` (Johnson/EntryRec/OklaSib.lean); the bodies: `scWhole_ok`, `StringsList.prjT_embT`,
`bodyS`'s own law; the number of slots is 2 ^ `G.depthReq` by `threeProtocolsFromDryRunAtFullSize`'s text.

Limits: THE DATA FAIL CLOSED: where a test on the dry runs fails, that file's data are those of
three empty lists, and the four laws hold of a verifier that accepts nothing: THAT THE TESTS PASS at
any value of G (`GuardsPassFull`, `GuardsPassSmall`) is not shown here. THE WIRING IS OF OUR OWN
CHOICE: that programs are wired so (this K, these depths, these wire records, these bodies), and
that a leaf's body in a file of a program is the string that is written here, are facts about the
programs, which are not shown here. NO LAW OF A WIRE SPEAKS OF THE TWO DEPTHS of the key file's and
the entry file's request trees (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean, at the fields): the four laws hold
at any two numbers. The key file's depth is paid elsewhere: `CompilerSoundnessConditionStatements.keySound`
(Johnson/Top/InnerCompiledVerifier.lean) counts the error of a shared round of the key file 2 ^
`G.k.oneTime.binding.logLeaves` times. The program's test on a key's public values admits that
number only as 0 (`Key.fixedOk`, OnBytes/Key/Fixed.lean); nothing here uses that. With one K a round
that needs fewer blocks has a typed answer with blocks that it does not read. "Every round's
verifier message is exactly uniform" is met because the rounds draw hash blocks: every round's error
must then be shown against blocks.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.FilesAt
import OnBytes.Flat.RecordSeed
import Johnson.Flat.RestSib
import Johnson.EntryRec.OklaSib
import Johnson.EntryRec.BodiesAt
import OnBytes.Slice.EntryWireNums
import OnBytes.Slice.EntryWireDepth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The four clauses at a wiring made of three wire records. -/
theorem wires_of {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} {K : ℕ} {wT : ProtocolQueryLayout lam K (batTC L aT)}
    {wL : ProtocolQueryLayout lam K (batLC L aL)} {wB : ProtocolQueryLayout lam K L.onlineBatch}
    {depth depthReq depthReqT depthReqL : ℕ} {b : Bodies L Bd} (hT : wT.OKG) (hL : wL.OKG)
    (hB : wB.OKG) (fits : L.wordLength ≤ 2 ^ depth) (slots : L.maxBatchSize = 2 ^ depthReq)
    (extDepth : wT.ext.depth = depth ∧ wL.ext.depth = depth ∧ wB.ext.depth = depth)
    (depthT : depth ≤ wT.maxDepth) (depthL : depth ≤ wL.maxDepth) (depthB : depth ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val)
    (extL : (∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val) ∧
      (∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val))
    (hb : b.OK) :
    (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b).OKG ∧
      (wTC (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b)).OKG ∧
      (wLC (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b)).OKG ∧
      (wBC (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b)).OKG :=
  ⟨{ T := ⟨hT.sh, hT.ext, fun _ _ _ => Nat.zero_le _, hT.depth⟩
     Lk := ⟨hL.sh, hL.ext, fun _ _ _ => Nat.zero_le _, hL.depth⟩
     B := ⟨hB.sh, hB.ext, fun _ _ _ => Nat.zero_le _, hB.depth⟩
     fits := fits
     slots := slots
     extDepth := extDepth
     depthT := depthT
     depthL := depthL
     depthB := depthB
     extT := extT
     extB := extB
     extL := extL
     prjE_emb := hb.E
     prjT_emb := hb.T
     prjL_emb := hb.L
     prjB_emb := hb.B }, hT, hL, hB⟩


/-! ## The full-size files -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The data of the key file's rounds: the makers' own. -/
def dataKFull : WholeD :=
  WholeD.of frS.P.T.a (dataAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)))

/-- The data of the proof file's rounds: the makers' own. -/
def dataPFull : WholeD :=
  WholeD.of frS.P.T.a
    (dataAt frS.P.T.a (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)))

/-- **The makers' tests on the dry runs pass**, at the key file's and at the proof file's data.
Named. No proof of a clause on soundness in this library draws on it: `soundThreeFull_guarded`
(Johnson/Flat/ThreeAtFiles.lean) asks a test that decides it and states it
beside its clause on soundness, whose proof does not use it. Where one of the two fails, that file's
data are those of three empty lists, and its decision says no at every record and all views (the
lemmas below). -/
def GuardsPassFull : Prop :=
  okAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true ∧
    okAt frS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true

/-- Where the key file's test fails, its data are those of three empty lists. -/
theorem dataKFull_empty
    (h : ¬ okAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true) :
    dataKFull G = WholeD.of frS.P.T.a (OnBytes.Three.Whole.of [] [] []) := by
  unfold dataKFull dataAt
  rw [if_neg h]

/-- Where the proof file's test fails, its data are those of three empty lists. -/
theorem dataPFull_empty
    (h : ¬ okAt frS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true) :
    dataPFull G = WholeD.of frS.P.T.a (OnBytes.Three.Whole.of [] [] []) := by
  unfold dataPFull dataAt
  rw [if_neg h]

/-- The key file's decision: the makers' own. -/
def runKFull (rec : RecFull) (v₁ v₂ v₃ : PQ.View) : Bool :=
  okAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) &&
    decideKey G.k (keyOf (fun β : NZ => β.val) rec)
      (dataAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))).t₁
      (dataAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))).t₂ v₁ v₂ v₃

/-- The proof file's decision: the makers' own. -/
def runPFull (z : X × RecFull) (v₁ v₂ v₃ : PQ.View) : Bool :=
  okAt frS.P.T.a (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) &&
    decideProof G.c (keyOf (fun β : NZ => β.val) z.2) (G.block z.1)
      (dataAt frS.P.T.a
        (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1))).t₁
      (dataAt frS.P.T.a
        (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1))).t₂ v₁ v₂ v₃

/-- Where the key file's test fails, its decision says no, whatever the record and the views. -/
theorem runKFull_false
    (h : ¬ okAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true)
    (rec : RecFull) (v₁ v₂ v₃ : PQ.View) : runKFull G rec v₁ v₂ v₃ = false := by
  unfold runKFull
  rw [Bool.eq_false_iff.2 h, Bool.false_and]

/-- Where the proof file's test fails, its decision says no, whatever the instance, the record and
the views. -/
theorem runPFull_false
    (h : ¬ okAt frS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true)
    (z : X × RecFull) (v₁ v₂ v₃ : PQ.View) : runPFull G z v₁ v₂ v₃ = false := by
  unfold runPFull
  rw [Bool.eq_false_iff.2 h, Bool.false_and]

/-- The number of blocks but one of the one wiring: the greatest that a round of the three files
asks, at least the entry's description's own number, and enough for the record's seed. -/
def KFullAt : ℕ :=
  max (kThree .two (dataKFull G) frRds (dataPFull G)) (max frD.K (seedBS recLg recS).b)

/-- It is at least the entry's description's own number of blocks. -/
theorem entryK_le_KFullAt : frD.K ≤ KFullAt G :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restFullAt : RestR A.Mat X
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Ans frS.P.T.a linkSibFull :=
  restSibFull A (relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P P.hL

/-- **The object of the three files is `LrG` at `restSibFull`** (Johnson/Flat/RestSib.lean), by
unfolding; the link's honest prover is the provers' own. -/
theorem objFullAt : LrG (restFullAt A E G P) = (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P := rfl

/-- **The wiring at this size, with K blocks for a round's verifier message** (its field `K` is
K + 1): the three files' own wire records; a body is the leaf's own string of bits; the depth of the
request tree of the key file's calls is the key's chains' own (`G.k.oneTime.binding.logLeaves`),
that of the entry file's calls is 0 (one leaf). Letters: K; the length of a salt. -/
def wireFullK (K salt : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireOf2 (L := LrG (restFullAt A E G P)) (aT := (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT)
    (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)) (K + 1)
    (wqWhole (ckP .two) K (chalP .two K) ((dataKFull G).at frS.P.T.a)
      (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK (runKFull G))
    (wSib (restFullAt A E G P) K (chalP .two K))
    (wqWhole (ckP .two) K (chalP .two K) ((dataPFull G).at frS.P.T.a)
      (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP (runPFull G))
    frS.P.T.a G.depthReq G.k.oneTime.binding.logLeaves 0
    (bodiesSib (restFullAt A E G P) salt
      (SCode.emb _ (scWhole salt (ckP .two) ((dataKFull G).at frS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty))
      (SCode.prj _ (scWhole salt (ckP .two) ((dataKFull G).at frS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty))
      (SCode.emb _ (scWhole salt (ckP .two) ((dataPFull G).at frS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty))
      (SCode.prj _ (scWhole salt (ckP .two) ((dataPFull G).at frS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty)))

/-- **The four clauses at it**, at every K that is at least the greatest number of blocks that a
round of the three files asks. -/
theorem wiresFullK (K : ℕ)
    (hK : kThree .two (dataKFull G) frRds (dataPFull G) ≤ K) (salt : ℕ) :
    (wireFullK A E G P K salt).OKG ∧ (wTC (wireFullK A E G P K salt)).OKG ∧
      (wLC (wireFullK A E G P K salt)).OKG ∧ (wBC (wireFullK A E G P K salt)).OKG := by
  have h := nums_ofLib .two K frRds
    (fun d hd => (kThree_entry .two (dataKFull G) frRds (dataPFull G) d hd).trans hK)
    fr_wire_work fr_wire_own fr_wire_depth
  rw [← dsFull_eq] at h
  exact wires_of
    (wqWhole_okg_ckP .two K ((dataKFull G).at frS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
      ByteArray.empty silK (runKFull G)
      (fun d hd => (kThree_key .two (dataKFull G) frRds (dataPFull G) d hd).trans hK)
      (dataAt_work frS.P.T.a _))
    (wSib_okg (restFullAt A E G P) K (chalP .two K) (fun _ => true) h.2.2.1
      (TypedOracleCompiler.Run.planPull_okg .two K dsFull (fun _ => true) h.1 h.2.1))
    (wqWhole_okg_ckP .two K ((dataPFull G).at frS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
      ByteArray.empty silP (runPFull G)
      (fun d hd => (kThree_proof .two (dataKFull G) frRds (dataPFull G) d hd).trans hK)
      (dataAt_work frS.P.T.a _))
    (le_refl _) rfl ⟨rfl, rfl, rfl⟩ (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
    ⟨(TypedOracleCompiler.Run.PQ.bodyS frS.P.T.a salt).get_e,
      SCode.prj_emb _ _ (scWhole_ok salt (ckP .two) ((dataKFull G).at frS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty (dataAt_depth frS.P.T.a _)),
      TypedOracleCompiler.StringsList.prjT_embT salt (ckP .two) dsFull h.2.2.2,
      SCode.prj_emb _ _ (scWhole_ok salt (ckP .two) ((dataPFull G).at frS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty (dataAt_depth frS.P.T.a _))⟩

/-- **The wiring at this size, written**: at `KFullAt G`. Letter: the length of a salt. -/
def wireFullAt (salt : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireFullK A E G P (KFullAt G) salt

/-- **The four clauses at the written wiring**: no premise. -/
theorem wiresFullAt (salt : ℕ) :
    (wireFullAt A E G P salt).OKG ∧ (wTC (wireFullAt A E G P salt)).OKG ∧
      (wLC (wireFullAt A E G P salt)).OKG ∧ (wBC (wireFullAt A E G P salt)).OKG :=
  wiresFullK A E G P (KFullAt G) (le_max_left _ _) salt

/-- The three depths of its request trees. -/
theorem wireFullAt_depths (salt : ℕ) :
    (wireFullAt A E G P salt).depthReq = G.depthReq ∧
      (wireFullAt A E G P salt).depthReqT = G.k.oneTime.binding.logLeaves ∧
      (wireFullAt A E G P salt).depthReqL = 0 := ⟨rfl, rfl, rfl⟩

/-- The wiring has blocks enough for the record's seed. -/
theorem seedKFull (salt : ℕ) : (seedBS recLg recS).b ≤ (wireFullAt A E G P salt).K :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_succ (KFullAt G))

end

/-! ## The small files -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The data of the key file's rounds: the makers' own. -/
def dataKSmall : WholeD :=
  WholeD.of srS.P.T.a (dataAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)))

/-- The data of the proof file's rounds: the makers' own. -/
def dataPSmall : WholeD :=
  WholeD.of srS.P.T.a
    (dataAt srS.P.T.a (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)))

/-- **The makers' tests on the dry runs pass**, at the key file's and at the proof file's data.
Named; no theorem of this library on soundness names it. Where one of the two fails, that file's
data are those of three empty lists, and its decision says no at every record and all views (the
lemmas below). -/
def GuardsPassSmall : Prop :=
  okAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true ∧
    okAt srS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true

/-- Where the key file's test fails, its data are those of three empty lists. -/
theorem dataKSmall_empty
    (h : ¬ okAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true) :
    dataKSmall G = WholeD.of srS.P.T.a (OnBytes.Three.Whole.of [] [] []) := by
  unfold dataKSmall dataAt
  rw [if_neg h]

/-- Where the proof file's test fails, its data are those of three empty lists. -/
theorem dataPSmall_empty
    (h : ¬ okAt srS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true) :
    dataPSmall G = WholeD.of srS.P.T.a (OnBytes.Three.Whole.of [] [] []) := by
  unfold dataPSmall dataAt
  rw [if_neg h]

/-- The key file's decision: the makers' own. -/
def runKSmall (rec : RecSmall) (v₁ v₂ v₃ : PQ.View) : Bool :=
  okAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) &&
    decideKey G.k (keyOf (fun β : NZ => β.val) rec)
      (dataAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))).t₁
      (dataAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))).t₂ v₁ v₂ v₃

/-- The proof file's decision: the makers' own. -/
def runPSmall (z : X × RecSmall) (v₁ v₂ v₃ : PQ.View) : Bool :=
  okAt srS.P.T.a (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) &&
    decideProof G.c (keyOf (fun β : NZ => β.val) z.2) (G.block z.1)
      (dataAt srS.P.T.a
        (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1))).t₁
      (dataAt srS.P.T.a
        (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1))).t₂ v₁ v₂ v₃

/-- Where the key file's test fails, its decision says no, whatever the record and the views. -/
theorem runKSmall_false
    (h : ¬ okAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true)
    (rec : RecSmall) (v₁ v₂ v₃ : PQ.View) : runKSmall G rec v₁ v₂ v₃ = false := by
  unfold runKSmall
  rw [Bool.eq_false_iff.2 h, Bool.false_and]

/-- Where the proof file's test fails, its decision says no, whatever the instance, the record and
the views. -/
theorem runPSmall_false
    (h : ¬ okAt srS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true)
    (z : X × RecSmall) (v₁ v₂ v₃ : PQ.View) : runPSmall G z v₁ v₂ v₃ = false := by
  unfold runPSmall
  rw [Bool.eq_false_iff.2 h, Bool.false_and]

/-- The number of blocks but one of the one wiring: the greatest that a round of the three files
asks, at least the entry's description's own number, and enough for the record's seed. -/
def KSmallAt : ℕ :=
  max (kThree .two (dataKSmall G) srRds (dataPSmall G)) (max srD.K (seedBS 19 1).b)

/-- It is at least the entry's description's own number of blocks. -/
theorem entryK_le_KSmallAt : srD.K ≤ KSmallAt G :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- What the object holds beside its word length, its symbols and its link. -/
abbrev restSmallAt : RestR A.Mat X
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Ans srS.P.T.a linkSibSmall :=
  restSibSmall A (relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P P.hL

/-- **The object of the three files is `LrG` at `restSibSmall`** (Johnson/Flat/RestSib.lean), by
unfolding; the link's honest prover is the provers' own. -/
theorem objSmallAt : LrG (restSmallAt A E G P) = (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P := rfl

/-- **The wiring at this size, with K blocks for a round's verifier message** (its field `K` is
K + 1): the three files' own wire records; a body is the leaf's own string of bits; the depth of the
request tree of the key file's calls is the key's chains' own (`G.k.oneTime.binding.logLeaves`),
that of the entry file's calls is 0 (one leaf). Letters: K; the length of a salt. -/
def wireSmallK (K salt : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireOf2 (L := LrG (restSmallAt A E G P)) (aT := (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT)
    (aL := _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)) (K + 1)
    (wqWhole (ckP .two) K (chalP .two K) ((dataKSmall G).at srS.P.T.a)
      (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK (runKSmall G))
    (wSib (restSmallAt A E G P) K (chalP .two K))
    (wqWhole (ckP .two) K (chalP .two K) ((dataPSmall G).at srS.P.T.a)
      (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty silP (runPSmall G))
    srS.P.T.a G.depthReq G.k.oneTime.binding.logLeaves 0
    (bodiesSib (restSmallAt A E G P) salt
      (SCode.emb _ (scWhole salt (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty))
      (SCode.prj _ (scWhole salt (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty))
      (SCode.emb _ (scWhole salt (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty))
      (SCode.prj _ (scWhole salt (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty)))

/-- **The four clauses at it**, at every K that is at least the greatest number of blocks that a
round of the three files asks. -/
theorem wiresSmallK (K : ℕ)
    (hK : kThree .two (dataKSmall G) srRds (dataPSmall G) ≤ K) (salt : ℕ) :
    (wireSmallK A E G P K salt).OKG ∧ (wTC (wireSmallK A E G P K salt)).OKG ∧
      (wLC (wireSmallK A E G P K salt)).OKG ∧ (wBC (wireSmallK A E G P K salt)).OKG := by
  have h := nums_ofLib .two K srRds
    (fun d hd => (kThree_entry .two (dataKSmall G) srRds (dataPSmall G) d hd).trans hK)
    sr_wire_work sr_wire_own sr_wire_depth
  rw [← dsSmall_eq] at h
  exact wires_of
    (wqWhole_okg_ckP .two K ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
      ByteArray.empty silK (runKSmall G)
      (fun d hd => (kThree_key .two (dataKSmall G) srRds (dataPSmall G) d hd).trans hK)
      (dataAt_work srS.P.T.a _))
    (wSib_okg (restSmallAt A E G P) K (chalP .two K) (fun _ => true) h.2.2.1
      (TypedOracleCompiler.Run.planPull_okg .two K dsSmall (fun _ => true) h.1 h.2.1))
    (wqWhole_okg_ckP .two K ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
      ByteArray.empty silP (runPSmall G)
      (fun d hd => (kThree_proof .two (dataKSmall G) srRds (dataPSmall G) d hd).trans hK)
      (dataAt_work srS.P.T.a _))
    (le_refl _) rfl ⟨rfl, rfl, rfl⟩ (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
    ⟨(TypedOracleCompiler.Run.PQ.bodyS srS.P.T.a salt).get_e,
      SCode.prj_emb _ _ (scWhole_ok salt (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀)
        (join₀ G.rec₀) ByteArray.empty (dataAt_depth srS.P.T.a _)),
      TypedOracleCompiler.StringsList.prjT_embT salt (ckP .two) dsSmall h.2.2.2,
      SCode.prj_emb _ _ (scWhole_ok salt (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2)
        (join₀ G.z₀.2) ByteArray.empty (dataAt_depth srS.P.T.a _))⟩

/-- **The wiring at this size, written**: at `KSmallAt G`. Letter: the length of a salt. -/
def wireSmallAt (salt : ℕ) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireSmallK A E G P (KSmallAt G) salt

/-- **The four clauses at the written wiring**: no premise. -/
theorem wiresSmallAt (salt : ℕ) :
    (wireSmallAt A E G P salt).OKG ∧ (wTC (wireSmallAt A E G P salt)).OKG ∧
      (wLC (wireSmallAt A E G P salt)).OKG ∧ (wBC (wireSmallAt A E G P salt)).OKG :=
  wiresSmallK A E G P (KSmallAt G) (le_max_left _ _) salt

/-- The three depths of its request trees. -/
theorem wireSmallAt_depths (salt : ℕ) :
    (wireSmallAt A E G P salt).depthReq = G.depthReq ∧
      (wireSmallAt A E G P salt).depthReqT = G.k.oneTime.binding.logLeaves ∧
      (wireSmallAt A E G P salt).depthReqL = 0 := ⟨rfl, rfl, rfl⟩

/-- The wiring has blocks enough for the record's seed. -/
theorem seedKSmall (salt : ℕ) : (seedBS 19 1).b ≤ (wireSmallAt A E G P salt).K :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_succ (KSmallAt G))

end

end VerifiableInference.OnPublicFiles

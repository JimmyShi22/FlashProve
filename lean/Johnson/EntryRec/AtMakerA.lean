-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/AtMakerA.lean: the laws of the wires without the record's wire: the four clauses
that `OKC` (Johnson/TypedOracleCompiler/RecCompile/Cms.lean) and `OKA` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean: the
compiled verifier with the answers alone in the lists) have in common; the wiring at the two makers'
values and an entry's part; and `OKA` at it.

  `Four W`: the laws of the whole wiring W and of its three wire records at the object's own
    protocols.
  `four_wireOf2`: `Four` at `wireOf2` (Johnson/EntryRec/WiringOfTypedOracleCarrier.lean), for every object with
    records, type of bodies and two annotations: from the three wire records' laws, the clauses on
    numbers and places that `QueryLayout.OKG` asks, and `Bodies.OK`.
  `four_files`: `Four` where `okc_files` has `OKC`, from the same hypotheses but the one on the
    record's code.
  `oka_of_four`: `OKA W cA` from `Four W` and the laws of the answers' code.
  `wireM`: the wiring of `(filesM ..).withProvers P`: `wireF` at the entry's part's number of blocks and
    wire record, the bodies `bodiesF` with OnBytes/Flat/StoredBodies.lean's `embStored` and
    `prjStored` for a stored table's symbols.
  `four_atMakers`: `Four (wireM ..)`, from `LinkWireOK` at the entry's part (`hL`), that its two
    maps read back what they write (`hLb`), and that the number of slots is 2 ^ depthReq (`slots`).
    What `four_files` asks of the two whole files holds of the makers' data by `kM_key`, `kM_proof`,
    `dataAt_work` and `dataAt_depth`.
  `OkAts`: the tests on the data of the key file and of the proof file pass.
  `oka_atMakers`: under `OkAts`: `OKA` at `wireM`, and the data at which the two whole files'
    protocols stand are those of the rounds that the dry runs state. Its other hypotheses: `hL`,
    `hLb`, `slots` as in `four_atMakers`; the laws of the answers' code (`hA`).

Why `OkAts` is named. Where a test fails the makers' data are those of three empty lists: `Four`
holds there too, of protocols that accept nothing (OnBytes/Maker/Files.lean's `keyIOR_guard`,
`proofIOR_guard`). `four_atMakers` holds without `OkAts`; a sentence "at the real files" needs it.

Limits: those of Johnson/EntryRec/OkcFiles.lean's and BodiesAt.lean's heads. That `OkAts` holds at
any parameters is not shown here. THAT `hL` AND `hLb` ARE MET BY ANY ENTRY's PART IS NOT SHOWN HERE.
That `AnsOK` (`hA`) is met by any code of this object's answers is not shown here; it cannot be met
where the answers are infinitely many. One letter `salt` serves the bodies of the files' own trees
and of the stored tables; the format has two numbers (a plan's, and a stored table's own), and
nothing here ties the letter to either. The depths `depthReqT`, `depthReqL` of the request trees of
Test and Link are free letters. `wireM` is a wiring of our choice: that the programs are wired so is
not a statement of Lean.


-/
import Johnson.EntryRec.AtMakerB
import Johnson.TypedOracleCompiler.RecCompile.CmsAns

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The laws of a wiring and of its three wire records at the object's own protocols. -/
def Four (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Prop :=
  W.OKG ∧ (wTC W).OKG ∧ (wLC W).OKG ∧ (wBC W).OKG

/-- **The four clauses, at three wire records laid as one wiring.** -/
theorem four_wireOf2 {K : ℕ} {wT : ProtocolQueryLayout lam K (batTC L aT)} {wL : ProtocolQueryLayout lam K (batLC L aL)}
    {wB : ProtocolQueryLayout lam K L.onlineBatch} {depth depthReq depthReqT depthReqL : ℕ} {b : Bodies L Bd}
    (hT : wT.OKG) (hL : wL.OKG) (hB : wB.OKG)
    (fits : L.wordLength ≤ 2 ^ depth) (slots : L.maxBatchSize = 2 ^ depthReq)
    (extDepth : wT.ext.depth = depth ∧ wL.ext.depth = depth ∧ wB.ext.depth = depth)
    (depthT : depth ≤ wT.maxDepth) (depthL : depth ≤ wL.maxDepth) (depthB : depth ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val)
    (extL : (∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val) ∧
      (∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val))
    (hb : b.OK) :
    Four (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b) :=
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

/-- The laws that the verifier with the answers alone asks. -/
theorem oka_of_four {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    (h : Four W) (hA : AnsOK cA) : OKA W cA :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hA⟩

end TypedOracleCompiler.Compile.Batch.Cms

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Hiop Compile OnBytes.Maker OnBytes.Flat OnBytes.Slice
open TypedOracleCompiler.Compile.Batch.Cms (Bodies Four four_wireOf2 oka_of_four)

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))

/-- **The four clauses at the three files.** -/
theorem four_files (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
    (b : Bodies (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd)
    (bK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.entry.work ≤ 64)
    (hL : LinkWireOK K a eL wL)
    (bP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.entry.work ≤ 64)
    (slots : Z.N = 2 ^ depthReq) (hb : b.OK) :
    Four (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b) :=
  four_wireOf2
    (wqWhole_okg_ckP f K (DK.at a) tFk tJk t3k silK runK bK wK) hL.okg
    (wqWhole_okg_ckP f K (DP.at a) tFp tJp t3p silP runP bP wP)
    (le_refl _) slots ⟨rfl, hL.depth, rfl⟩ (le_max_left _ _) hL.deep (le_max_left _ _)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) ⟨hL.first, hL.second⟩ hb

end

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (key : Kc.conf.Rec → TableKey)
  (k : OnBytes.Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : OnBytes.Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec)
  (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a (kM Kc f key k rec₀ c block z₀)) (N : ℕ)
  (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).Provers)

/-- **The wiring of the three files at the two makers' values and an entry's part.** -/
noncomputable def wireM (salt depthReq depthReqT depthReqL : ℕ) :
    TypedOracleCompiler.Iop.QueryLayout 256
      (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
        ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).withProvers P)
          (List Bool)
        (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annT
        (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annL)
          :=
  wireF f p.K a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
    (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) p.wL (List Bool)
      depthReq depthReqT depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) salt (embStored
      a salt) (prjStored a salt))

/-- **The four clauses at the object of the three files.** -/
theorem four_atMakers (salt depthReq depthReqT depthReqL : ℕ)
    (hL : LinkWireOK p.K a p.toLinkProtocolWithLeafCoding p.wL)
    (hLb : ∀ q s, p.prjL q (p.embL q s) = some s) (slots : N = 2 ^ depthReq) :
    Four (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P salt
      depthReq depthReqT depthReqL) :=
  four_files f p.K a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
    (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) p.wL (List Bool)
      depthReq depthReqT depthReqL _
    (kM_key Kc f key k rec₀ c block z₀ p) (dataAt_work a _) hL
    (kM_proof Kc f key k rec₀ c block z₀ p) (dataAt_work a _) slots
    (bodiesF_ok f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) salt (embStored
      a salt) (prjStored a salt) (prjStored_embStored a salt)
      (dataAt_depth a _) hLb (dataAt_depth a _))

/-- **The tests on the data of the key file and of the proof file pass.** -/
structure OkAts : Prop where
  okK : okAt a (dryKey k (key rec₀)) = true
  okP : okAt a (dryProof c (key z₀.2) (block z₀.1)) = true

/-- **The laws that the verifier with the answers alone asks, at the two makers' values, where the
tests on the data pass**; and there the data are those of the rounds that the dry runs state. Asked
beside: `hL`, `hLb`, `slots`, and the laws of the answers' code (`hA`). -/
theorem oka_atMakers (hok : OkAts Kc key k rec₀ c block z₀) (salt depthReq depthReqT depthReqL : ℕ)
    (cA : ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).withProvers
      P).OutOfDomainAnswer → List (Dig 256))
    (hL : LinkWireOK p.K a p.toLinkProtocolWithLeafCoding p.wL)
    (hLb : ∀ q s, p.prjL q (p.embL q s) = some s) (slots : N = 2 ^ depthReq)
    (hA : TypedOracleCompiler.Compile.Batch.Cms.AnsOK cA) :
    TypedOracleCompiler.Compile.Batch.Cms.OKA
        (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P salt
      depthReq depthReqT depthReqL) cA ∧
      dataK Kc key k rec₀ = WholeD.of a (wholeAt (dryKey k (key rec₀))) ∧
      dataP Kc key c block z₀ = WholeD.of a (wholeAt (dryProof c (key z₀.2) (block z₀.1))) :=
  ⟨oka_of_four (four_atMakers Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
      early late P salt depthReq depthReqT depthReqL hL hLb slots) hA,
    by unfold dataK dataAt; rw [if_pos hok.okK], by unfold dataP dataAt; rw [if_pos hok.okP]⟩

end OnBytes.RunA

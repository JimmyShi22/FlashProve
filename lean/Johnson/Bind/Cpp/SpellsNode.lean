-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SpellsNode.lean: THE THIRD EQUATION OF THE INTERFACE (SpellsNode,
Johnson/Bind/Cpp/Spells.lean), PROVED, at all public files Z and every hash function, under no
premise: a vertex's typed answer is the format's vertex hash (number 166) at the start c, the digest
of the three public files, over the hash function read on byte strings, read as a digest.

Why. The written committer's tree asks a typed oracle at two digests. That oracle is read out of one
hash function through the told structure's coding of typed queries. The running committer
(Johnson/Bind/Twin.lean) asks the format's hash at the two children's bytes. The tie between the two
wants that these are one answer.

How, from letters to the told structure (the first three in the namespace Bind.Node, the others in
Bind.Cpp).
  `mAll_node`   at ANY data of the one coding of all three files' typed queries (`mAll`,
     Johnson/PV/CutAll.lean): what is read out at a vertex of two strings of 256 bits is the hash
     function's answer at the bits of the format's string under 166, at the page's digest. Calls:
     `implOf_node` (OnBytes/TypedOracleCompiler/Run/PageOf.lean), `cutAll_proof` (CutAll.lean), `cutProof_node`
     (OnBytes/K/Arm/ProofCut.lean), `pNode_put` (Run/CodingPage166.lean).
  `mOneAt_node`, `mD_node`   so at the run's coding at bytes c, and at a value d of the public
     reading (Johnson/Top/Fire/Code/TieAtValues.lean, Johnson/Flat/Told/Dec/TAt.lean).
  `node_T₀`   so at the told structure's coding (`T₀_m`, Johnson/Goal/Conditions/BindsPlain.lean),
     at every value d: the start is the bytes of d's told part.
  `vertex_at`   the format's vertex hash over a hash function, written out.
  **`spellsNode`**   the two meet, by `spellsC` (Johnson/Bind/Cpp/SpellsC.lean).

Limits. One equation between terms of this library. Nothing on any program; nothing on collisions;
no binding of the commitment (the opening form, BindsWith), no correctness of extraction, no index
privacy (hiding of the weights).
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.SpellsC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Node
open OnBytes.K.Arm TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open _root_.Iop (Dig)
open _root_.Run (bytesToBits bitsToBytes pNode_put)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} {C : BothCut L K}

/-- **A vertex, at any data of the one coding**: what is read out at two strings of 256 bits is the
hash function's answer at the bits of the format's string under 166, at the page's digest. -/
theorem mAll_node (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (back : StrCode (AllPts 256 K L))
    (g : Fam (rom 256)) (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) :
    (readBlocks (mAll H G back) g OracleName.node (l, r) : Dig 256) =
      g () (bytesToBits (Fmt.oStr 0 166 0 0 C.P.cfg (bitsToBytes l ++ bitsToBytes r))) :=
  PageOf.implOf_node (cutAll C) (cutAll_one H G) (cutAll_hd H G) back g (l, r) _
    (cutAll_proof _ _ ((cutProof_node C.proof (l, r)).trans (pNode_put C.P.cfg l r hl hr)))

end Bind.Node

namespace Bind.Node
open LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open OnBytes.K.Arm.Pub
open PV.EntryFive (dsF xsF)

variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull)
  (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (P : (FsAtR A E G DK DP runK runP dec).Provers)
  (h₀ : HId) (it : XF → ByteArray) (sR : ℕ)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
  (hK : KF DK DP + 1 + 1 < 2 ^ 49)

/-- A vertex at the run's coding at bytes c. -/
theorem mOneAt_node (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) (dK dP : Pd3)
    (g : Fam (rom 256)) (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) :
    (readBlocks (mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK) g
        TypedOracleCompiler.Compile.Batch.OracleName.node (l, r) : Dig 256) =
      g () (bytesToBits (Fmt.oStr 0 166 0 0 c (bitsToBytes l ++ bitsToBytes r))) := by
  unfold mOneAt PV.MFull.mFOneD W4M.mAny
  exact mAll_node _ _ _ g l r hl hr

/-- A vertex at the run's coding at a value of the public reading: the start is the bytes of the
first answer. -/
theorem mD_node (d : D8) (g : Fam (rom 256)) (l r : Bits) (hl : l.length = 256)
    (hr : r.length = 256) :
    (readBlocks (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d) g
        TypedOracleCompiler.Compile.Batch.OracleName.node (l, r) : Dig 256) =
      g () (bytesToBits
        (Fmt.oStr 0 166 0 0 (digToBytes d.1) (bitsToBytes l ++ bitsToBytes r))) := by
  unfold mD
  exact mOneAt_node A E G DK DP runK runP dec P h₀ it sR hDK hDP hK _ _ _ _ _ g l r hl hr

end Bind.Node

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop (Dig)

/-- The format's vertex hash over a hash function, read as a digest, is that function's answer at
the bits of the format's string under 166. -/
theorem vertex_at (hash : Hash) (cfg l r : ByteArray) :
    _root_.Run.bytesToDig (Fmt.vertexW (m := Id) (hAt hash) cfg l r) =
      hash (_root_.Run.bytesToBits (Fmt.oStr 0 166 0 0 cfg (l ++ r))) := by
  unfold Fmt.vertexW hAt
  rw [Fmt.HM_id]
  unfold Fmt.HO
  rw [if_neg (by decide)]
  exact OnBytes.K.Arm.bytesToDig_digToBytes _

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem OnBytes.K.Arm.Pub.pub8 PV.EncId.encF LPFD.Full.mD
  LPFD.Full.mOneAt PV.MFull.cfgF hAt

/-- **A vertex at the told structure's coding**, at every value d of the public reading. -/
theorem node_T₀ (Z : PublicFiles) (d : (T₀ Z).D) (g : Fam (rom 256)) (l r : Bits) (hl : l.length = 256)
    (hr : r.length = 256) :
    (readBlocks ((T₀ Z).m d) g OracleName.node (l, r) : Dig 256) =
      g () (_root_.Run.bytesToBits (Fmt.oStr 0 166 0 0 (_root_.Run.digToBytes ((T₀ Z).part d))
        (_root_.Run.bitsToBytes l ++ _root_.Run.bitsToBytes r))) :=
  Bind.Node.mD_node (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).G
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).P (dataAtFiles flashProveData Z).hStar (dataAtFiles flashProveData Z).it
    (dataAtFiles flashProveData Z).sR (dataAtFiles flashProveData Z).hDK (dataAtFiles flashProveData Z).hDP (dataAtFiles flashProveData Z).hK d g l r
    hl hr

/- And these. -/
attribute [local irreducible] T₀ dAt

/-- **A VERTEX's ANSWER IS THE FORMAT's VERTEX HASH, AT THE START c.** -/
theorem spellsNode (Z : PublicFiles) (hash : Hash) : SpellsNode Z hash := by
  intro a b
  rw [vertex_at]
  show (readBlocks ((T₀ Z).m (dAt Z hash)) (_root_.Run.famOne hash) OracleName.node
    (List.ofFn a, List.ofFn b) : Dig 256) = _
  rw [node_T₀ Z _ _ _ _ (List.length_ofFn) (List.length_ofFn),
    show (T₀ Z).part (dAt Z hash) = hash (configString Z) from spellsC Z hash]
  rfl

end Bind.Cpp

end

#print axioms Bind.Node.mAll_node
#print axioms Bind.Node.mOneAt_node
#print axioms Bind.Node.mD_node
#print axioms Bind.Cpp.vertex_at
#print axioms Bind.Cpp.node_T₀
#print axioms Bind.Cpp.spellsNode

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/Leaf.lean: a leaf's answer under the written committer's coding of typed queries
is the format's leaf hash under the number 174: the proposition `Bind.Cpp.SpellsLeaf`
(Johnson/Bind/Cpp/Spells.lean), where the plan's salt has 40 bytes. Statements with proofs. No
definition: no goal is stated.
Why. The committer that is written out in Lean, `(T₀ Z).commitAtCoins`
(Johnson/Top/ToldCommitPlain.lean; Johnson/Goal/Conditions/BindsPlain.lean), asks typed oracles,
which are read out of one hash function through a coding of typed queries into strings. To compare
its commitment with that of a committer that asks the format's hash at byte strings, each kind of
typed query has to be spelled. This file spells the leaf.
The road, from letters up.
  `mFOneD_leaf`: at the coding `PV.MFull.mFOneD` (Johnson/Top/Fire/Code/Dec/MOneD.lean), at letters:
    the string of a leaf query whose typed salt is "c, then salt bytes" and whose body spells a
    label and bytes is the format's string of that call, with the start c. From `mF_codeD`,
    `code_leaf` (CutCode.lean), `leafCode_at` and `leafOK2_cfg` (OnBytes/TypedOracleCompiler/Run/RowsE3.lean).
  `mD_code_leaf`, `mD_read_leaf`: the same at `LPFD.Full.mD` (Johnson/Flat/Told/Dec/TAt.lean) at a
    value d of the public reading, and the answer that is read out of a hash function there.
  `read_leaf_at`: at `T₀ Z`, AT EVERY d: at the body of a stored table's symbol (position, column)
    that passes `storedOK` and the typed salt "the bytes of the told part of d, then salt bytes of
    the plan's length".
  **`spellsLeaf_of`**: `SpellsLeaf Z hash`, from `SaltAt Z` (the plan's salt at Z has 40 bytes) and
    `SpellsC Z hash` (the told part of the public reading is the hash function's answer at the
    public files' string).
Limits. Equations between values of this library's own terms: NOTHING ON ANY PROGRAM, and nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding. `SaltAt Z` IS A PREMISE AND IS SHOWN AT NO Z HERE; without
it the proposition is false at a hash function that tells the two strings apart, since the coding
then writes an escape string (by reading: the length test of the code of leaves fails). `SpellsC` is
a premise here and is not proved here (Closed.lean lays its theorem in). Nothing is asked of the
words of a column: `storedOK` (OnBytes/TypedOracleCompiler/Run/Tag174.lean) bounds the column's length and the
label's two words alone. That `Fmt.leafW` is what the format's page says, and that any program
computes it, is not said here. At the full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Cpp.Spells
import Johnson.Bind.Spell.CutCode
import OnBytes.TypedOracleCompiler.Run.RowsE3
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
open TypedOracleCompiler.Strings (ok2 rd2)

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (salt : ℕ) (K : ℕ)
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (it : ReqAt Inst.Model.ppref → ByteArray) (r₀ : RecFull)
  (c : ByteArray) (hc : c.size = 32) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
  (hK : K + 1 + 1 < 2 ^ 49)

/-- The string of a leaf query whose typed salt begins with c. -/
theorem mFOneD_leaf (b : List Bool) (n t i : ℕ) (z : ByteArray) (hok : ok2 b = true)
    (hrd : rd2 b = (n, t, i, z)) (sa : ByteArray) (hsa : sa.size = salt) (j : Fin 1) :
    (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP
        hK).code
        .leaf ⟨b, bytesToBits c ++ bytesToBits sa⟩ j =
      bytesToBits (Fmt.oStr 0 n t i c (z ++ sa)) := by
  rw [← mF_codeD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK
      hDP hK .leaf (by decide)]
  refine code_leaf _ _ _ _ ?_ j
  have h1 : (KeyLeaves.leavesAt W4M.L0 (8 * salt) c).lf.put ⟨b, bytesToBits c ++ bytesToBits sa⟩ =
      some (bytesToBits (Fmt.oStr 0 n t i c (z ++ sa))) :=
    RowsE3.leafCode_at W4M.L0 (8 * salt) salt rfl c b n t i z hok hrd c sa hc hsa
      (RowsE3.leafOK2_cfg W4M.L0 c sa hc b)
  exact (TypedOracleCompiler.Run.LinkAlong.leavesAlong_put
    (leafPairOf (L := carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) W4M.L0
      (Equiv.refl (List Bool))) (KeyLeaves.leavesAt W4M.L0 (8 * salt) c)
    ⟨b, bytesToBits c ++ bytesToBits sa⟩ ⟨b, bytesToBits c ++ bytesToBits sa⟩ rfl).trans h1

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
open TypedOracleCompiler.Strings (ok2 rd2)

variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull)
  (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool)
  (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
  (hK : KF DK DP + 1 + 1 < 2 ^ 49)

/-- The string of a leaf query under the run's coding at d, where the typed salt begins with the
bytes of d's first answer. -/
theorem mD_code_leaf (d : D8) (b : List Bool) (n t i : ℕ) (z : ByteArray) (hok : ok2 b = true)
    (hrd : rd2 b = (n, t, i, z)) (sa : ByteArray) (hsa : sa.size = saltG G) (j : Fin 1) :
    (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d).code .leaf
        ⟨b, bytesToBits (digToBytes d.1) ++ bytesToBits sa⟩ j =
      bytesToBits (Fmt.oStr 0 n t i (digToBytes d.1) (z ++ sa)) := by
  unfold mD mOneAt
  exact mFOneD_leaf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b n t i z hok hrd sa hsa j

/-- So the answer that is read out of a hash function. -/
theorem mD_read_leaf (d : D8) (b : List Bool) (n t i : ℕ) (z : ByteArray) (hok : ok2 b = true)
    (hrd : rd2 b = (n, t, i, z)) (sa : ByteArray) (hsa : sa.size = saltG G) (g : Fam (rom 256)) :
    (readBlocks (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d) g .leaf
        ⟨b, bytesToBits (digToBytes d.1) ++ bytesToBits sa⟩ : Dig 256) =
      g () (bytesToBits (Fmt.oStr 0 n t i (digToBytes d.1) (z ++ sa))) := by
  rw [← mD_code_leaf A E G DK DP runK runP dec P h₀ it sR hDK hDP hK d b n t i z hok hrd sa hsa 0]
  rfl

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
open TypedOracleCompiler.Strings (ok2 rd2 spell2 ok2_spell rd2_spell)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem
  LPFD.Full.mD

/-- A leaf's answer under the written committer's coding AT EVERY d, at the body of a stored
table's symbol and the typed salt "the bytes of the told part of d, then the salt bytes". -/
theorem read_leaf_at (Z : PublicFiles) (d : (T₀ Z).D) (g : Fam (rom 256)) (y : ℕ × List UInt64)
    (u : ByteArray) (hu : u.size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G)
    (hy : TypedOracleCompiler.Run.storedOK 32 (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) y) :
    (readBlocks ((T₀ Z).m d) g OracleName.leaf
        ⟨(R₀ Z).queryLayout.embE y, leafSalt (digToBytes ((T₀ Z).part d)) u⟩ : Dig 256) =
      g () (bytesToBits (Fmt.oStr 0 174
        (Fmt.leafPlace 0 y.2.length (LPFD.Full.saltG (dataAtFiles flashProveData Z).G / 8)) (2 ^ 32 + y.1)
        (digToBytes ((T₀ Z).part d))
        (Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length
          (LPFD.Full.saltG (dataAtFiles flashProveData Z).G)) ++ u))) := by
  have hb : (R₀ Z).queryLayout.embE y = spell2 174 (Fmt.leafPlace 0 y.2.length
                (LPFD.Full.saltG (dataAtFiles flashProveData Z).G / 8), 2 ^ 32 + y.1,
                Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length
                  (LPFD.Full.saltG (dataAtFiles flashProveData Z).G))) :=
    embStored_fit 32 (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) y hy
  have ht : Fmt.leafPlace 0 y.2.length (LPFD.Full.saltG (dataAtFiles flashProveData Z).G / 8) < 2 ^ 48 := by
    have := hy.2.1
    omega
  rw [hb]
  exact mD_read_leaf (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).G
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).P (dataAtFiles flashProveData Z).hStar (dataAtFiles flashProveData Z).it
    (dataAtFiles flashProveData Z).sR (dataAtFiles flashProveData Z).hDK (dataAtFiles flashProveData Z).hDP (dataAtFiles flashProveData Z).hK d _ 174 _
        _ _
    (ok2_spell 174 _ _ _ (Or.inr rfl) ht hy.2.2) (rd2_spell 174 _ _ _ (by decide) ht hy.2.2) u hu g

/-- **`SpellsLeaf Z hash`**, where the plan's salt at Z has 40 bytes (`SaltAt Z`), from
`SpellsC Z hash`. -/
theorem spellsLeaf_of (Z : PublicFiles) (hs : SaltAt Z) (hash : Hash) (hc : SpellsC Z hash) :
    SpellsLeaf Z hash := by
  intro y u b j hj hu h1 h2
  have hG : LPFD.Full.saltG (dataAtFiles flashProveData Z).G = 40 := (saltG_built Z).trans hs
  have hcB : Bind.Cpp.cAt Z hash = digToBytes ((T₀ Z).part (dAt Z hash)) := by
    unfold Bind.Cpp.cAt
    rw [hc]
  have hj' : j < 2 ^ 32 := (n_R₀ Z) ▸ hj
  have hy : TypedOracleCompiler.Run.storedOK 32 (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) (y ⟨j, hj⟩) := by
    rw [hG]
    refine ⟨?_, ?_, ?_⟩
    · rw [h2]; norm_num
    · rw [h2]; unfold Fmt.leafPlace; norm_num
    · rw [h1]; omega
  have key := read_leaf_at Z (dAt Z hash) (_root_.Run.famOne hash) (y ⟨j, hj⟩) (u j)
    (hu.trans hG.symm) hy
  rw [hG, h1, ← hcB] at key
  unfold famAt committerLeafInput
  rw [dif_pos hj]
  refine key.trans ?_
  unfold Fmt.leafW hAt Fmt.HM Fmt.leafBytes
  rw [if_neg (by decide), hu]
  exact (_root_.Run.TieTree.bytes_dig _).symm

end
end Bind.Spell

#print axioms Bind.Spell.mFOneD_leaf
#print axioms Bind.Spell.mD_code_leaf
#print axioms Bind.Spell.mD_read_leaf
#print axioms Bind.Spell.read_leaf_at
#print axioms Bind.Spell.spellsLeaf_of

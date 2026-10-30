-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvAny.lean: THE ONE CODING's WRITING SIDE AS A VALUE WITH CODE, AT ANY INTERFACE L : BatchProtocolWithLeafBody
  I X AND ANY NUMBER OF BLOCKS: for the one sheet verifyV (DvOf …): to be called at L := carrierV LV
  (List Bool) AT aL.
  WriteSide S lam      blocks · rng · code: TO THE LETTER Rom.ImplV.

    `Rom.ImplV` is declared in Rom/FamilySide.lean, `mVOf` is declared in this file at the type WriteSide, and `toImplV` (W4M.WriteSide S lam → ImplV S lam) is declared in Johnson/PV/MFull.lean and in Johnson/PV/MSmall.lean.
  mVOf C bk            ⟨blk K, rngEquiv 256 K, codeRun (fun _ => L) (cutAll C) bk⟩: THE VALUE FOR
    THE LETTER m
  mVOf_reads           PageRun.famRun at put := cutAll C, bk IS what mVOf reads out of a hash
    function g: by unfolding
  mVOf_blocks | _rng | _code   against the theorem's coding mAll H G back: one in blocks and rng;
    one in code at every oracle but the spare one (codeRun_eq, OnBytes/TypedOracleCompiler/Run/PageRunLaws.lean)
  pageAny · fitKAny · fitPAny · runAny    the page of all three files, both tests of fitness, and
    the record «once a query» (Lite.onceD), at L, from the same letters as MemberOne's
    pageOne
  bothAny := bothOf pageAny fitKAny fitPAny
  famAny := famCut pageAny fitKAny fitPAny runAny bk O     THE FAST FAMILY; famAny_reads: it IS what
    mVOf bothAny bk reads out of gOf O
No soundness. Nothing has run.


-/
import Johnson.PV.FamCut
import OnBytes.TypedOracleCompiler.Run.PageRunLaws
import Johnson.Top.ProofPageD
import Johnson.RunOne.OnceD

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page
    Johnson.RunOne
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (HId)

/-- The writing side of an encoding of typed queries: what an algorithm over one hash function
  reads. -/
structure WriteSide (S : OSpec) (lam : ℕ) where
  blocks : S.ι → ℕ
  rng : ∀ o, S.Rng o ≃ (Fin (blocks o) → Fin lam → Bool)
  code : (o : S.ι) → S.Dom o → Fin (blocks o) → List Bool

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **THE VALUE FOR THE LETTER m.** -/
def mVOf (C : BothCut L K) (bk : AllPts 256 K L → List Bool) : WriteSide (typedOracleFamily 256 K L) 256 :=
  ⟨blk K, rngEquiv 256 K, codeRun (fun _ => L) (cutAll C) bk⟩

/-- **What it reads out of a hash function is PageRun.famRun.** -/
theorem mVOf_reads (C : BothCut L K) (bk : AllPts 256 K L → List Bool) (g : Fam (rom 256))
    (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famRun (fun _ => L) (cutAll C) bk g o q =
      ((mVOf C bk).rng o).symm fun j => g () ((mVOf C bk).code o q j) := rfl

section Against
variable {C : BothCut L K} {lL : ℕ} (H : BothLaws C) (G : LinkLaws C lL) (back : StrCode (AllPts 256
    K L))

theorem mVOf_blocks : (mVOf C back.put).blocks = (mAll H G back).blocks := rfl

theorem mVOf_rng : (mVOf C back.put).rng = (mAll H G back).rng := rfl

/-- **At every oracle but the spare one the string is the theorem's coding's.** -/
theorem mVOf_code (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other) (q : domOf 256 L o)
    (j : Fin (blk K o)) : (mVOf C back.put).code o q j = (mAll H G back).code o q j :=
  codeRun_eq (TypedOracleCompiler.Run.PageOf.pageOf (cutAll C) (cutAll_one H G) (cutAll_hd H G) back) o ho q
      j

end Against

variable (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (tlK tlP : Dig 256 → List OnBytes.E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ) (bd : L.Bd → List Bool) (p0 p1 : PBt L .test)
  (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode L (K + 1)) (V : Leaves L) (dK dP : Pd3)

/-- **THE PAGE OF ALL THREE FILES**, with the six digests as data. -/
def pageAny : PageJ L (K + 1) :=
  (pageFill cfg sR (fillJ C DK tFk tJk t3k rdK (silentKey h₀ k X))
    (fillJ C DP tFp tJp t3p rdP (silentProof h₀ c req)) bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk
    V).withPd dK dP

/-- The test on the key file's chain queries. -/
def fitKAny : FitJ L .test := fitAt C DK tFk tJk t3k rdK (fFrontK tlK) (fJoin tlK) fSeam

/-- The test on the proof file's chain queries. -/
def fitPAny : FitJ L .onl := fitAt C DP tFp tJp t3p rdP (fFrontP tlP req okX) (fJoin tlP) fSeam

/-- What the calls of a chain query share, once a query, along the data. -/
def runAny : RunJ (pageAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg sR bd p0
    p1
    isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) where
  key := Lite.onceD C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK)
  proof := Lite.onceD C DP tFp tJp t3p rdP ((silentProof h₀ c req).withPd dP)
  hk := fun q => Lite.onceD_eq C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK) q
  hp := fun q => Lite.onceD_eq C DP tFp tJp t3p rdP ((silentProof h₀ c req).withPd dP) q

/-- The data of the one cut. -/
def bothAny : BothCut L (K + 1) :=
  bothOf (pageAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg sR bd p0 p1 isP0 isP1 cfgL
      sh
      hp0 hp1 rest Lk V dK dP)
    (fitKAny C DK tFk tJk t3k rdK tlK) (fitPAny C DP tFp tJp t3p rdP req okX tlP)

variable (bk : AllPts 256 (K + 1) L → List Bool) (O : ByteArray → ByteArray)

/-- **THE FAST FAMILY.** -/
def famAny : Fam (typedOracleFamily 256 (K + 1) L) :=
  famCut _ (fitKAny C DK tFk tJk t3k rdK tlK) (fitPAny C DP tFp tJp t3p rdP req okX tlP)
    (runAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0
      hp1 rest Lk V dK dP) bk O

/-- **IT IS WHAT THE VALUE FOR m READS OUT OF THE HASH FUNCTION gOf O.** -/
theorem famAny_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1
        cfgL sh hp0 hp1 rest Lk V dK dP bk O o q =
      ((mVOf (bothAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1
          isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) bk).rng o).symm fun j =>
        gOf O () ((mVOf (bothAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg
            sR
          bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) bk).code o q j) :=
  congrFun (congrFun (famCut_famRun _ _ _ _ bk O) o) q

end W4M

#print axioms W4M.mVOf_reads
#print axioms W4M.mVOf_code
#print axioms W4M.famAny_reads

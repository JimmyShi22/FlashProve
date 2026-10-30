-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvAt.lean: THE VALUE FOR THE ONE SHEET's LETTER m, AND THE FAST FAMILY, WITH EVERY LETTER
  OF THE PAGE THAT A TERM OF THE LIBRARY WITH CODE CAN FILL FILLED; general in the interface L, so
  that ONE CALL lays it at carrierV LV (List Bool) AT aL.
WHAT A CALLER BRINGS (all data; no law):
  L · K · the rounds' data DK DP (already «.at a») · the six fixed messages (front₀ rK · join₀ rK ·
    empty · front₀ rP · join₀ rP · empty)
  rdK rdP      the interface's plain parts read as the files' own: at carrierV | typedOracleCarrier: «some»
  h₀ k c'      read for the six pd alone, which dK dP overwrite: any values with code
  req · okX    the request's two strings and the test on a typed instance (the front set's: reqOf sp
    · okItems okS isR)
  v            the tables' number of row bits (tlK := fun _ l => cAL v 1 l · tlP :=
    tlAns, Johnson/Flat/TailAns.lean)
  c            the configuration's digest, 32 bytes · dK dP: the six chains' parameters' digests ·
    sR: the bytes of the request tree's salt
  bdE          the bodies as strings of bits: at Bd := List Bool: Equiv.refl _
  p0 · serK    the seeds' queries' plain part (SeedVals.plainFirst _ _ _ _) and the serialiser of
    the key file's plain parts (serWhole …)
  sh · rest    the tables' shape as bits (pubShapeTop‹S›) and the rest of a table's name
    (pubRestTop‹S› c)
  nb           the bits of a file's salt (8 * salt)
  linkF        THE ENTRY FILE's CHAIN QUERIES' STRINGS: A LETTER STILL: ArmLinkCode.linkAt has no
    code (its first query's code lf0 reads the answers back out of their digests by choice:
    OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean:51-54, :92-100)
  bk           the total code's put behind the escape (ArmBack.backL2 … .put)
NAMES: pageAnyF (pageAny with the two spellings as functions; pageAnyF_eq := rfl) · pageAt · fitKAt
  · fitPAt · runAt' · bothAt · **mAt** · **famAt** · famAt_reads · the record's wire's five: tAt ·
  cfgAt c · (sh) · (p0) · (p0).
No soundness. Nothing has run.


-/
import Johnson.PV.MvAny
import OnBytes.Maker.Page.LeafTakenAt
import Johnson.Flat.ArmPlain
import Johnson.Flat.TailAns
import OnBytes.K.KeyAnswers
import OnBytes.TypedOracleCompiler.Run.SeedVals
import Johnson.RunOne.Hollow

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page
    Johnson.RunOne
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open TypedOracleCompiler.Run.SeedPoints (fbSeeds)
open OnBytes.Flat (isAt isAt_iff tlAns)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (HId)

/-- An interface of which the code of leaves reads no field: the least at hand. -/
def L0 : _root_.Iop.BatchProtocol Unit Unit :=
  (Johnson.RunOne.hollowT (⟨Johnson.RunOne.noProto (oneExternalString 0 Unit), PUnit.unit⟩ : BatchInteractiveOracleProof Unit
      (oneExternalString 0 Unit)) ()).toBatchProtocol

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}
  (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)

section F
variable (cfg : ByteArray) (sR : ℕ) (bd : L.Bd → List Bool) (p0 p1 : PBt L .test)
  (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool))
  (leafXF : LeafIn L → Option (List Bool)) (dK dP : Pd3)

/-- The page of all three files, with the entry's and the leaves' spellings as functions. -/
def pageAnyF : PageJ L (K + 1) :=
  ({ cfg := cfg
     key := fillJ C DK tFk tJk t3k rdK (silentKey h₀ k X)
     proof := fillJ C DP tFp tJp t3p rdP (silentProof h₀ c' req)
     sR := sR
     leaf := leafOf bd
     link := linkF
     seeds := (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest (K + 1)).put
     leafX := leafXF
     other := fun _ => none } : PageJ L (K + 1)).withPd dK dP

/-- It is pageAny at the two codes' own functions. -/
theorem pageAnyF_eq (Lk : LinkCode L (K + 1)) (V : Leaves L) :
    pageAnyF C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req cfg sR bd p0 p1 isP0 isP1 cfgL sh
        hp0
        hp1 rest Lk.pL.put V.lf.put dK dP =
      pageAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req cfg sR bd p0 p1 isP0 isP1 cfgL sh
          hp0
        hp1 rest Lk V dK dP := rfl

end F

variable (v : ℕ) (c : ByteArray) (sR : ℕ) (bdE : L.Bd ≃ List Bool) (p0 : PBt L .test)
  (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)

/-- **THE PAGE.** -/
def pageAt : PageJ L (K + 1) :=
  pageAnyF C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE p0 p0 (isAt serK p0)
    (isAt serK p0) (TypedOracleCompiler.Run.SeedVals.cfgL c) sh (isAt_iff serK p0) (isAt_iff serK p0) rest
        linkF
    (leavesJ L0 nb c bdE).lf.put dK dP

def fitKAt : FitJ L .test := fitKAny C DK tFk tJk t3k rdK fun _ l => OnBytes.K.cAL v 1 l

def fitPAt : FitJ L .onl := fitPAny C DP tFp tJp t3p rdP req okX tlAns

/-- What the calls of a chain query share, once a query, along the data. -/
def runAt' : RunJ (pageAt (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE p0
    serK sh
    rest linkF nb dK dP) where
  key := Lite.onceD C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK)
  proof := Lite.onceD C DP tFp tJp t3p rdP ((silentProof h₀ c' req).withPd dP)
  hk := fun q => Lite.onceD_eq C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK) q
  hp := fun q => Lite.onceD_eq C DP tFp tJp t3p rdP ((silentProof h₀ c' req).withPd dP) q

def bothAt : BothCut L (K + 1) :=
  bothOf (pageAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE p0 serK sh rest linkF
      nb dK
      dP)
    (fitKAt C DK tFk tJk t3k rdK v) (fitPAt C DP tFp tJp t3p rdP req okX)

variable (bk : AllPts 256 (K + 1) L → List Bool) (O : ByteArray → ByteArray)

/-- **THE VALUE FOR THE LETTER m.** -/
def mAt : WriteSide (typedOracleFamily 256 (K + 1) L) 256 :=
  mVOf (bothAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest
      linkF nb
    dK dP) bk

/-- **THE FAST FAMILY.** -/
def famAt : Fam (typedOracleFamily 256 (K + 1) L) :=
  famCut _ (fitKAt C DK tFk tJk t3k rdK v) (fitPAt C DP tFp tJp t3p rdP req okX)
    (runAt' C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE p0 serK sh rest linkF nb dK
        dP)
    bk O

/-- **THE FAST FAMILY IS WHAT mAt READS OUT OF THE HASH FUNCTION gOf O.** -/
theorem famAt_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
        nb dK
        dP bk O o q =
      ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
          nb
          dK dP bk).rng o).symm fun j =>
        gOf O () ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
            rest
          linkF nb dK dP bk).code o q j) :=
  congrFun (congrFun (famCut_famRun _ _ _ _ bk O) o) q

/-- The record's wire's tag. -/
def tAt : Tag := .test

/-- The digests of a table's name behind the root. -/
def cfgAt (c : ByteArray) : List (Dig 256) := TypedOracleCompiler.Run.SeedVals.cfgL c

end W4M

#print axioms W4M.pageAnyF_eq
#print axioms W4M.famAt_reads

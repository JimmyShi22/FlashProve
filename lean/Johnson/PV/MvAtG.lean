-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvAtG.lean: Johnson/PV/MvAt.lean's pageAt | runAt' | famAt WITH THE SEEDS' SPELLING AS A
  FUNCTION (seedsF), AND THE EQUATIONS := rfl THAT pageAt | famAt ARE THESE AT THE SEEDS' OWN CODE.
  WHY: at a carrier whose key file's protocol has no round (the hollow carrier of the proof file:
hollow, Johnson/RunOne/Hollow.lean) the type of the seeds' queries' plain part is empty:
  pageAt, which takes such a plain part, has no value there; no typed query under the key file's tag
  exists there either.


-/
import Johnson.PV.MvAt

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page
    Johnson.RunOne
open TypedOracleCompiler.Run.SeedPoints (fbSeeds)
open OnBytes.Flat (isAt isAt_iff tlAns)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (HId)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}
  (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (v : ℕ) (c : ByteArray) (sR : ℕ) (bdE : L.Bd ≃ List Bool)
  (seedsF : FbIn 256 L .test × Fin (K + 1 + 1) → Option (List Bool))
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)

/-- The page, with the seeds' spelling as a function. -/
def pageAtG : PageJ L (K + 1) :=
  ({ cfg := c
     key := fillJ C DK tFk tJk t3k rdK (silentKey h₀ k X)
     proof := fillJ C DP tFp tJp t3p rdP (silentProof h₀ c' req)
     sR := sR
     leaf := leafOf bdE
     link := linkF
     seeds := seedsF
     leafX := (leavesJ L0 nb c bdE).lf.put
     other := fun _ => none } : PageJ L (K + 1)).withPd dK dP

def runAtG : RunJ (pageAtG (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE
    seedsF linkF
    nb dK dP) where
  key := Lite.onceD C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK)
  proof := Lite.onceD C DP tFp tJp t3p rdP ((silentProof h₀ c' req).withPd dP)
  hk := fun q => Lite.onceD_eq C DK tFk tJk t3k rdK ((silentKey h₀ k X).withPd dK) q
  hp := fun q => Lite.onceD_eq C DP tFp tJp t3p rdP ((silentProof h₀ c' req).withPd dP) q

variable (bk : AllPts 256 (K + 1) L → List Bool) (O : ByteArray → ByteArray)

def famAtG : Fam (typedOracleFamily 256 (K + 1) L) :=
  famCut _ (fitKAt C DK tFk tJk t3k rdK v) (fitPAt C DP tFp tJp t3p rdP req okX)
    (runAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE seedsF linkF nb dK dP) bk O

variable (p0 : PBt L .test) (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)

/-- The seeds' own code's function. -/
def seedsAt : FbIn 256 L .test × Fin (K + 1 + 1) → Option (List Bool) :=
  (fbSeeds L .test p0 p0 (isAt serK p0) (isAt serK p0) (TypedOracleCompiler.Run.SeedVals.cfgL c) sh
    (isAt_iff serK p0) (isAt_iff serK p0) rest (K + 1)).put

/-- **pageAt IS pageAtG at the seeds' own code.** -/
theorem pageAt_eq :
    pageAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE p0 serK sh rest linkF nb dK
        dP =
      pageAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE
        (seedsAt (K := K) c p0 serK sh rest) linkF nb dK dP := rfl

/-- **famAt IS famAtG at the seeds' own code.** -/
theorem famAt_eq :
    famAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
        nb dK dP
        bk O =
      famAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE
        (seedsAt (K := K) c p0 serK sh rest) linkF nb dK dP bk O := rfl

end W4M

#print axioms W4M.pageAt_eq
#print axioms W4M.famAt_eq

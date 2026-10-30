-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FitD.lean (fitAtD | fitAtD_eq LIE IN Johnson/PV/FitDCore.lean):
  THE TEST ON WHAT A CHAIN QUERY HOLDS (fitAt: OnBytes/Maker/Page/FitAt.lean:114) WITH THE PLAIN
  PART READ ALONG THE DATA (Lite.partAtD: Johnson/RunOne/OnceD.lean:40), FOR SPEED
  ALONE; fitAtD_eq: IT IS fitAt.
AND THE FAST FAMILY AT IT: famAtGD; famAtGD_eq: IT IS W4M.famAtG (Johnson/PV/MvAtG.lean). No
  premise.


-/
import Johnson.PV.MvAtG
import Johnson.PV.FitDCore

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page
    Johnson.RunOne
open OnBytes.Flat (tlAns)
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
  (bk : AllPts 256 (K + 1) L → List Bool) (O : ByteArray → ByteArray)

/-- **The fast family with the fast tests.** -/
def famAtGD : Fam (typedOracleFamily 256 (K + 1) L) :=
  famCut _ (fitAtD C DK tFk tJk t3k rdK (fFrontK fun _ l => OnBytes.K.cAL v 1 l) (fJoin fun _ l =>
      OnBytes.K.cAL v 1 l) fSeam)
    (fitAtD C DP tFp tJp t3p rdP (fFrontP tlAns req okX) (fJoin tlAns) fSeam)
    (runAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE seedsF linkF nb dK dP) bk O

/-- **It is famAtG.** -/
theorem famAtGD_eq :
    famAtGD C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF nb dK dP
        bk O =
      famAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF nb dK
          dP bk O := by
  unfold famAtGD
  rw [fitAtD_eq, fitAtD_eq]
  rfl

end W4M

#print axioms W4M.famAtGD_eq

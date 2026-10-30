-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvPrepQ.lean (famPrepQ | shoutAt | shoutAt_eq LIE IN Johnson/PV/PrepCore.lean): THE FAST
  FAMILY AT A PREPARED VALUE AND AT ANY bk: famPrepQ pr bk O mK mP :=
  famCutQ … (Johnson/PV/FamCutQ.lean) at Johnson/PV/PrepCore.lean's Prep.
  **famPrepQ_at : famPrepQ (prepAt …) bk O mK mP = famAt … bk O** · **famPrepQ_reads**: it IS what
    mAt … bk reads out of gOf O: AT EVERY bk AND EVERY HINT; no premise.
  shoutAt bk: bk itself, with a line on the error stream whenever it is called (dbgTrace is no part
    of a value: shoutAt_eq := rfl).


-/
import Johnson.PV.MvPrep
import Johnson.PV.FamCutQ

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

variable (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (v : ℕ) (c : ByteArray) (sR : ℕ) (bdE : L.Bd ≃ List Bool)
  (p0 : PBt L .test) (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)
  (bk : AllPts 256 (K + 1) L → List Bool) (O : ByteArray → ByteArray) (mK mP : ℕ → ℕ)

/-- **At prepAt it is famAt, at every bk and every hint.** -/
theorem famPrepQ_at :
    famPrepQ (prepAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
        rest linkF nb dK dP) bk O mK mP =
      famAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
          nb dK dP bk O := by
  unfold famPrepQ
  rw [famCutQ_eq]
  show famCut _ (fitAtD C DK tFk tJk t3k rdK _ _ _) (fitAtD C DP tFp tJp t3p rdP _ _ _) _ bk O = _
  rw [fitAtD_eq, fitAtD_eq]
  rfl

/-- **SO IT IS WHAT mAt … bk READS OUT OF THE HASH FUNCTION gOf O.** -/
theorem famPrepQ_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famPrepQ (prepAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
        rest linkF nb dK dP) bk O mK mP o q =
      ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
          nb dK dP bk).rng o).symm fun j =>
        gOf O () ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
            rest linkF nb dK dP bk).code o q j) := by
  rw [famPrepQ_at]
  exact famAt_reads ..

end W4M

#print axioms W4M.famPrepQ_at
#print axioms W4M.famPrepQ_reads

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvAtL.lean: THE FAST FAMILY FOR THE ONE SHEET's m IN THE FORM FOR A LONG EVALUATION:
  Johnson/PV/MvAt.lean's famAt | Johnson/PV/MvAtG.lean's famAtG over famCutL
  (Johnson/PV/FamCutL.lean: as many delayed values as the rounds need, and the last; no query held
  under the
proof file's tag) and the tests read along the data (Johnson/PV/FitD.lean). The hints:
  Lite.needAt DK | DP (Johnson/RunOne/OnceD.lean:65).
  famAtGL … seedsF linkF nb dK dP e O   ·  famAtGL_eq : … = famAtG … (fun _ => e ()) O
  famAtL … p0 serK sh rest linkF nb dK dP e O  ·  famAtL_eq : … = famAt … (fun _ => e ()) O  ·
    **famAtL_reads**: it IS what mAt … (fun _ => e ()) reads out of gOf O.
e : Unit → List Bool: THE ESCAPE's STRING AS ONE CONSTANT: bk := fun _ => e (): the shouting stub.
  No premise anywhere. No soundness. Nothing has run.


-/
import Johnson.PV.FamCutL
import Johnson.PV.FitD

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

section G
variable (seedsF : FbIn 256 L .test × Fin (K + 1 + 1) → Option (List Bool))
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)
  (e : Unit → List Bool) (O : ByteArray → ByteArray)

/-- The family for a long evaluation, with the seeds' spelling as a function. -/
def famAtGL : Fam (typedOracleFamily 256 (K + 1) L) :=
  famCutL _ (fitAtD C DK tFk tJk t3k rdK (fFrontK fun _ l => OnBytes.K.cAL v 1 l) (fJoin fun _ l =>
      OnBytes.K.cAL v 1 l) fSeam)
    (fitAtD C DP tFp tJp t3p rdP (fFrontP tlAns req okX) (fJoin tlAns) fSeam)
    (runAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE seedsF linkF nb dK dP) e O
    (Lite.needAt DK) (Lite.needAt DP)

/-- **It is famAtG at the constant bk.** -/
theorem famAtGL_eq :
    famAtGL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF nb dK dP
        e O =
      famAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF nb dK
          dP (fun _ => e ()) O := by
  unfold famAtGL
  rw [famCutL_eq, fitAtD_eq, fitAtD_eq]
  rfl

end G

variable (p0 : PBt L .test) (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)
  (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)
  (e : Unit → List Bool) (O : ByteArray → ByteArray)

/-- **THE FAST FAMILY, FOR A LONG EVALUATION.** -/
def famAtL : Fam (typedOracleFamily 256 (K + 1) L) :=
  famAtGL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE (seedsAt (K := K) c p0
      serK sh rest) linkF nb dK dP e O

/-- **It is famAt at the constant bk.** -/
theorem famAtL_eq :
    famAtL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
        nb dK dP e O =
      famAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
          nb dK dP (fun _ => e ()) O :=
  (famAtGL_eq C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE (seedsAt (K := K) c
      p0 serK sh rest) linkF nb dK dP e O).trans
    (famAt_eq C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE linkF nb dK dP (fun
        _ => e ()) O p0 serK sh rest).symm

/-- **IT IS WHAT mAt, AT THE CONSTANT bk, READS OUT OF THE HASH FUNCTION gOf O.** -/
theorem famAtL_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famAtL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
        nb dK dP e O o q =
      ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF
          nb dK dP (fun _ => e ())).rng o).symm fun j =>
        gOf O () ((mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
            rest linkF nb dK dP (fun _ => e ())).code o q j) := by
  rw [famAtL_eq]
  exact famAt_reads ..

end W4M

#print axioms W4M.famAtGL_eq
#print axioms W4M.famAtL_eq
#print axioms W4M.famAtL_reads

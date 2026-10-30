-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/PV/MvAtAny.lean: ONE EQUATION AT LETTERS: W4M.mAt (Johnson/PV/MvAt.lean), at the entry's
  strings of a LinkCode, IS W4M.mVOf at W4M.bothAny (Johnson/PV/MvAny.lean) at that code and the
  leaves' code leavesJ: so Johnson/PV/LawsAny.lean's laws speak of the value that is laid. := rfl.


-/
import Johnson.PV.MvAt
import Johnson.PV.LawsAny

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page
    Johnson.RunOne
open TypedOracleCompiler.Run.SeedPage (LinkCode)
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
  (v : ℕ) (c : ByteArray) (sR : ℕ) (bdE : L.Bd ≃ List Bool) (p0 : PBt L .test)
  (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray) (Lk : LinkCode L (K + 1)) (nb : ℕ) (dK
      dP : Pd3)
  (bk : AllPts 256 (K + 1) L → List Bool)

theorem mAt_is_any :
    mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest Lk.pL.put
        nb dK dP bk =
      mVOf (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX (fun _ l =>
          OnBytes.K.cAL v 1 l) tlAns c sR bdE p0 p0 (isAt serK p0) (isAt serK p0)
        (TypedOracleCompiler.Run.SeedVals.cfgL c) sh (isAt_iff serK p0) (isAt_iff serK p0) rest Lk (leavesJ
                    L0 nb c bdE) dK dP) bk := rfl

/-- The same, string by string. -/
theorem mAt_code_any (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) (j : Fin (blk (K + 1)
                    o)) :
    (mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest
        Lk.pL.put nb dK dP bk).code o q j =
      (mVOf (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX (fun _ l =>
          OnBytes.K.cAL v 1 l) tlAns c sR bdE p0 p0 (isAt serK p0) (isAt serK p0)
        (TypedOracleCompiler.Run.SeedVals.cfgL c) sh (isAt_iff serK p0) (isAt_iff serK p0) rest Lk (leavesJ
                    L0 nb c bdE) dK dP) bk).code o q j := rfl

/-- Two tests on a typed instance that are one function give one string. (Two texts of one `match`
  in two files are two constants to Lean: this carries an equation of functions over.) -/
theorem mAt_code_okX (okX' : X → Bool) (h : okX = okX')
    (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool))
    (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) (j : Fin (blk (K + 1) o)) :
    (mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest linkF nb
        dK dP bk).code o q j =
      (mAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX' v c sR bdE p0 serK sh rest linkF
          nb dK dP bk).code o q j := by
  subst h
  rfl

end W4M

#print axioms W4M.mAt_is_any

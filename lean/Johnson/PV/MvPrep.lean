-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MvPrep.lean (Prep | famPrep | famPrep_hint LIE IN Johnson/PV/PrepCore.lean):
  THE PAGE MADE ONCE. WHY (A READING OF THE TEXTS; WHETHER IT IS SO, AND WHAT IT COSTS,
  IS FOR A MEASUREMENT): famAt | famAtL … are definitions of many letters whose value is a FUNCTION
  of the oracle's name and the query: handed on with these two left
open, compiled Lean may run the whole body anew AT EVERY QUERY: the page would then be built again
  each time: six hashes of the chains' parameter bytes (silentKey | silentProof make them; withPd
  then overwrites them) and six lengths of the lists of rounds: at every leaf and vertex too.
HERE: what does not hang on the query is a VALUE, no function: `Prep`: the page, both tests, the
  record «once a query». A caller binds it once (let pr := prepAt …) and hands on famPrep pr e O mK
  mP.
  prepAtG | prepAt            the value, from famAtGL's | famAtL's own letters
  famPrep pr e O mK mP        := famCutL pr.P pr.ΦK pr.ΦP pr.R e O mK mP  ·  famPrep_hint: at any
    two pairs of hints it is one function  ·  hintK K D: the hint under the key file's tag that
    covers the seeds' queries
  **famPrep_atG | famPrep_at** : famPrep (prepAtG | prepAt …) e O (needAt DK) (needAt DP) = famAtGL
    | famAtL … e O := rfl
What a compiler computes how often is a fact about that compiler and no theorem. No soundness.


-/
import Johnson.PV.MvAtL
import Johnson.PV.PrepCore

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

/-- **The hint under the key file's tag.** At the typed rounds 0, 1, 2: ALL blocks; else what the
  key file's own round needs. WHY: the seeds' two queries stand under that tag at the typed rounds 1
  and 2 (sel0 | sel1: OnBytes/TypedOracleCompiler/Run/SeedPoints.lean), and the record's seed
reads 95 blocks of the second answer at the small size and 140 at the full, while needAt of the key
  file's data at the typed rounds 0 1 2 is 0 45 0 AT BOTH SIZES (evaluated at one set of public
  files, not shown here): there every block that the seed reads lies beyond the hint: and a
  block beyond the hint that is read is hashed anew for every bit. A handful of queries stand at
  these rounds: keeping all their blocks costs little. -/
def hintK (K : ℕ) (D : WholeD) (i : ℕ) : ℕ := if i ≤ 2 then K else Lite.needAt D i

variable (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (v : ℕ) (c : ByteArray) (sR : ℕ) (bdE : L.Bd ≃ List Bool)

/-- The value, with the seeds' spelling as a function. -/
def prepAtG (seedsF : FbIn 256 L .test × Fin (K + 1 + 1) → Option (List Bool))
    (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3) : Prep
        L (K + 1) :=
  ⟨_, fitAtD C DK tFk tJk t3k rdK (fFrontK fun _ l => OnBytes.K.cAL v 1 l) (fJoin fun _ l =>
      OnBytes.K.cAL v 1 l) fSeam,
    fitAtD C DP tFp tJp t3p rdP (fFrontP tlAns req okX) (fJoin tlAns) fSeam,
    runAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req c sR bdE seedsF linkF nb dK dP⟩

theorem famPrep_atG (seedsF : FbIn 256 L .test × Fin (K + 1 + 1) → Option (List Bool))
    (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)
    (e : Unit → List Bool) (O : ByteArray → ByteArray) :
    famPrep (prepAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF
        nb dK dP) e O (Lite.needAt DK) (Lite.needAt DP) =
      famAtGL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE seedsF linkF nb dK
          dP e O := rfl

/-- **The value.** -/
def prepAt (p0 : PBt L .test) (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)
    (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3) : Prep
        L (K + 1) :=
  prepAtG C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE (seedsAt (K := K) c p0
      serK sh rest) linkF nb dK dP

theorem famPrep_at (p0 : PBt L .test) (serK : Ser (PBt L .test)) (sh : Bits) (rest : ByteArray)
    (linkF : FbIn 256 L .link × Fin (K + 1 + 1) → Option (List Bool)) (nb : ℕ) (dK dP : Pd3)
    (e : Unit → List Bool) (O : ByteArray → ByteArray) :
    famPrep (prepAt C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh
        rest linkF nb dK dP) e O (Lite.needAt DK) (Lite.needAt DP) =
      famAtL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c' req okX v c sR bdE p0 serK sh rest
          linkF nb dK dP e O := rfl

end W4M

#print axioms W4M.famPrep_atG
#print axioms W4M.famPrep_at

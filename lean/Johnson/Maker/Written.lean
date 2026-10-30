-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Written.lean: a whole key file and a whole proof file as written files (`FileW`,
OnBytes/TypedOracleCompiler/Joined/Wire.lean) of the object with records of three files (`objF`, `wireF`,
Johnson/EntryRec/OkcFiles.lean); and that the compiled verifier with a record runs just their
verifiers.

The compiled verifier with a record (`VC`, Johnson/TypedOracleCompiler/RecCompile/Cms.lean) runs three compiled
verifiers: of Test, of Link, of the session. At `objF` Test is a whole key file and the session a
whole proof file, each three joined chains (OnBytes/Maker/Whole.lean). The theorems on a file with
three joined chains (OnBytes/TypedOracleCompiler/Joined/) speak of a written file: a description, a tag, a wire
record, and how symbols, plain parts and the instance are written into the typed queries. Here the
two are laid on each other. Nothing is cast: at `objF` and `wireF` the carrier's shapes and
annotations at the two tags are the files' own by unfolding.

  `fileKey`     the key file: under the tag of Test; no instance is written into a query
  `fileProof`   the proof file: under the session's tag; the request and the record are written
  `fileKey_verify`, `fileProof_verify`
                the written file's verifier, chain by chain, is the compiled verifier that `VC` runs
                for Test, and for the session
  `fileKey_laws`, `fileProof_laws`
                what OnBytes/TypedOracleCompiler/Joined/Top.lean asks of a file itself (`FileLaws`): the decision is
                local; the joining round is shared and coherent; the laws of the wire record; a
                symbol of the stored table that is written is read back. From hypotheses on numbers
                and on the bodies, each named.

Not claimed. Nothing on soundness, on an honest prover, or on whether the data are those of any
file.


-/
import Johnson.EntryRec.OkcFiles
import OnBytes.Maker.WholeLocal
import OnBytes.TypedOracleCompiler.Joined.Top

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies typedOracleCarrier OutOfDomainSampleQueryLayout wTC wBC vTC vBC cmsT cmsB xinB)

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd)

/-- **The key file as a written file.** -/
noncomputable def fileKey :
    FileW (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b)
      (chainsOf (ckP f) (DK.at a) tFk tJk t3k) (Seed × Ans) (oneExternalString (2 ^ a) SgX) where
  D := wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK
  t := .test
  wq := wqWhole (ckP f) K (chalP f K) (DK.at a) tFk tJk t3k silK runK
  embS := b.embT
  embP := fun z => z
  xin := fun _ => none
  embE := b.embE

/-- **The proof file as a written file.** -/
noncomputable def fileProof :
    FileW (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b)
      (chainsOf (ckP f) (DP.at a) tFp tJp t3p) (X × (Seed × Ans)) (oneExternalString (2 ^ a) SgX) where
  D := wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP
  t := .onl
  wq := wqWhole (ckP f) K (chalP f K) (DP.at a) tFp tJp t3p silP runP
  embS := b.embB
  embP := fun z => z
  xin := xinB (L := objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
  embE := b.embE

variable (S : OutOfDomainSampleQueryLayout 256 (K + 1)
    (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd
    (chainsOf (ckP f) (DK.at a) tFk tJk t3k).ann eL.aL)
  (p : _root_.Compile.Params)

/-- **The key file's verifier, chain by chain, is the compiled verifier that `VC` runs for
Test.** -/
theorem fileKey_verify (cm : Dig 256) (rec : Seed × Ans)
    (π : (fileKey f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b).Prf) :
    (fileKey f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b).verify p.sMT p.sFS
        (cmsT (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
          depthReq depthReqT depthReqL b) S cm rec) rec π =
      vTC (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b) S p cm rec π :=
  FileW.verify_eq _ p.sMT p.sFS _ rec π

/-- **The proof file's verifier is the compiled verifier that `VC` runs for the session.** -/
theorem fileProof_verify (cm : Dig 256) (x : X) (rec : Seed × Ans)
    (π : (fileProof f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b).Prf) :
    (fileProof f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b).verify p.sMT p.sFS
        (cmsB (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
          depthReq depthReqT depthReqL b) S cm rec) (x, rec) π =
      vBC (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b) S p cm x rec π :=
  FileW.verify_eq _ p.sMT p.sFS _ (x, rec) π

/-- **What is owed of the key file itself.** bK, wK: no round of it has more than K blocks, or more
than 64 bits of work; hb: what is written into a body is read back. -/
theorem fileKey_laws (bK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.entry.work ≤ 64) (hb : b.OK) :
    FileLaws (fileKey f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b) b.prjE where
  isLocal := wholeIOR_local (ckP f) (DK.at a) tFk tJk t3k silK runK
  laws := chainsOf_laws (ckP f) (DK.at a) tFk tJk t3k
  wire := wqWhole_okg_ckP f K (DK.at a) tFk tJk t3k silK runK bK wK
  prjE_emb := hb.E

/-- **What is owed of the proof file itself.** -/
theorem fileProof_laws (bP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.entry.work ≤ 64) (hb : b.OK) :
    FileLaws (fileProof f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b) b.prjE where
  isLocal := wholeIOR_local (ckP f) (DP.at a) tFp tJp t3p silP runP
  laws := chainsOf_laws (ckP f) (DP.at a) tFp tJp t3p
  wire := wqWhole_okg_ckP f K (DP.at a) tFp tJp t3p silP runP bP wP
  prjE_emb := hb.E

end

end OnBytes.Maker

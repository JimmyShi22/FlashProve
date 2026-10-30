-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/WrittenA.lean: the two written files of Johnson/Maker/Written.lean and the compiled
verifiers of the verifier with a record at the answers alone (`verifyAtFullKey`,
Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean).

`verifyAtFullKey` is `VC` with other lists and another request: the key's and the session's chains are handed
the root and the record's answers, not the seed; and the session's request holds the instance with
a fixed record r₀ in the record's place. Its two compiled verifiers for a whole file are `verifyOfflineProof` and
`verifyOnlineProof`.

  `fileKey_verifyA`    the key file of Written.lean, at the list with the answers alone, is what
                       `verifyAtFullKey` runs for Test: the written file itself does not turn
  `fileProofA`         the proof file as a written file whose request holds r₀ in the record's
                       place: `fileProof` with that one field turned
  `fileProofA_verify`  its verifier, chain by chain, is what `verifyAtFullKey` runs for the session
  `fileProofA_laws`    what OnBytes/TypedOracleCompiler/Joined/Top.lean asks of a file itself (`FileLaws`), from the
                       hypotheses of `fileProof_laws`

Not claimed. Nothing on soundness, on an honest prover, or on whether the data are those of any
file.


-/
import Johnson.Maker.Written
import Johnson.TypedOracleCompiler.RecCompile.CmsAns

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies typedOracleCarrier verifyOfflineProof verifyOnlineProof cmsTA cmsBA xinBA)

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
  (cA : Ans → List (Dig 256)) (r₀ : Seed × Ans) (p : _root_.Compile.Params)

/-- **The key file's verifier at the answers alone is the compiled verifier that `verifyAtFullKey` runs for
Test.** -/
theorem fileKey_verifyA (cm : Dig 256) (rec : Seed × Ans)
    (π : (fileKey f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b).Prf) :
    (fileKey f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b).verify p.sMT p.sFS
        (cmsTA (L := objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) cA cm
          rec.2) rec π =
      verifyOfflineProof (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
                       depthReqT depthReqL b) cA p cm rec π :=
  FileW.verify_eq _ p.sMT p.sFS _ rec π

/-- **The proof file as a written file whose request holds r₀ in the record's place.** -/
noncomputable def fileProofA :
    FileW (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b)
      (chainsOf (ckP f) (DP.at a) tFp tJp t3p) (X × (Seed × Ans)) (oneExternalString (2 ^ a) SgX) :=
  { fileProof f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b with
    xin := xinBA (L := objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) r₀ }

/-- **Its verifier is the compiled verifier that `verifyAtFullKey` runs for the session.** -/
theorem fileProofA_verify (cm : Dig 256) (x : X) (rec : Seed × Ans)
    (π : (fileProofA f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b r₀).Prf) :
    (fileProofA f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b r₀).verify p.sMT p.sFS
        (cmsBA (L := objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) cA cm
          rec.2) (x, rec) π =
      verifyOnlineProof (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
                      depthReqT depthReqL b) cA r₀ p cm x rec π :=
  FileW.verify_eq _ p.sMT p.sFS _ (x, rec) π

/-- **What is owed of that file itself.** -/
theorem fileProofA_laws
    (bP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.entry.work ≤ 64) (hb : b.OK) :
    FileLaws (fileProofA f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b r₀) b.prjE where
  isLocal := wholeIOR_local (ckP f) (DP.at a) tFp tJp t3p silP runP
  laws := chainsOf_laws (ckP f) (DP.at a) tFp tJp t3p
  wire := wqWhole_okg_ckP f K (DP.at a) tFp tJp t3p silP runP bP wP
  prjE_emb := hb.E

end

end OnBytes.Maker

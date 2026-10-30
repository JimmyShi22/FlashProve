-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/OpenedAtA.lean: the openings in the typing of a key file and of a proof file are as
the strict format asks, at the two written files themselves, where the verifier's messages give the
draws as read but for the digests drawn.

OnBytes/Maker/TypingAlike.lean has the four records of the strict format (`opened_atA`) at the
description and the wire record that OnBytes/Maker/ makes of a file's data.
Johnson/Maker/Written.lean and WrittenA.lean lay these into written files, `fileKey` and
`fileProofA`, whose verifiers are the compiled verifiers that `verifyAtFullKey` runs for Test and for the
session at `objF` and `wireF` (`fileKey_verifyA`, `fileProofA_verify`). This file says the four
records at these two, in the words of the fields `opened₁`, `opened₂`, `opened₃`, `openedE` of
`AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean), with that record's own premises on the three chains:
their values under fixed oracle functions g.

  `fileProofA_openedA`   the four records at the proof file `fileProofA`
                         (Johnson/Maker/WrittenA.lean): the proof file whose request holds a fixed
                         record r₀.
  `fileKey_openedA`      the four records at the key file.

The letter A at the end of these two names says: the draws but for the digests. In `fileProofA` it
says: the verifier at the answers alone.

The premises are those of `opened_atA`; none is shown here. Both proofs are the one term
`opened_atA`. `fileProofA_openedA` has no caller.

Not claimed. The other six fields of `AfterRuns`. Nothing on soundness.


-/
import Johnson.Maker.WrittenA
import OnBytes.Maker.TypingAlike
import OnBytes.TypedOracleCompiler.Joined.K.Left

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined Rom
open OnBytes.TwoLaws (LAlike DrawnAlike)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies)

section Proof
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK : WholeD) (W : Three.Whole)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd) (r₀ : Seed × Ans)

/-- the proof file, written, with r₀ in the record's place in the request -/
local notation "𝔉" => fileProofA f K a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP
  runP eL Z wL Bd depthReq depthReqT depthReqL b r₀
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFp tJp t3p

/-- **The four records at the proof file.** -/
theorem fileProofA_openedA (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) _)) (sb : ℕ)
    (cfg : ByteArray) (pF : TFp) (pJ : TJp) (p3 : T3p) (salt : ByteArray) (path : List ByteArray)
    (r : Proof.TailRead) (π : (𝔉).Prf)
    (h : typeFile (ckP f) a W tFp tJp t3p silP runP sb cfg pF pJ p3 salt path r = some π)
    (cms : List (Dig 256)) (x : X × (Seed × Ans)) (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂)
    (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π).det g = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a').det g = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a' b').det g = some e')
    (hshape : shapesFit a W = true) (hseal : sealBare W = true) (hsalts : saltsFit sb W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32) (hcfg : cfg.size = 32)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₁ ((𝒞).rho₁ (glue a' b' e').1)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₂ ((𝒞).rho₂ (glue a' b' e').1)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₃ ((𝒞).rho₃ (glue a' b' e').1))) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₁ (𝒞).A₁ (wire₁ (𝔉).wq) a'.2.1
        (rd₁ (𝔉).D (𝔉).wq x π a' b' e') (op₁ (𝔉).D π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₂ (𝒞).A₂ (wire₂ (𝔉).wq) b'.2.1
        (rd₂ (𝔉).D (𝔉).wq x π a' b' e') (op₂ (𝔉).D π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₃ (𝒞).A₃ (wire₃ (𝔉).wq) e'.2.1
        (rd₃ (𝔉).D (𝔉).wq x π a' b' e') (op₃ (𝔉).D π) ∧
      OpenedE (256 + 8 * sb) (𝔉).wq.maxDepth (𝔉).wq.ext (readE (𝔉).D (𝔉).wq x (glue a' b' e').1)
        π.ext :=
  opened_atA (ckP f) K (chalP f K) a W tFp tJp t3p silP runP g sb cfg pF pJ p3 salt path r π h
    x a' b' e' h₁ h₂ h₃ hshape hseal hsalts hrun hcfg hl₁ hl₂ hl₃ hd₁ hd₂ hd₃

end Proof

section Key
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (W : Three.Whole) (DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd)

/-- the key file, written -/
local notation "𝔉" => fileKey f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP
  eL Z wL Bd depthReq depthReqT depthReqL b
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFk tJk t3k

/-- **The four records at the key file.** -/
theorem fileKey_openedA (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) _)) (sb : ℕ) (cfg : ByteArray)
    (pF : TFk) (pJ : TJk) (p3 : T3k) (salt : ByteArray) (path : List ByteArray)
    (r : Proof.TailRead) (π : (𝔉).Prf)
    (h : typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg pF pJ p3 salt path r = some π)
    (cms : List (Dig 256)) (x : Seed × Ans) (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂)
    (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π).det g = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a').det g = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a' b').det g = some e')
    (hshape : shapesFit a W = true) (hseal : sealBare W = true) (hsalts : saltsFit sb W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32) (hcfg : cfg.size = 32)
    (hl₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList)
    (hl₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList)
    (hl₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList)
    (hd₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₁ ((𝒞).rho₁ (glue a' b' e').1)))
    (hd₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₂ ((𝒞).rho₂ (glue a' b' e').1)))
    (hd₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
      (drawnT (ckP f) (WholeD.of a W).ds₃ ((𝒞).rho₃ (glue a' b' e').1))) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₁ (𝒞).A₁ (wire₁ (𝔉).wq) a'.2.1
        (rd₁ (𝔉).D (𝔉).wq x π a' b' e') (op₁ (𝔉).D π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₂ (𝒞).A₂ (wire₂ (𝔉).wq) b'.2.1
        (rd₂ (𝔉).D (𝔉).wq x π a' b' e') (op₂ (𝔉).D π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) (𝒞).c₃ (𝒞).A₃ (wire₃ (𝔉).wq) e'.2.1
        (rd₃ (𝔉).D (𝔉).wq x π a' b' e') (op₃ (𝔉).D π) ∧
      OpenedE (256 + 8 * sb) (𝔉).wq.maxDepth (𝔉).wq.ext (readE (𝔉).D (𝔉).wq x (glue a' b' e').1)
        π.ext :=
  opened_atA (ckP f) K (chalP f K) a W tFk tJk t3k silK runK g sb cfg pF pJ p3 salt path r π h
    x a' b' e' h₁ h₂ h₃ hshape hseal hsalts hrun hcfg hl₁ hl₂ hl₃ hd₁ hd₂ hd₃

end Key

end OnBytes.Maker

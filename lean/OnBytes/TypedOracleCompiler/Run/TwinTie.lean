-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinTie.lean.
Run/TwinTie.lean: THE TWIN IS THE COMPILED VERIFIER: verifyT (Run/TwinDefs.lean) =
Compile.Batch.verifyOneProtocol AT THE PROTOCOL OF THE SKELETON, AS TREES OF QUERIES, FOR EVERY SKELETON,
WIRING AND AMBIENT INTERFACE. One statement (Run.Twin.Spec.verifyT_eq) and its proof, function by
function; the functions without queries: Run/TwinTiePure.lean.
    Spec.verifyT_eq     verifyT L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
                        verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π
HOW TO USE IT. At a run the first two arguments are WRITTEN OUT (the interface's two fields as plain
terms): reading a field of the interface would build it, and with it its Test's shape.
WHAT IS NOT SAID. Nothing on what the evaluator builds or how long a run takes. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.TwinTie
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
import OnBytes.TypedOracleCompiler.Run.TwinDefs
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem lateT_eq (i : ℕ) (x : Option X) : lateT L.late i x = lateInstancePart L i x := rfl

theorem chainT_eq (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
        (rts : List (Dig lam)) (pls : Plains (up S)),
      chainT L.early L.late t cms x salt rtreq S A W embP i ph rts pls =
        recomputeChain t cms x salt rtreq (up S) A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      have ih := chainT_eq t cms x salt rtreq S A W
      simp only [chainT, ih, lateT_eq]
      rfl

variable {Y : Type} {E : ExtSpec}

theorem chainQT_eq (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    chainQT L.early L.late t P wq embP xin cms x π = recomputeChainOfProof t P.up wq embP xin cms x π :=
  chainT_eq t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0 .first π.roots π.plains

theorem forestsOfT_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    forestsOfT P wq embS embE cms x π ρ rts = forestsOf P.up wq embS embE cms x π ρ rts := by
  unfold forestsOfT forestsOf
  rw [forestsT_eq I X lam K L P.S P.ann wq.sh embS rts, effPlainsT_eq lam P.S P.ann rts π.plains]
  dsimp only [PS.up]
  cases forestsB (up P.S) P.ann wq.sh embS rts
      (fun p =>
        @decide (p ∈ P.reads x ρ (effPlains (up P.S) P.ann rts π.plains))
          (@Finset.decidableMem _ wq.decO _ _)) π.opens <;>
    cases forestExt wq.ext embE cms
        (fun p => @decide (p ∈ P.extReads x ρ) (@Finset.decidableMem _ wq.ext.dec _ _)) π.ext
      <;> rfl

theorem afterFT_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam)
    (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    afterFT P wq depthReq x π ρ rts ph Fs s = afterF P.up wq depthReq x π ρ rts ph Fs s := by
  unfold afterFT afterF
  rw [mkTrT_eq lam K P.S P.ann wq.sh rts π.plains ρ π.opens]

theorem afterBOT_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterBOT P wq embS embE depthReq cms x π ρ rts ph =
      checkPrunedOpenings P.up wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterBOT checkPrunedOpenings
  rw [forestsOfT_eq]
  simp only [afterFT_eq]
  cases forestsOf P.up wq embS embE cms x π ρ rts <;> rfl

theorem strictBT_eq (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    strictBT sMT sFS P wq depthReq x π ρ rts ph =
      proofHasStrictFormat sMT sFS P.up wq depthReq x π ρ rts ph := by
  unfold strictBT proofHasStrictFormat
  rw [countT_eq lam P.S rts, strictST_eq lam K sMT P.S P.ann wq.sh rts,
    effPlainsT_eq lam P.S P.ann rts π.plains]

/-- THE TIE. -/
def Spec.verifyT_eq : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag)
      (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyT L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π

theorem verifyT_eq : Spec.verifyT_eq := by
  intro I X lam K L Y E sMT sFS t P wq embS embP xin embE depthReq cms x π
  unfold verifyT verifyOneProtocol
  rw [chainQT_eq]
  refine congrArg _ (funext fun r => ?_)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · rfl
  · simp only [strictBT_eq, afterBOT_eq]

end TypedOracleCompiler.Run.Twin

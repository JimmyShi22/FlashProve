-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxDet.lean: the lax compiled verifier (Compile/Batch/Verifier.lean: verifyB: the
chain, then afterB: no test of the strict format; each opened position climbed alone along its whole
path) as a function of the oracle functions: verifyB_det. Definitions and equations without a
hypothesis. General in the protocol Q. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.
Why. Run/VerifyDet.lean has the plain form of the strict verifier verifyOneProtocol alone. VerifyB's text,
the judges judgeEL and the ties at H_b have the lax one.
  runCheckF g c  one check: the leaf's answer, climbed along c.path by the vertex oracle, is c.root
  afterBF g Q wq …  what follows the chain, clause by clause as afterB has them: checksB and
      checksExt are some; at most nOpen checks; each well formed and of depth ≤ maxDepth; every
      check says yes; the request tree's check if the chain has joined (reqPartF); the local
      verifier's decision at the transcript mkTr
  verifyLF g t Q wq …  the chain's plain form chainF, then afterBF
  runCheck_detF, runChecks_detF, afterB_det, verifyB_det  (runCheck c).det g = runCheckF g c;
      (runChecks cs).det g = cs.all (runCheckF g); (afterB …).det g = afterBF g …; (verifyB t Q wq
      embS embP xin embE depthReq cms x π).det g = verifyLF g t Q wq embS embP xin embE depthReq cms
      x π
What is not said. Nothing on soundness: equations between two ways of computing one truth value. The
values agree; the number of calls of g need not. verifyLF is no form to run (it has protocols and
shapes as parameters): Run/LaxThin.lean: verifyLX.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))

/-- one check, as a function of the oracle functions -/
def runCheckF (c : Check lam L) : Bool :=
  decide (climbF (nodeF g) c.path c.j (g TypedOracleCompiler.Compile.Batch.OracleName.leaf c.inp :
      Dig lam) = c.root)

variable {Y : Type} {E : ExtSpec}

/-- What follows the chain. -/
def afterBF (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  haveI := wq.ext.dec
  match checksB Q.loc.shape Q.ann wq.sh embS rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains))) π.opens,
    TypedOracleCompiler.Compile.Batch.checksExt wq.ext embE cms (fun p => decide (p ∈ Q.loc.extReads x ρ))
        π.ext wq.ext.all with
  | some a, some b =>
      if (a ++ b).length ≤ wq.nOpen ∧
          (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then
        (a ++ b).all (runCheckF g) && reqPartF g depthReq π ph &&
          Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens)
      else false
  | _, _ => false

/-- THE LAX COMPILED VERIFIER OF ONE SLOT AS A FUNCTION OF THE ORACLE FUNCTIONS. -/
def verifyLF (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) : Bool :=
  match chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) => afterBF g Q wq embS embE depthReq cms x π ρ rts ph

/-! ### The ties -/

theorem runCheck_detF (c : Check lam L) :
    (TypedOracleCompiler.Compile.Batch.runCheck (K := K) c).det g = runCheckF g c := by
  simp only [TypedOracleCompiler.Compile.Batch.runCheck, det_bind', det_pure', det_askV]
  exact congrArg (fun r => decide (r = c.root))
    (Evaluates.climbM (_root_.Compile.Batch.Seed.evalO g) (qN := hashTreeNode (L := L) (K := K))
        (hN := nodeF g)
      (fun _ _ => rfl) c.path c.j _)

theorem runChecks_detF : ∀ cs : List (Check lam L),
    (TypedOracleCompiler.Compile.Batch.runChecks (K := K) cs).det g = cs.all (runCheckF g)
  | [] => rfl
  | c :: cs => by
      simp only [TypedOracleCompiler.Compile.Batch.runChecks, det_bind', det_pure', runCheck_detF,
          runChecks_detF cs,
        List.all_cons]

theorem afterB_det (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (afterB Q wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBF g Q wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterB afterBF
  split
  · rename_i a b ha hb
    simp only [ha, hb]
    split_ifs
    · unfold reqPartF
      cases ph.slotVal with
      | none =>
        simp only [det_bind', det_pure', runChecks_detF]
      | some c =>
        simp only [det_bind', det_pure', runChecks_detF, reqCheck_det]
    · rfl
  · rename_i hn
    split
    · rename_i a b ha hb
      exact (hn a b ha hb).elim
    · rfl

/-- THE RUN OF THE LAX VERIFIER UNDER ORACLE FUNCTIONS. -/
theorem verifyB_det (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyB t Q wq embS embP xin embE depthReq cms x π).det g =
      verifyLF g t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyB verifyLF recomputeChainOfProof
  rw [OComp.det_bind, chainB_det]
  cases chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r => exact afterB_det g Q wq embS embE depthReq cms x π _ _ _

end

end TypedOracleCompiler.Run

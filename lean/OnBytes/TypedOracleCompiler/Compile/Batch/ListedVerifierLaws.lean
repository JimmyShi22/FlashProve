-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifierLaws.lean: the verifier along lists
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean, verifyBSL) is the compiled verifier of one slot
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol), as a tree of queries, under premises on the
four things that its caller hands over.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The premises.
  hO: in the trees that a round's wiring lists, an opening of the prover's oracles stands only at
    listed leaves (ListedOK, ListedStrict.lean).
  hE: an opening of the external oracles stands only at listed positions.
  hA: the wire's list of all positions of the external oracles holds every position.
  hR: at all verifier's messages and plain parts, mkRd gives, tree by tree, the leaves whose
    positions the protocol reads, rising (LeavesOK, ListedForests.lean).
  hRE: at all verifier's messages, mkRdE gives the wire's list of all positions, filtered by what
    the protocol reads.

Main definitions. isReadOf, isReadEOf: "is this position read", as verifyOneProtocol asks it.
Main theorems. strictBBL_eq, forestsOfL_eq, afterFL_eq, afterBOL_eq; verifyBSL_eq.

Limits. That the premises hold of any lists is not shown here (at the description of a whole file:
OnBytes/Maker/ListedWholeTop.lean). No oracle functions come in: the two sides are one tree of
queries. Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifier
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedExtLaws
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A member of l is in l filtered by f exactly if f says yes. -/
theorem contains_filter {α : Type} [DecidableEq α] (l : List α) (f : α → Bool) (p : α)
    (h : p ∈ l) : (l.filter f).contains p = f p := by
  by_cases hf : f p = true
  · rw [hf]
    exact List.elem_eq_true_of_mem (List.mem_filter.2 ⟨h, hf⟩)
  · have hf' : f p = false := Bool.eq_false_iff.2 hf
    rw [hf']
    cases hc : (l.filter f).contains p with
    | false => rfl
    | true => exact absurd (List.mem_filter.1 (List.mem_of_elem_eq_true hc)).2 hf

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)

/-- Is this position of the prover's oracles read: as verifyOneProtocol asks it. -/
def isReadOf (x : Y) (ρ : Rho Q.loc.shape) (pl : Plains Q.loc.shape) : OPos Q.loc.shape → Bool :=
  haveI := wq.decO
  fun p => decide (p ∈ Q.loc.reads x ρ pl)

/-- Is this position of the external oracles read: as verifyOneProtocol asks it. -/
def isReadEOf (x : Y) (ρ : Rho Q.loc.shape) : E.Pos → Bool :=
  haveI := wq.ext.dec
  fun p => decide (p ∈ Q.loc.extReads x ρ)

variable (sMT sFS : ℕ) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves)
  (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos) (ρ : Rho Q.loc.shape)
  (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

/-- The strict format along the lists is the strict format. -/
theorem strictBBL_eq (hO : ListedOK Q.loc.shape Q.ann wq.sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) (hA : ∀ p, p ∈ wq.ext.all)
    (hL : LeavesOK Q.loc.shape Q.ann wq.sh
      (isReadOf Q wq x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) rd)
    (hRE : rdE = wq.ext.all.filter (isReadEOf Q wq x ρ)) :
    strictBBL sMT sFS Q wq.sh wq.ext.less depthReq π own listed rd rdE rts ph =
      proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph := by
  have e1 := strictSBL_eq sMT Q.loc.shape Q.ann wq.sh rts
    (isReadOf Q wq x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) π.opens own rd hO
    (readsOK_of_leavesOK Q.loc.shape Q.ann wq.sh _ rd hL)
  have e0 : (letI := wq.ext.dec; fun p => rdE.contains p) = isReadEOf Q wq x ρ := by
    letI := wq.ext.dec
    funext p
    rw [hRE]
    exact contains_filter wq.ext.all (isReadEOf Q wq x ρ) p (hA p)
  have e2 := strictExtL_eq sMT wq.ext (isReadEOf Q wq x ρ) π.ext listed hE hA
  show (decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape rts) &&
      strictSBL sMT Q.loc.shape Q.ann wq.sh rts π.opens own rd &&
      strictExtL sMT (letI := wq.ext.dec; fun p => rdE.contains p) π.ext listed &&
      decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
      (ph.slotVal.isSome || π.rsalt.isEmpty)) = _
  rw [e1, e0, e2]
  rfl

variable (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
  (cms : List (Dig lam))

/-- The checks made along the lists of what is read are the checks. -/
theorem forestsOfL_eq
    (hL : LeavesOK Q.loc.shape Q.ann wq.sh
      (isReadOf Q wq x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) rd)
    (hRE : rdE = wq.ext.all.filter (isReadEOf Q wq x ρ)) :
    forestsOfL Q wq.sh wq.ext.less embS embE cms π rd rdE rts =
      forestsOf Q wq embS embE cms x π ρ rts := by
  have e1 := forestsBL_eq Q.loc.shape Q.ann wq.sh embS rts
    (isReadOf Q wq x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) π.opens rd hL
  have e2 := forestExtL_eq wq.ext embE cms (isReadEOf Q wq x ρ) π.ext rdE hRE
  unfold forestsOfL
  rw [e1, e2]
  rfl

/-- Behind the checks the two verifiers are one text. -/
theorem afterFL_eq (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    afterFL (K := K) Q wq.sh wq.ext.less depthReq x π ρ rts ph Fs s =
      afterF Q wq depthReq x π ρ rts ph Fs s := rfl

/-- Behind the strict format the verifier along the lists is the compiled verifier. -/
theorem afterBOL_eq
    (hL : LeavesOK Q.loc.shape Q.ann wq.sh
      (isReadOf Q wq x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) rd)
    (hRE : rdE = wq.ext.all.filter (isReadEOf Q wq x ρ)) :
    afterBOL Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embE depthReq cms x π rd rdE ρ rts ph =
      checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterBOL checkPrunedOpenings
  rw [forestsOfL_eq Q wq x π rd rdE ρ rts embS embE cms hL hRE]
  rfl

/-- **The verifier along the lists is the compiled verifier**, as a tree of queries. -/
theorem verifyBSL_eq (t : Tag) (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t))
    (xin : Y → Option X) (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos)
    (hO : ListedOK Q.loc.shape Q.ann wq.sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) (hA : ∀ p, p ∈ wq.ext.all)
    (hR : ∀ ρ pl, LeavesOK Q.loc.shape Q.ann wq.sh (isReadOf Q wq x ρ pl) (mkRd x ρ pl))
    (hRE : ∀ ρ, mkRdE x ρ = wq.ext.all.filter (isReadEOf Q wq x ρ)) :
    verifyBSL sMT sFS t Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embP xin embE depthReq cms
        x π own listed mkRd mkRdE =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyBSL verifyOneProtocol recomputeChainOfProof
  refine congrArg _ (funext fun r => ?_)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · rfl
  · show (if strictBBL sMT sFS Q wq.sh wq.ext.less depthReq π own listed
          (mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) (mkRdE x ρ) rts ph = true then
        afterBOL Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embE depthReq cms x π
          (mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) (mkRdE x ρ) ρ rts ph
      else pure false) = _
    rw [strictBBL_eq Q wq sMT sFS depthReq x π own listed _ _ ρ rts ph hO hE hA (hR ρ _) (hRE ρ),
      afterBOL_eq Q wq depthReq x π _ _ ρ rts ph embS embE cms (hR ρ _) (hRE ρ)]

end

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.verifyBSL_eq

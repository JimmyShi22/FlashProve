-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/FixInstance.lean: the compiled verifier of one slot, as OnBytes/TypedOracleCompiler/ has it (a second form
of the compiler's verifier side, beside the library's own), at a protocol with its instance fixed.

A protocol reads its instance in three places: the positions that it reads in the external strings,
the positions that it reads in its own oracles, and its decision. `InteractiveOracleProof.fixAt Q x` is the protocol
without an instance (its instance type is `Unit`) that reads and decides as Q does at x. It has Q's
rounds, so an argument string and a wire for Q are an argument string and a wire for it.

Main definitions: `fixAt`, `fixB`.
Main theorems. `verifyBS_fix`: the compiled verifier at Q and the instance x is, term for term, the
compiled verifier at `fixB Q x` and the instance `()`, if the latter's first query is handed what
Q's is handed at x.

What is not claimed. Nothing on soundness: a protocol with its instance fixed is another protocol,
and a statement on it for one x says nothing on Q at another. For proofs only; the program does not
import this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace OnBytes.K

open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The protocol without an instance that reads and decides as Q does at x. -/
def fixAt {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (x : Y) : InteractiveOracleProof Unit E where
  shape := Q.shape
  blinded := Q.blinded
  extReads := fun _ => Q.extReads x
  reads := fun _ => Q.reads x
  accept := fun _ => Q.accept x

/-- The same for a protocol with an annotation of its rounds. -/
def fixB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (x : Y) : BatchInteractiveOracleProof Unit E :=
  ⟨fixAt Q.loc x, Q.ann⟩

/-- A wire for Q as a wire for Q with its instance fixed. -/
def fixW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (x : Y) :
    ProtocolQueryLayout lam K (fixB Q x) :=
  ⟨wq.sh, wq.ext, wq.decO, wq.nOpen, wq.maxDepth⟩

/-- An argument string for Q as one for Q with its instance fixed. -/
def fixP {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (π : OneProtocolProof lam Q) (x : Y) :
    OneProtocolProof lam (fixB Q x) :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path, π.rsalt⟩

section Steps
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
  (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

theorem chainQB_fix :
    recomputeChainOfProof t (fixB Q x) (fixW wq x) embP (fun _ => xin x) cms () (fixP π x) =
      recomputeChainOfProof t Q wq embP xin cms x π := rfl

theorem strictBB_fix (sMT sFS : ℕ) :
    proofHasStrictFormat sMT sFS (fixB Q x) (fixW wq x) depthReq () (fixP π x) ρ rts ph =
      proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph := rfl

theorem forestsOf_fix :
    forestsOf (L := L) (fixB Q x) (fixW wq x) embS embE cms () (fixP π x) ρ rts =
      forestsOf Q wq embS embE cms x π ρ rts := rfl

theorem afterF_fix (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    afterF (fixB Q x) (fixW wq x) depthReq () (fixP π x) ρ rts ph Fs s =
      afterF Q wq depthReq x π ρ rts ph Fs s := rfl

theorem afterBO_fix :
    checkPrunedOpenings (fixB Q x) (fixW wq x) embS embE depthReq cms () (fixP π x) ρ rts ph =
      checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph := by
  unfold checkPrunedOpenings
  rw [forestsOf_fix]
  rfl

/-- **The compiled verifier of one slot at Q and x is the one at Q with x fixed.** -/
theorem verifyBS_fix (sMT sFS : ℕ) :
    verifyOneProtocol sMT sFS t (fixB Q x) (fixW wq x) embS embP (fun _ => xin x) embE depthReq cms ()
        (fixP π x) =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyOneProtocol
  rw [chainQB_fix]
  congr 1
  funext r
  cases r with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    show (if proofHasStrictFormat sMT sFS (fixB Q x) (fixW wq x) depthReq () (fixP π x) ρ rts ph = true then
        checkPrunedOpenings (fixB Q x) (fixW wq x) embS embE depthReq cms () (fixP π x) ρ rts ph
      else pure false) = _
    rw [strictBB_fix, afterBO_fix]

end Steps

end OnBytes.K

#print axioms OnBytes.K.verifyBS_fix

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TwoCarryFix.lean: two laws of the compiled verifier of one slot without the strict format,
as OnBytes/TypedOracleCompiler/ has it: at a protocol with its instance fixed; and at another list of outer roots
that agrees with the first at the places that the wiring reads.

`verifyB` (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) recomputes the chain and goes on with `afterB`:
the checks of the openings, each along its own path, and the decision. OnBytes/K/FixInstance.lean
has, for the verifier with the strict format, that the verifier at a protocol Q and an instance x is
the verifier at Q with x fixed. For proofs only; the program does not import this file.

Main theorems.
 `afterB_fix`, `verifyB_fix`   the same for `afterB` and `verifyB`.
 `checksExt_cms`, `afterB_cms` the checks of the openings in the external trees, and so `afterB`,
    are the same terms at two lists of outer roots cms, cms', if the wiring names trees below a
    number n alone and the two lists have the same member, or the same fixed value where there is
    none, at every place below n. Behind the chain the list is read at the trees' numbers and
    nowhere else.

What is not claimed. Nothing on the chain, whose first query holds the whole list. Nothing on the
verifier with the strict format. Nothing on soundness.


-/
import OnBytes.K.FixInstance

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Carry
open _root_.Compile TypedOracleCompiler.Iop Rom OnBytes.K
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The checks of the openings in the external trees read the list of outer roots at the trees'
numbers alone. -/
theorem checksExt_cms {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms cms' : List (Dig lam)) (n : ℕ) (hw : ∀ p, we.which p < n)
    (hc : ∀ t, t < n → cms'.getD t default = cms.getD t default) (isRead : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos, checksExt we emb cms' isRead g ps = checksExt we emb cms isRead g ps
  | [] => rfl
  | p :: ps => by
      unfold checksExt
      rw [checksExt_cms we emb cms cms' n hw hc isRead g ps, hc _ (hw p)]

section
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
  (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

/-- What follows the chain is the same at two lists of outer roots that agree below n, if the wiring
names trees below n alone. -/
theorem afterB_cms (cms' : List (Dig lam)) (n : ℕ) (hw : ∀ p, wq.ext.which p < n)
    (hc : ∀ t, t < n → cms'.getD t default = cms.getD t default) :
    afterB (L := L) (K := K) Q wq embS embE depthReq cms' x π ρ rts ph =
      afterB (L := L) (K := K) Q wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterB
  rw [checksExt_cms wq.ext embE cms cms' n hw hc]

/-- What follows the chain, at Q with x fixed. -/
theorem afterB_fix :
    afterB (L := L) (K := K) (fixB Q x) (fixW wq x) embS embE depthReq cms () (fixP π x) ρ rts ph =
      afterB Q wq embS embE depthReq cms x π ρ rts ph := rfl

/-- **The compiled verifier of one slot without the strict format, at Q and x, is the one at Q with
x fixed**, if the latter's first query is handed what Q's is handed at x. -/
theorem verifyB_fix :
    verifyB t (fixB Q x) (fixW wq x) embS embP (fun _ => xin x) embE depthReq cms () (fixP π x) =
      verifyB t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyB
  rw [chainQB_fix]
  congr 1
  funext r
  cases r with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    exact afterB_fix Q wq embS embE depthReq cms x π ρ rts ph

end

end TypedOracleCompiler.Compile.Batch.Carry

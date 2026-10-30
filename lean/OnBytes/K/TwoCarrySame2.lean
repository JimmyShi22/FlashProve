-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TwoCarrySame2.lean: the law of OnBytes/K/TwoCarrySame.lean, "the lax compiled verifier
hangs on the fields that it reads", for two protocols on two kinds of external strings and two
wirings with two numbers of blocks, where the kinds and the numbers are equal by proofs.

In `SameRun` the two protocols share the kind E of external strings, and the two wirings the number
K of blocks of an answer. A written object may have these as other terms: a depth that is equal to
the description's by a theorem, a numeral for K. E and K stand in the types of protocol, wiring,
typed string and oracle functions, so the two sides cannot then be written into `SameRun`. Here both
are letters on each side. For proofs only; the program does not import this file.

Main definition: `SameRun2`.
Main theorems.
 `SameRun2.same`  at one E and one K it is `SameRun`.
 `verifyB_same2`  under `SameRun2`, E' = E and K' = K, at maps of external symbols and at oracle
                  functions that agree: the two verifiers' runs return the same.
 `readBlocks_cast` the oracle functions that an encoding, carried along an equation of the numbers
                  of blocks, reads out of an oracle agree with those of the encoding.

What is not claimed. Nothing on soundness. That any two protocols have `SameRun2`.


-/
import OnBytes.K.TwoCarrySame
import Rom.Cache
import Rom.Prefix

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Carry
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {t : Tag} {Y : Type}

/-- `SameRun` with two kinds of external strings and two numbers of blocks. -/
structure SameRun2 {E' E : ExtSpec} {K' K : ℕ} (Q' : BatchInteractiveOracleProof Y E') (Q : BatchInteractiveOracleProof Y E)
    (wq' : ProtocolQueryLayout lam K' Q') (wq : ProtocolQueryLayout lam K Q)
    (embS' : (p : OPos Q'.loc.shape) → OSym Q'.loc.shape p → Body L)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP' : PlainPart Q'.loc.shape Q'.ann → PlainPart (shapeOf L t) (annOf L t))
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t))
    (π' : OneProtocolProof lam Q') (π : OneProtocolProof lam Q) : Prop where
  /-- the protocol: its rounds, their marks, what it reads, its decision -/
  shape : Q'.loc.shape = Q.loc.shape
  ann : HEq Q'.ann Q.ann
  extReads : HEq Q'.loc.extReads Q.loc.extReads
  reads : HEq Q'.loc.reads Q.loc.reads
  accept : HEq Q'.loc.accept Q.loc.accept
  /-- the wiring -/
  sh : HEq wq'.sh wq.sh
  ext : HEq wq'.ext wq.ext
  nOpen : wq'.nOpen = wq.nOpen
  maxDepth : wq'.maxDepth = wq.maxDepth
  /-- how symbols and plain parts are written into queries -/
  embS : HEq embS' embS
  embP : HEq embP' embP
  /-- the typed string -/
  salt : π'.salt = π.salt
  roots : π'.roots = π.roots
  plains : HEq π'.plains π.plains
  opens : HEq π'.opens π.opens
  pext : HEq π'.ext π.ext
  rtreq : π'.rtreq = π.rtreq
  slot : π'.slot = π.slot
  path : π'.path = π.path
  rsalt : π'.rsalt = π.rsalt

/-- At one kind of external strings and one number of blocks it is `SameRun`. -/
theorem SameRun2.same {E : ExtSpec} {K : ℕ} {Q' Q : BatchInteractiveOracleProof Y E} {wq' : ProtocolQueryLayout lam K Q'}
    {wq : ProtocolQueryLayout lam K Q} {embS' : (p : OPos Q'.loc.shape) → OSym Q'.loc.shape p → Body L}
    {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embP' : PlainPart Q'.loc.shape Q'.ann → PlainPart (shapeOf L t) (annOf L t)}
    {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)}
    {π' : OneProtocolProof lam Q'} {π : OneProtocolProof lam Q}
    (h : SameRun2 (t := t) Q' Q wq' wq embS' embS embP' embP π' π) :
    SameRun (t := t) Q' Q wq' wq embS' embS embP' embP π' π :=
  ⟨h.shape, h.ann, h.extReads, h.reads, h.accept, h.sh, eq_of_heq h.ext, h.nOpen, h.maxDepth,
    h.embS, h.embP, h.salt, h.roots, h.plains, h.opens, eq_of_heq h.pext, h.rtreq, h.slot, h.path,
    h.rsalt⟩

/-- **The two runs return the same.** -/
theorem verifyB_same2 {E' E : ExtSpec} (hE : E' = E) {K' K : ℕ} (hK : K' = K)
    {Q' : BatchInteractiveOracleProof Y E'} {Q : BatchInteractiveOracleProof Y E} {wq' : ProtocolQueryLayout lam K' Q'} {wq : ProtocolQueryLayout lam K Q}
    {embS' : (p : OPos Q'.loc.shape) → OSym Q'.loc.shape p → Body L}
    {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embP' : PlainPart Q'.loc.shape Q'.ann → PlainPart (shapeOf L t) (annOf L t)}
    {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)}
    {π' : OneProtocolProof lam Q'} {π : OneProtocolProof lam Q}
    (h : SameRun2 (t := t) Q' Q wq' wq embS' embS embP' embP π' π) (xin : Y → Option X)
    (embE' : E'.Sym → Body L) (embE : E.Sym → Body L) (hemb : HEq embE' embE) (depthReq : ℕ)
    (cms : List (Dig lam)) (x : Y) (g' : Fam (typedOracleFamily lam K' L)) (g : Fam (typedOracleFamily lam K L))
    (hg : HEq g' g) :
    (verifyB t Q' wq' embS' embP' xin embE' depthReq cms x π').det g' =
      (verifyB t Q wq embS embP xin embE depthReq cms x π).det g := by
  subst hE hK
  obtain rfl := eq_of_heq hemb
  obtain rfl := eq_of_heq hg
  rw [verifyB_same h.same xin embE' depthReq cms x]

/-- The oracle functions of an encoding that is carried along an equation of the numbers of blocks.
-/
theorem readBlocks_cast {K K' n : ℕ} (hK : K = K') (m : OracleCoding (typedOracleFamily lam K L) n)
    (o : Fam (rom n)) : HEq (readBlocks (hK ▸ m) o) (readBlocks m o) := by
  subst hK
  rfl

end TypedOracleCompiler.Compile.Batch.Carry

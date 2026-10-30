-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TwoCarrySame.lean: the lax compiled verifier of one slot (`verifyB`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) hangs on the fields of protocol, wiring and typed string
that it reads, and on nothing else.

Two protocols may be alike in all that the compiled verifier reads and still not be one term: their
lists of rounds may be equal by a proof and not by unfolding, and the field `blinded`, which the
verifier never reads, may differ. `SameRun` lists, field by field, what must agree; where a field's
type hangs on the list of rounds, the agreement is an equation between terms of two types (`HEq`).
For proofs only; the program does not import this file.

Main definition: `SameRun`.
Main theorem. `verifyB_same`: under `SameRun` the two verifiers are one program.

What is not claimed. Nothing on soundness. That any two protocols have `SameRun`.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Carry
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {t : Tag} {Y : Type} {E : ExtSpec}

/-- **What the lax compiled verifier reads of protocol, wiring, maps and typed string**, at two of
each: all agree. The field `blinded` of a protocol is not among them; nor is the wiring's way to
decide whether two positions are equal: there is one answer. -/
structure SameRun (Q' Q : BatchInteractiveOracleProof Y E) (wq' : ProtocolQueryLayout lam K Q') (wq : ProtocolQueryLayout lam K Q)
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
  ext : wq'.ext = wq.ext
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
  pext : π'.ext = π.ext
  rtreq : π'.rtreq = π.rtreq
  slot : π'.slot = π.slot
  path : π'.path = π.path
  rsalt : π'.rsalt = π.rsalt

set_option smartUnfolding false in
/-- **The lax compiled verifier hangs on these alone.** -/
theorem verifyB_same {Q' Q : BatchInteractiveOracleProof Y E} {wq' : ProtocolQueryLayout lam K Q'} {wq : ProtocolQueryLayout lam K Q}
    {embS' : (p : OPos Q'.loc.shape) → OSym Q'.loc.shape p → Body L}
    {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embP' : PlainPart Q'.loc.shape Q'.ann → PlainPart (shapeOf L t) (annOf L t)}
    {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)}
    {π' : OneProtocolProof lam Q'} {π : OneProtocolProof lam Q}
    (h : SameRun (t := t) Q' Q wq' wq embS' embS embP' embP π' π) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) :
    verifyB t Q' wq' embS' embP' xin embE depthReq cms x π' =
      verifyB t Q wq embS embP xin embE depthReq cms x π := by
  obtain ⟨⟨s', bl', er', rd', ac'⟩, A'⟩ := Q'
  obtain ⟨⟨s, bl, er, rd, ac⟩, A⟩ := Q
  obtain ⟨sh', ext', dec', nO', mD'⟩ := wq'
  obtain ⟨sh, ext, dec, nO, mD⟩ := wq
  obtain ⟨salt', roots', plains', opens', pext', rtreq', slot', path', rsalt'⟩ := π'
  obtain ⟨salt, roots, plains, opens, pext, rtreq, slot, path, rsalt⟩ := π
  obtain ⟨hs, hA, her, hrd, hac, hsh, hext, hn, hm, hS, hP, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  dsimp only at hs hA her hrd hac hsh hext hn hm hS hP h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst hs
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq her
  obtain rfl := eq_of_heq hrd
  obtain rfl := eq_of_heq hac
  obtain rfl := eq_of_heq hsh
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  subst hext hn hm h1 h2 h5 h6 h7 h8 h9
  obtain rfl : dec' = dec := Subsingleton.elim _ _
  rfl

end TypedOracleCompiler.Compile.Batch.Carry

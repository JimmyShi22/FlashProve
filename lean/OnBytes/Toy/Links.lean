-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Toy/Links.lean: a chain of links, a small test protocol of the C++ library
(blocks/toy/segments.h). The number of links is read from the parameter bytes.

It is the smallest use of the frame in which a request's sub-proofs follow each other
(OnBytes/Iop/Req.lean). Each link is a product of two vectors, and the product of one link is a
factor of the next. The prover knows x_1 and b_1, b_2, .. over the base field. With c_m = x_m b_m
entry by entry and x_(m+1) = c_m it proves that the committed products are right. There is no model,
no key, no table and no reply. The chain's statement is empty.

Each link runs the frame's first message (SEND, or the code switch from the link before), ZERO (the
verifier draws a point), PSC (the sumcheck at that point, OnBytes/Iop/Psc.lean), and the frame's
closing (BAT, FOLD). After the last link the frame runs the last proximity test.

A vector fills the lower half of a row, and the rows that this file makes read only that half of a
main row (vectorOfRow). In segments.h the upper half holds zeros and, at its end, the pad of the
sample of an oracle message that has no mask row, such as the message of c.

The parameter bytes are an input. They hold the plan and the items "codes" and "the chain of
links".

Main definitions: Toy.linkVerify, Toy.linksVerify, Toy.LinksPublic, Toy.linksChain, Toy.links.

What is not claimed: that the plan in the parameter bytes reaches a security level; anything on what
a proof file hides; that the shape in the parameter bytes is that of the chain of links. This file
does not test how many rows a link's oracle messages have, nor that a link has one moment, and a
row's number is read modulo the table's 2^rowBits rows (vectorOfRow). The C++ verifier
(segments_verify_file) makes plan, codes and shape from the run's public file; here
OnBytes/Shell/Toys.lean does that and then calls Toy.links. No theorem is stated here.
-/
import OnBytes.Result
import OnBytes.Chain.Reader
import OnBytes.Params.Chains
import OnBytes.Iop.Req
import OnBytes.Iop.Psc

namespace OnBytes.Toy

open Params (ReqShape)

/-- The multilinear map whose table is the vector in the lower half of row number which of o's main
table, which has rowBits row bits. which must be below 2^rowBits: only its low rowBits bits are
read. -/
def vectorOfRow (o rowBits which : Nat) : MapAt := fun row point coeff =>
  row.add o .main (((Tensor.eq point coeff).push oneE zeroE).insertChoice 0 rowBits which)

/-- The sub-proof of one link: ZERO and PSC for x b = c, and the three rows that PSC leaves, on the
link's group. own: the oracle messages of the link's present moment. own[0] holds b and gives the
mask entries, and own[1] holds c. In the first link x and b are the rows 0 and 1 of own[0]. In a
later link b is row 0 of own[0], and x is the product of the link before, in the message that the
frame has kept (f.keptBefore). -/
def linkVerify (f : ReqFrame) (own : Array Nat) : Blk Unit := do
  let S ← Blk.statement
  let first ← Blk.get own[0]?
  let c ← Blk.get own[1]?
  let x ← if f.link == 0 then pure first else Blk.get f.keptBefore[0]?
  let bRow := if f.link == 0 then 1 else 0
  let zeta ← hearDraw "ZERO" ((S.codes.base.getD f.shape.code default).logEll - 1)
  let summand : Psc.Summand :=
    { shown := 2, kept := 1, degree := 2,
      coeffs := fun _ y => [mulE (y.getD 0 zeroE) (y.getD 1 zeroE), negE oneE] }
  let claim : Psc.Claim :=
    { vars := zeta.map fun z => Psc.Weight.equality z 3, masks := [], target := zeroE }
  let fresh ← takeSlots first (Psc.masksOf claim summand)
  let out ← Psc.verify claim summand fresh
  Blk.addRow f.group (← Blk.get (Psc.rowU out [vectorOfRow c (S.rowBits c .main) 0]))
  let ex ← Blk.get out.ends[0]?
  let eb ← Blk.get out.ends[1]?
  Blk.addRow f.group (pointRow ex (vectorOfRow x (S.rowBits x .main) 0))
  Blk.addRow f.group (pointRow eb (vectorOfRow first (S.rowBits first .main) bRow))

/-- The verifier of the chain of links. -/
def linksVerify (shape : ReqShape) : Blk Unit := do
  let _ ← reqVerify shape (fun f _ own (_ : Unit) => linkVerify f own) ()
  Blk.requireAllTested

/-- What the parameter bytes of a run hold. -/
structure LinksPublic where
  given : Params.Given
  codes : Codes
  shape : ReqShape

/-- Reads the parameter bytes of a run. Returns nothing if `Params.Given.read` refuses the bytes, if
the plan names another field than the one in which OnBytes computes (p = 2^64 - 2^32 + 1), if the
further items are not exactly the two, under their names and in this order, or if an item's value
is not encoded as the format page says. -/
def LinksPublic.read (params : ByteArray) : Option LinksPublic := do
  let g ← Params.Given.read params
  if g.plan.field != .two then none
  if g.itemNames != ["codes", "the chain of links"] then none
  let codes ← Params.readCodes (← g.item "codes")
  let shape ← Params.readReq (← g.item "the chain of links")
  pure ⟨g, codes, shape⟩

/-- The run's verifier. -/
def LinksPublic.block (p : LinksPublic) : Blk Unit := linksVerify p.shape

/-- What the run's verifier starts from. -/
def LinksPublic.start (p : LinksPublic) : Start :=
  { entries := p.given.rounds, samples := p.given.plan.samples, st := { codes := p.codes } }

/-- The run's chain: its description, from the dry run of the verifier, and its decision. The label
is 2, the statement is empty, and the chain's random bytes are at the start of the file. -/
def linksChain (p : LinksPublic) : Option (Chain Unit) := do
  let rounds ← p.block.rounds p.start
  let spec ← Params.describeWith p.given 2 ByteArray.empty .inFile rounds
  pure { spec := spec, dec := fun _ v => p.block.decides p.start v }

/-- The verdict on a proof file of the chain of links under given parameter bytes. -/
def links (params file : ByteArray) : Verdict :=
  match (LinksPublic.read params).bind linksChain with
  | none => .refused ⟨.configuration, "parameters"⟩
  | some c =>
    match readChain c.spec [] file 0 with
    | none => .refused ⟨.proof, "reader"⟩
    | some (o, j) =>
      if j != file.size then .refused ⟨.proof, "reader"⟩
      else if c.dec () (viewOf c.spec o) then .accepted
      else .refused ⟨.proof, "decision"⟩

end OnBytes.Toy

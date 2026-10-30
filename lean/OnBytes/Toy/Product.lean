-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Toy/Product.lean: the product test, a small test protocol of the C++ library
(blocks/toy/product.h).

It is the smallest whole run of the protocol's machinery: one chain, one committed oracle message,
one sumcheck, one proximity test. There is no model, no key and no table in it. The prover knows
three vectors a, b, c over the base field with a_i b_i = c_i for all i. It commits to them and
proves the relation on what it has committed to. The chain's statement is empty.

The blocks, in the order of the run: SEND (the oracle message a, b, c with its mask row, and with
it the fresh mask of the first fold), ZERO (the verifier draws a point zeta, and the relation
becomes the one claim sum_i eq(zeta, i) (a_i b_i - c_i) = 0), PSC (the sumcheck of that claim), then
the proximity test (OnBytes/Iop/Prox.lean): BAT, then FOLD and CS for each stage except the last,
then BASE. The stages are read from the parameter bytes; the test refuses fewer than two.

The parameter bytes are an input. They hold the plan and the items "codes", "the oracle message
a, b, c", "the stages of the proximity test" and "the choices of the proximity test".

Main definitions: Toy.productVerify, Toy.ProductPublic, Toy.productChain, Toy.product.

What is not claimed: that the plan in the parameter bytes reaches a security level; anything on what
a proof file hides; that the shapes in the parameter bytes are those of the product test. This file
does not test that the oracle message has the three main rows a, b, c, and a row's number is read
modulo the table's 2^rowBits rows (rowOfTable). The C++ verifier (toy_verify_file) makes plan, codes
and shapes from the run's public file; here OnBytes/Shell/Toys.lean does that and then calls
Toy.product. No theorem is stated here.
-/
import OnBytes.Result
import OnBytes.Chain.Reader
import OnBytes.Params.Chains
import OnBytes.Iop.Prox
import OnBytes.Iop.Psc

namespace OnBytes.Toy

open Params (IoppStage IoppChoice)

/-- The verifier of the product test, block by block. notice: the oracle message a, b, c. -/
def productVerify (notice : OracleNotice) (stages : List IoppStage) (choice : IoppChoice) :
    Blk Unit := do
  let sent : Array OracleNotice :=
    match stages with
    | s :: _ => #[notice, foldMaskNotice (ioppFoldShape s {})]
    | [] => #[notice]
  let ids ← sendVerify sent
  let o ← Blk.get ids[0]?
  let S ← Blk.statement
  let zeta ← hearDraw "ZERO" (S.codes.base.getD notice.shape.code default).logEll
  -- the summand Y_1 Y_2 - U_1: a and b are shown under masks, c stays a term of the row
  let summand : Psc.Summand :=
    { shown := 2, kept := 1, degree := 2,
      coeffs := fun _ y => [mulE (y.getD 0 zeroE) (y.getD 1 zeroE), negE oneE] }
  let claim : Psc.Claim :=
    { vars := zeta.map fun z => Psc.Weight.equality z 3, masks := [], target := zeroE }
  let fresh ← takeSlots o (Psc.masksOf claim summand)
  let out ← Psc.verify claim summand fresh
  let g ← Blk.newGroup 0
  Blk.join g o
  let rowBits := S.rowBits o .main
  Blk.addRow g (← Blk.get (Psc.rowU out [rowOfTable o .main rowBits 2]))
  for (e, j) in out.ends.zipIdx do
    Blk.addRow g (pointRow e (rowOfTable o .main rowBits j))
  ioppVerify g stages choice ids[1]?
  Blk.requireAllTested

/-- What the parameter bytes of a run hold. -/
structure ProductPublic where
  given : Params.Given
  codes : Codes
  notice : OracleNotice
  stages : List IoppStage
  choice : IoppChoice

/-- Reads the parameter bytes of a run. Returns nothing if `Params.Given.read` refuses the bytes, if
the plan names another field than the one in which OnBytes computes (p = 2^64 - 2^32 + 1), if the
further items are not exactly the four, under their names and in this order, or if an item's value
is not encoded as the format page says. -/
def ProductPublic.read (params : ByteArray) : Option ProductPublic := do
  let g ← Params.Given.read params
  if g.plan.field != .two then none
  if g.itemNames != ["codes", "the oracle message a, b, c", "the stages of the proximity test",
      "the choices of the proximity test"] then none
  let codes ← Params.readCodes (← g.item "codes")
  let notice ← Params.readNotice (← g.item "the oracle message a, b, c")
  let stages ← Params.readStages (← g.item "the stages of the proximity test")
  let ride ← Params.readFlag (← g.item "the choices of the proximity test")
  pure ⟨g, codes, notice, stages, ⟨ride⟩⟩

/-- The run's verifier. -/
def ProductPublic.block (p : ProductPublic) : Blk Unit :=
  productVerify p.notice p.stages p.choice

/-- What the run's verifier starts from. -/
def ProductPublic.start (p : ProductPublic) : Start :=
  { entries := p.given.rounds, samples := p.given.plan.samples, st := { codes := p.codes } }

/-- The run's chain: its description, from the dry run of the verifier, and its decision. The label
is 1, the statement is empty, and the chain's random bytes are at the start of the file. -/
def productChain (p : ProductPublic) : Option (Chain Unit) := do
  let rounds ← p.block.rounds p.start
  let spec ← Params.describeWith p.given 1 ByteArray.empty .inFile rounds
  pure { spec := spec, dec := fun _ v => p.block.decides p.start v }

/-- The names of the checks at which a verdict on a file of a test protocol can refuse. -/
def names : List String := ["parameters", "reader", "decision"]

/-- The verdict on a proof file of the product test under given parameter bytes. -/
def product (params file : ByteArray) : Verdict :=
  match (ProductPublic.read params).bind productChain with
  | none => .refused ⟨.configuration, "parameters"⟩
  | some c =>
    match readChain c.spec [] file 0 with
    | none => .refused ⟨.proof, "reader"⟩
    | some (o, j) =>
      if j != file.size then .refused ⟨.proof, "reader"⟩
      else if c.dec () (viewOf c.spec o) then .accepted
      else .refused ⟨.proof, "decision"⟩

end OnBytes.Toy

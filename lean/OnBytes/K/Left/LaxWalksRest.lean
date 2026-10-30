-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxWalksRest.lean: the field "walks" of `LaxRest` (OnBytes/K/Left/LaxAt.lean), in
that record's own letters, from the reader's equation at a ground; and `LaxRest` whole from the
decision's field alone.

Main names:
  `walks_rest`: `LaxRest.walks`: `walks_of_parts` (OnBytes/K/Left/LaxWalks.lean) at
    `walkParts_ground` (OnBytes/K/Left/LaxWalksGround.lean).
  `rest_of_accept`: `LaxRest`, its fields rows, cols, listed by OnBytes/K/Left/LaxRestAt.lean, walks
    by `walks_rest`, accept a premise. It shows that the four fit the record to the letter.

Limits: the reader's equation e, that the statement's items hold the two roots (`hit`), `hok`, `hw`
and the field accept are premises. General in the ground: no ground is named. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxWalksGround
import OnBytes.K.Left.LaxRestAt

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.EntryFill
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf wX bodyS RowsT RowsL)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround linkAtCfg AskedE withinX)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

variable (G : EntryGround) (c : ByteArray) (hc : c.size = 32)
  (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
  (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true) (a : AskedE)
  (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ)
  (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle)
    (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement a.first a.further)) seen b
      i = some (a.out, j))
  (hit : ∀ t ∈ (entryXD G c).stored.flatten,
    _root_.Fmt.itemRoot (Params.Link.statement a.first a.further) t.item =
      some (if t.item == 1 then a.further.root else a.first.root))

include hw e hit in
/-- `LaxRest.walks`. -/
theorem walks_rest : ∃ (vert : ByteArray → ByteArray → ByteArray)
      (e1 : Enc1 (Body (Ls (entryXD G c) (d1Run G.q.link.table.cubeBits G.q.link.table.answers))))
      (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop),
    NodeLaw (famAt G c hc) vert ∧
    (∀ q z, (ownES (entryXD G c) hok).emb (.inr q) z =
      embLS (entryXD G c).C (liftT e1) (entryXD G c).ds q z) ∧
    FormsOn Fm 0 (entryXD G c).ds ∧
    (∀ run, a.out.run = some run → ∀ op ∈ ownOps a.out,
      OwnOkE (famAt G c hc) vert e1 run Fm Rt op) ∧
    (∀ op ∈ stoOps a.out,
      StoOkE (famAt G c hc) vert (bodyS (entryXD G c).a (entryXD G c).base.plan.salt).embE
        (entryXD G c).a (entryXD G c).base.cfg
        [bytesToDig a.first.root, bytesToDig a.further.root] (entryXD G c) op) ∧
    RtsL Rt (entryXD G c).C 0 (entryXD G c).ds
      (PQ.rtSL (entryXD G c).C (entryXD G c).ds a.out.rounds.toList) :=
  walks_of_parts (entryXD G c) hok (d1Run _ _) (famAt G c hc)
    (walkParts_ground G c (d1Run _ _) hc G.q.link.table hok hw e a.first.root a.further.root hit)

include hw e hit in
/-- `LaxRest`, from the decision's field alone. -/
theorem rest_of_accept (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up)
    (accept : ∀ ρ : Rho (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)),
      PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn) →
      PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true →
      (PSXE (entryXD G c) (decAt G c)).up.loc.accept (xOfAskedC _ _ a)
        ((wqXE (entryXD G c) (decAt G c)).ext.build fun p => (π.ext p).map Opening.sym)
        (mkTr (PSXE (entryXD G c) (decAt G c)).up.loc.shape
          (PSXE (entryXD G c) (decAt G c)).up.ann (wqXE (entryXD G c) (decAt G c)).sh
          (rtsAt G c a.out) π.plains ρ π.opens) = true) :
    LaxRest G c hc hok a π where
  rows := fun ρ hd => rows_rest G c hok a seen b i j e π ρ hd
  cols := cols_rest G c hok a seen b i j e
  listed := fun ρ hd => listed_rest G c hok a seen b i j e hw ρ hd
  walks := walks_rest G c hc hok hw a seen b i j e hit
  accept := accept

end OnBytes.K.Left

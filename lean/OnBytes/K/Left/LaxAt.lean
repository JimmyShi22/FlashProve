-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxAt.lean: the lax verifier's yes on an entry file's typed string at a ground
(`OnBytes.Tie.EntryGround`) and a digest of the public files, under the family that a run evaluates,
from the typing's yes, the chain, two conditions on the description, and five fields that are still
owed.

Main names:
  `decAt G c`, `famAt G c hc`, `rtsAt G c o`: the decision of a run, the family that a run
    evaluates, the chain's record of roots.
  `LaxRest G c hc hok a π`: the five fields: `rows`, `cols` (own trees), `listed` (stored tables),
    `walks`, `accept`; where a field speaks of verifier messages, it does so for every list that
    draws what the reader drew (and, for `accept`, passes all tests of work).
  `lax_at`: the join, by `lax_of_debts` (OnBytes/K/Left/Lax.lean) at what the chain yields
    (`ChainYes`, OnBytes/K/Left/LaxChain.lean).

Not claimed. That `LaxRest` is met: its fields are paid in the other files of this folder. An
implication between yeses, at one fixed oracle, the one made from the format's hash: nothing on
soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Lax
import OnBytes.K.Left.LaxChain
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.EntryFill
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf wX bodyS RowsT RowsL)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround linkAtCfg AskedE)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

variable (G : EntryGround) (c : ByteArray) (hc : c.size = 32)
  (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The decision of a run at a ground and a digest. -/
abbrev decAt : XE (List T3) G.q.link.table.cubeBits G.q.link.table.answers → View → Bool :=
  decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers

/-- The family that a run evaluates at a ground and a digest. -/
abbrev famAt : Fam (typedOracleFamily 256 ((entryXD G c).K + 1)
    (Ls (entryXD G c) (d1Run G.q.link.table.cubeBits G.q.link.table.answers))) :=
  EntryRunTop.famOf (entryXD G c) hc (d1Run _ _) G.q.link.table

/-- What the chain's record of roots is, at what was read. -/
abbrev rtsAt (o : _root_.Fmt.ChainOut) :
    RootsOfChain 256 (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)) :=
  ((none, some []), PQ.rtSL (entryXD G c).C (entryXD G c).ds o.rounds.toList)

/-- What is still owed at a ground, beside the typing, the chain and the description: five
fields, each for every list ρ of verifier messages that draws what the reader drew (and, for the
decision, passes all tests of work). a: what the strict converter hands over; π: the typed string.
-/
structure LaxRest (a : AskedE) (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up) : Prop where
  /-- Own: "read" means "listed in the file's opening" -/
  rows : ∀ ρ : Rho (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)),
    PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn) →
    ∃ sb, RowsL (entryXD G c).C (tblOf (ownOps a.out)) sb (entryXD G c).ds a.out.rounds.toList
      fun q => (haveI := (wqXE (entryXD G c) (decAt G c)).decO
        decide (Sum.inr q ∈ (PSXE (entryXD G c) (decAt G c)).up.loc.reads (xOfAskedC _ _ a) ρ
          (effPlains (PSXE (entryXD G c) (decAt G c)).up.loc.shape
            (PSXE (entryXD G c) (decAt G c)).up.ann (rtsAt G c a.out) π.plains)))
  /-- Own: the columns have their forms' widths -/
  cols : ColsFit (ownOps a.out)
  /-- Ext: a position read in a stored table is listed in a stored opening of that table -/
  listed : ∀ ρ : Rho (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)),
    PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn) →
    ListedX (entryXD G c) (entryXD G c).a (stoOps a.out) fun p =>
      (haveI := (wqXE (entryXD G c) (decAt G c)).ext.dec
       decide (p ∈ (PSXE (entryXD G c) (decAt G c)).up.loc.extReads (xOfAskedC _ _ a) ρ))
  /-- Walks -/
  walks : ∃ (vert : ByteArray → ByteArray → ByteArray)
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
      (PQ.rtSL (entryXD G c).C (entryXD G c).ds a.out.rounds.toList)
  /-- The decision -/
  accept : ∀ ρ : Rho (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)),
    PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn) →
    PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true →
    (PSXE (entryXD G c) (decAt G c)).up.loc.accept (xOfAskedC _ _ a)
      ((wqXE (entryXD G c) (decAt G c)).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE (entryXD G c) (decAt G c)).up.loc.shape (PSXE (entryXD G c) (decAt G c)).up.ann
        (wqXE (entryXD G c) (decAt G c)).sh (rtsAt G c a.out) π.plains ρ π.opens) = true

/-- The lax verifier's yes at a ground, from the typing's yes, the chain, two conditions on the
description, and the five fields. -/
theorem lax_at (a : AskedE) (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up)
    (hπ : assembleS (entryXD G c) (decAt G c) a.out = some π)
    (hch : ChainYes G c hc (d1Run _ _) G.q.link.table (decAt G c) a.first a.further a.out π
      (xOfAskedC _ _ a).2)
    (hd : (∀ d ∈ (entryXD G c).ds, d.entry.work ≤ 64) ∧
      PQ.okX (entryXD G c).ds (entryXD G c).a (entryXD G c).xs = true)
    (R : LaxRest G c hc hok a π) :
    laxE (entryXD G c) (decAt G c) (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
      (ownES (entryXD G c) hok) (earlyTwo (A := List T3 × List T3) (d1Run _ _))
      (fun _ => TSE (entryXD G c) (seedEntry _ _)) (famAt G c hc)
      [bytesToDig a.first.root, bytesToDig a.further.root] (xOfAskedC _ _ a) π = true := by
  obtain ⟨ρ, v, h1, h2, h3⟩ := hch
  exact lax_of_debts (entryXD G c) hok (d1Run _ _) (famAt G c hc) (decAt G c) _ _ _ a.out π ρ v
    ⟨hπ, h1, hd.1, hd.2, R.rows ρ h2, R.cols, R.listed ρ h2, R.walks, R.accept ρ h2 h3⟩

end OnBytes.K.Left
